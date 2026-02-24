use std::{collections::VecDeque, fmt};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        Body, Location, Place, TerminatorKind,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{self, GenericArgsRef, Ty, TyCtxt},
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::ty_visit::UnionRelatedTypes;

// CallGraph: caller -> callee list
pub type CallGraph = FxHashMap<DefId, Vec<DefId>>;

#[derive(Debug, Clone)]
pub struct SCCNode {
    pub id: usize,
    pub members: Vec<DefId>,
}

#[derive(Clone, Default)]
pub struct CondensationGraph {
    pub nodes: Vec<SCCNode>,
    pub edges: FxHashMap<usize, FxHashSet<usize>>,
}

impl fmt::Debug for CondensationGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CondensationGraph {{")?;
        writeln!(f, "\tnodes:")?;
        for node in &self.nodes {
            writeln!(f, "\t\tSCC #{}:", node.id)?;
            writeln!(f, "\t\t\tmembers: {:?}", node.members)?;
        }

        writeln!(f, "\tedges:")?;
        for node in &self.nodes {
            let scc_id = node.id;
            let dsts = self
                .edges
                .get(&scc_id)
                .map(|set| set.iter().copied().collect::<Vec<_>>())
                .unwrap_or_default();
            writeln!(f, "\t\t{scc_id} -> {dsts:?}")?;
        }
        write!(f, "}}")
    }
}

struct BodyUnionUseCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    union_tys: &'a FxHashSet<LocalDefId>,
    found_unions: FxHashSet<LocalDefId>,
}

#[derive(Clone, Copy)]
struct DirectCallee<'tcx> {
    def_id: DefId,
    args: Option<GenericArgsRef<'tcx>>,
}

impl<'tcx, 'a> BodyUnionUseCollector<'tcx, 'a> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, union_tys: &'a FxHashSet<LocalDefId>) -> Self {
        Self {
            tcx,
            body,
            union_tys,
            found_unions: FxHashSet::default(),
        }
    }
}

impl<'tcx> MirVisitor<'tcx> for BodyUnionUseCollector<'tcx, '_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let ty = place.ty(self.body, self.tcx).ty;
        collect_union_ids_from_ty(ty, self.union_tys, &mut self.found_unions);
        self.super_place(place, context, location);
    }
}

fn collect_union_ids_from_ty<'tcx>(
    mut ty: Ty<'tcx>,
    union_tys: &FxHashSet<LocalDefId>,
    out: &mut FxHashSet<LocalDefId>,
) {
    loop {
        match ty.kind() {
            ty::Adt(adt_def, _) if adt_def.is_union() => {
                if let Some(local_id) = adt_def.did().as_local()
                    && union_tys.contains(&local_id)
                {
                    out.insert(local_id);
                }
                break;
            }
            ty::Ref(_, inner, _) => ty = *inner,
            ty::RawPtr(t, _) => ty = *t,
            _ => break,
        }
    }
}

/// Collect seed functions for each union type
/// functions that directly use the union type in their signature (arguments or return type).
pub fn collect_union_seed_functions<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_tys: &[LocalDefId],
    verbose: bool,
) -> FxHashMap<LocalDefId, Vec<LocalDefId>> {
    let union_tys: FxHashSet<_> = union_tys.iter().copied().collect();
    let mut map: FxHashMap<LocalDefId, FxHashSet<LocalDefId>> = union_tys
        .iter()
        .copied()
        .map(|union_ty| (union_ty, FxHashSet::default()))
        .collect();

    for def_id in tcx.hir_body_owners() {
        if !is_seed_candidate(tcx, def_id) {
            continue;
        }

        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();
        let mut found_unions = FxHashSet::default();

        for arg in body.args_iter() {
            let ty = body.local_decls[arg].ty;
            collect_union_ids_from_ty(ty, &union_tys, &mut found_unions);
        }

        let mut collector = BodyUnionUseCollector::new(tcx, body, &union_tys);
        collector.visit_body(body);
        found_unions.extend(collector.found_unions);

        for union_ty in found_unions {
            map.entry(union_ty).or_default().insert(def_id);
        }
    }

    let map: FxHashMap<LocalDefId, Vec<LocalDefId>> = map
        .into_iter()
        .map(|(union_ty, mut fn_ids)| {
            let mut fn_ids = fn_ids.drain().collect::<Vec<_>>();
            fn_ids.sort_by_key(|def_id| tcx.def_path_str(*def_id));
            (union_ty, fn_ids)
        })
        .collect();

    if verbose {
        println!("\nCallgraph Seed Functions:\n\t{}", {
            let mut lines = map
                .iter()
                .map(|(ty, funcs)| {
                    let ty_name = tcx.def_path_str(*ty);
                    let func_names = funcs
                        .iter()
                        .map(|def_id| tcx.def_path_str(*def_id))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{ty_name}\n\t\t-> {func_names}")
                })
                .collect::<Vec<_>>();
            lines.sort();
            lines.join("\n\t")
        });
    }

    map
}

/// Build a callgraph for each target union type
pub fn build_union_callgraphs<'tcx>(
    tcx: TyCtxt<'tcx>,
    seed_functions: &FxHashMap<LocalDefId, Vec<LocalDefId>>,
    related_types_map: &FxHashMap<LocalDefId, UnionRelatedTypes<'tcx>>,
    verbose: bool,
) -> FxHashMap<LocalDefId, CallGraph> {
    // Debug step option
    let verbose_callgraph_steps = true;

    let mut callee_cache: FxHashMap<DefId, Vec<DirectCallee<'tcx>>> = FxHashMap::default();
    let mut union_callgraphs = FxHashMap::default();

    for (&union_ty, seeds) in seed_functions {
        let related_types = related_types_map
            .get(&union_ty)
            .cloned()
            .unwrap_or_else(|| UnionRelatedTypes {
                parent_types: FxHashSet::default(),
                field_types: FxHashSet::default(),
            });

        // To handle array [T; N]
        // In this case, we should also handle pointers or references to T or [T]
        // ex. &[T], *const T, *mut T, ...
        let field_pointer_types = collect_field_pointer_types(&related_types.field_types);

        // Seed funcs
        let seed_set = seeds
            .iter()
            .map(|id| id.to_def_id())
            .collect::<FxHashSet<_>>();

        let mut visited = FxHashSet::default();
        let mut worklist =
            VecDeque::from(seeds.iter().map(|id| id.to_def_id()).collect::<Vec<_>>());

        let mut graph: FxHashMap<DefId, FxHashSet<DefId>> = FxHashMap::default();

        if verbose && verbose_callgraph_steps {
            let mut parent_names = related_types
                .parent_types
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            parent_names.sort();

            let mut seed_names = seeds
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            seed_names.sort();

            let mut field_names = related_types
                .field_types
                .iter()
                .map(|ty| format!("{ty:?}"))
                .collect::<Vec<_>>();
            field_names.sort();

            let mut ptr_names = field_pointer_types
                .iter()
                .map(|ty| format!("{ty:?}"))
                .collect::<Vec<_>>();
            ptr_names.sort();

            println!(
                "\n[Callgraph][{}]\n\tParent Types:\n\t\t{}\n\tSeeds:\n\t\t{}",
                tcx.def_path_str(union_ty),
                parent_names.join("\n\t\t"),
                seed_names.join("\n\t\t")
            );
            println!(
                "\tField Types:\n\t\t{}\n\tField Pointer Types:\n\t\t{}",
                field_names.join("\n\t\t"),
                ptr_names.join("\n\t\t")
            );
        }

        while let Some(caller) = worklist.pop_front() {
            if !visited.insert(caller) {
                continue;
            }

            // Check the caller
            let caller_hits = signature_related_hits(
                tcx,
                union_ty,
                caller,
                None,
                &related_types,
                &field_pointer_types,
            );
            let is_seed = seed_set.contains(&caller);
            if !is_seed && caller_hits.is_empty() {
                if verbose && verbose_callgraph_steps {
                    println!(
                        "\t[Drop Caller] {} (no related type in signature)",
                        tcx.def_path_str(caller)
                    );
                }
                continue;
            }
            if verbose && verbose_callgraph_steps {
                if is_seed && caller_hits.is_empty() {
                    println!("\t[Keep Caller:Seed] {}", tcx.def_path_str(caller));
                } else {
                    println!(
                        "\t[Keep Caller] {} | hits: {}",
                        tcx.def_path_str(caller),
                        caller_hits.join(", ")
                    );
                }
            }

            let callees = collect_direct_callees(tcx, caller, &mut callee_cache);
            if verbose && verbose_callgraph_steps {
                println!(
                    "\t\tDirect callees from {}: {}",
                    tcx.def_path_str(caller),
                    callees
                        .iter()
                        .map(|callee| tcx.def_path_str(callee.def_id))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }

            graph.entry(caller).or_default();
            for callee in &callees {
                // Check callees
                let callee_hits = signature_related_hits(
                    tcx,
                    union_ty,
                    callee.def_id,
                    callee.args,
                    &related_types,
                    &field_pointer_types,
                );
                if callee_hits.is_empty() {
                    if verbose && verbose_callgraph_steps {
                        println!(
                            "\t\t[Drop Callee] {} (no related type in signature)",
                            tcx.def_path_str(callee.def_id)
                        );
                    }
                    continue;
                }
                graph.entry(caller).or_default().insert(callee.def_id);
                if verbose && verbose_callgraph_steps {
                    println!(
                        "\t\t[Keep Callee] {} | hits: {}",
                        tcx.def_path_str(callee.def_id),
                        callee_hits.join(", ")
                    );
                }
                if !visited.contains(&callee.def_id)
                    && is_expandable_graph_node(
                        tcx,
                        union_ty,
                        callee.def_id,
                        &related_types,
                        &field_pointer_types,
                    )
                {
                    // Add to worklist if not visited and expandable
                    worklist.push_back(callee.def_id);
                    if verbose && verbose_callgraph_steps {
                        println!("\t\t\t[Expand] {}", tcx.def_path_str(callee.def_id));
                    }
                } else if verbose && verbose_callgraph_steps {
                    println!("\t\t\t[No Expand] {}", tcx.def_path_str(callee.def_id));
                }
            }
        }

        let graph = graph
            .into_iter()
            .map(|(caller, mut callees)| {
                let mut callees = callees.drain().collect::<Vec<_>>();
                callees.sort_by_key(|def_id| tcx.def_path_str(*def_id));
                (caller, callees)
            })
            .collect::<FxHashMap<_, _>>();
        union_callgraphs.insert(union_ty, graph);
    }

    if verbose {
        println!("\nUnion Callgraphs:");
        let mut union_tys = union_callgraphs.keys().copied().collect::<Vec<_>>();
        union_tys.sort_by_key(|def_id| tcx.def_path_str(*def_id));
        for union_ty in union_tys {
            println!("\t{}:", tcx.def_path_str(union_ty));
            if let Some(graph) = union_callgraphs.get(&union_ty) {
                let mut callers = graph.keys().copied().collect::<Vec<_>>();
                callers.sort_by_key(|def_id| tcx.def_path_str(*def_id));
                for caller in callers {
                    let caller_name = tcx.def_path_str(caller);
                    let callees = graph
                        .get(&caller)
                        .expect("caller key was collected from the same map")
                        .iter()
                        .map(|def_id| tcx.def_path_str(*def_id))
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!("\t\t{caller_name} -> {callees}");
                }
            }
        }
    }

    union_callgraphs
}

pub fn callgraph_to_condensation_graph(callgraph: &CallGraph) -> CondensationGraph {
    struct Tarjan<'a> {
        graph: &'a CallGraph,
        index: usize,
        stack: Vec<DefId>,
        on_stack: FxHashSet<DefId>,
        index_of: FxHashMap<DefId, usize>,
        lowlink: FxHashMap<DefId, usize>,
        sccs: Vec<Vec<DefId>>,
    }

    impl<'a> Tarjan<'a> {
        fn strongconnect(&mut self, v: DefId) {
            let v_index = self.index;
            self.index += 1;
            self.index_of.insert(v, v_index);
            self.lowlink.insert(v, v_index);
            self.stack.push(v);
            self.on_stack.insert(v);

            if let Some(succs) = self.graph.get(&v) {
                for &w in succs {
                    if !self.index_of.contains_key(&w) {
                        self.strongconnect(w);
                        let w_low = *self.lowlink.get(&w).expect("w lowlink exists");
                        let v_low = self.lowlink.get_mut(&v).expect("v lowlink exists");
                        if w_low < *v_low {
                            *v_low = w_low;
                        }
                    } else if self.on_stack.contains(&w) {
                        let w_idx = *self.index_of.get(&w).expect("w index exists");
                        let v_low = self.lowlink.get_mut(&v).expect("v lowlink exists");
                        if w_idx < *v_low {
                            *v_low = w_idx;
                        }
                    }
                }
            }

            let v_low = *self.lowlink.get(&v).expect("v lowlink exists");
            if v_low == v_index {
                let mut scc = Vec::new();
                loop {
                    let w = self.stack.pop().expect("stack not empty");
                    self.on_stack.remove(&w);
                    scc.push(w);
                    if w == v {
                        break;
                    }
                }
                self.sccs.push(scc);
            }
        }
    }

    let mut all_nodes = FxHashSet::default();
    for (&caller, callees) in callgraph {
        all_nodes.insert(caller);
        for &callee in callees {
            all_nodes.insert(callee);
        }
    }

    let mut tarjan = Tarjan {
        graph: callgraph,
        index: 0,
        stack: Vec::new(),
        on_stack: FxHashSet::default(),
        index_of: FxHashMap::default(),
        lowlink: FxHashMap::default(),
        sccs: Vec::new(),
    };

    for &node in &all_nodes {
        if !tarjan.index_of.contains_key(&node) {
            tarjan.strongconnect(node);
        }
    }

    // Tarjan emits SCCs in reverse topological order of the condensation DAG.
    let mut nodes = Vec::with_capacity(tarjan.sccs.len());
    let mut scc_of = FxHashMap::default();
    for (scc_id, members) in tarjan.sccs.into_iter().enumerate() {
        for &member in &members {
            scc_of.insert(member, scc_id);
        }
        nodes.push(SCCNode {
            id: scc_id,
            members,
        });
    }

    let mut edges: FxHashMap<usize, FxHashSet<usize>> = FxHashMap::default();
    for node in &nodes {
        edges.entry(node.id).or_default();
    }
    for (&caller, callees) in callgraph {
        let src = *scc_of
            .get(&caller)
            .expect("caller in graph should map to an SCC");
        for &callee in callees {
            let dst = *scc_of
                .get(&callee)
                .expect("callee in graph should map to an SCC");
            if src != dst {
                edges.entry(src).or_default().insert(dst);
            }
        }
    }

    CondensationGraph { nodes, edges }
}

pub fn callgraphs_to_condensation_graphs(
    callgraphs: &FxHashMap<LocalDefId, CallGraph>,
) -> FxHashMap<LocalDefId, CondensationGraph> {
    callgraphs
        .iter()
        .map(|(&union_ty, graph)| (union_ty, callgraph_to_condensation_graph(graph)))
        .collect()
}

fn collect_direct_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    cache: &mut FxHashMap<DefId, Vec<DirectCallee<'tcx>>>,
) -> Vec<DirectCallee<'tcx>> {
    if let Some(cached) = cache.get(&def_id) {
        return cached.clone();
    }

    let collected = do_collect_direct_callees(tcx, def_id);
    cache.insert(def_id, collected.clone());
    collected
}

fn do_collect_direct_callees<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<DirectCallee<'tcx>> {
    if !is_expandable_def(tcx, def_id) {
        return Vec::new();
    }

    let local_def_id = match def_id.as_local() {
        Some(local_def_id) => local_def_id,
        None => return Vec::new(),
    };

    let body = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
    let body: &Body<'_> = &body.borrow();
    let mut callees = FxHashMap::<DefId, Option<GenericArgsRef<'tcx>>>::default();

    for bbd in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bbd.terminator().kind {
            if let Some((callee, _args)) = func.const_fn_def() {
                if is_callable_def(tcx, callee) {
                    callees.insert(callee, Some(_args));
                }
                continue;
            }
            if let ty::FnDef(callee, _) = func.ty(body, tcx).kind()
                && is_callable_def(tcx, *callee)
            {
                callees.entry(*callee).or_insert(None);
            }
        }
    }

    let mut callees = callees
        .into_iter()
        .map(|(def_id, args)| DirectCallee { def_id, args })
        .collect::<Vec<_>>();
    callees.sort_by_key(|callee| tcx.def_path_str(callee.def_id));
    callees
}

/// Heuristic to find user-defined seed functions that uses target union types
fn is_seed_candidate(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }

    if !tcx.is_mir_available(def_id.to_def_id()) {
        return false;
    }

    // Skip compiler/macro-generated bodies (ex. clone)
    if tcx.def_span(def_id).from_expansion() {
        return false;
    }

    let def_id = def_id.to_def_id();
    if let Some(impl_id) = tcx.impl_of_method(def_id)
        && let Some(trait_id) = tcx.trait_id_of_impl(impl_id)
    {
        let trait_path = tcx.def_path_str(trait_id);
        if trait_path.starts_with("core::") || trait_path.starts_with("std::") {
            return false;
        }
    }

    true
}

fn is_callable_def(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
}

/// Expandable and related type signature hit
fn is_expandable_graph_node<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: LocalDefId,
    def_id: DefId,
    related_types: &UnionRelatedTypes<'tcx>,
    field_pointer_types: &FxHashSet<Ty<'tcx>>,
) -> bool {
    is_expandable_def(tcx, def_id)
        && !signature_related_hits(
            tcx,
            union_ty,
            def_id,
            None,
            related_types,
            field_pointer_types,
        )
        .is_empty()
}

/// Check if a function's mir body is available
fn is_expandable_def(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local_def_id) = def_id.as_local() else {
        return false;
    };
    is_callable_def(tcx, def_id) && tcx.is_mir_available(local_def_id.to_def_id())
}

/// Check if the function signature caller contains a union related type which is one of below:
/// - the union type itself
/// - parent struct types including its pointer or reference
/// - pointer or reference of field types
/// - void pointer types
fn signature_related_hits<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: LocalDefId,
    def_id: DefId,
    args: Option<GenericArgsRef<'tcx>>,
    related_types: &UnionRelatedTypes<'tcx>,
    field_pointer_types: &FxHashSet<Ty<'tcx>>,
) -> Vec<String> {
    if !is_callable_def(tcx, def_id) {
        return Vec::new();
    }

    let poly_sig = tcx.fn_sig(def_id);
    let sig = match args {
        Some(args) => poly_sig.instantiate(tcx, args).skip_binder(),
        None => poly_sig.instantiate_identity().skip_binder(),
    };
    let mut hits = Vec::new();
    for (idx, ty) in sig.inputs().iter().enumerate() {
        if is_related_type(
            tcx,
            union_ty,
            *ty,
            related_types,
            field_pointer_types,
            false,
        ) {
            hits.push(format!("arg{idx}:{ty:?}"));
        }
    }
    let out_ty = sig.output();
    if is_related_type(
        tcx,
        union_ty,
        out_ty,
        related_types,
        field_pointer_types,
        false,
    ) {
        hits.push(format!("ret:{out_ty:?}"));
    }
    hits
}

// TODO: Logic check
fn is_related_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: LocalDefId,
    ty: Ty<'tcx>,
    related_types: &UnionRelatedTypes<'tcx>,
    field_pointer_types: &FxHashSet<Ty<'tcx>>,
    under_ptr_or_ref: bool,
) -> bool {
    if related_types.field_types.contains(&ty) {
        return under_ptr_or_ref;
    }
    if under_ptr_or_ref && field_pointer_types.contains(&ty) {
        return true;
    }

    match ty.kind() {
        ty::Adt(adt_def, substs) => {
            if let Some(local_def_id) = adt_def.did().as_local()
                && (local_def_id == union_ty || related_types.parent_types.contains(&local_def_id))
            {
                return true;
            }
            if under_ptr_or_ref && is_c_void_def(tcx, adt_def.did()) {
                return true;
            }
            substs.types().any(|t| {
                is_related_type(tcx, union_ty, t, related_types, field_pointer_types, false)
            })
        }
        ty::Ref(_, inner, _) => is_related_type(
            tcx,
            union_ty,
            *inner,
            related_types,
            field_pointer_types,
            true,
        ),
        ty::RawPtr(t, _) => {
            is_related_type(tcx, union_ty, *t, related_types, field_pointer_types, true)
        }
        ty::Tuple(tys) => tys
            .iter()
            .any(|t| is_related_type(tcx, union_ty, t, related_types, field_pointer_types, false)),
        ty::Array(t, _) | ty::Slice(t) => is_related_type(
            tcx,
            union_ty,
            *t,
            related_types,
            field_pointer_types,
            under_ptr_or_ref,
        ),
        _ => false,
    }
}

fn is_c_void_def(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let path = tcx.def_path_str(def_id);
    path == "libc::c_void" || path == "std::ffi::c_void" || path == "core::ffi::c_void"
}

fn collect_field_pointer_types<'tcx>(field_tys: &FxHashSet<Ty<'tcx>>) -> FxHashSet<Ty<'tcx>> {
    let mut pointee_tys = FxHashSet::default();
    for &field_ty in field_tys {
        collect_pointee_related_types(field_ty, &mut pointee_tys);
    }
    pointee_tys
}

fn collect_pointee_related_types<'tcx>(ty: Ty<'tcx>, out: &mut FxHashSet<Ty<'tcx>>) {
    match ty.kind() {
        ty::Array(inner, _) | ty::Slice(inner) | ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            out.insert(*inner);
            collect_pointee_related_types(*inner, out);
        }
        ty::Tuple(tys) => {
            for t in tys.iter() {
                collect_pointee_related_types(t, out);
            }
        }
        ty::Adt(_, substs) => {
            for t in substs.types() {
                collect_pointee_related_types(t, out);
            }
        }
        _ => {}
    }
}
