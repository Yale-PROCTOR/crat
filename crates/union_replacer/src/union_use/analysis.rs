// use etrace::some_or;
use points_to::{
    andersen,
    andersen::{LocEdges, LocNode},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, Body, Local, Location, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor as MirVisitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;
use utils::ty_shape;

use super::{
    callgraph::UnionCallContext,
    model::{self, ArgEffectKind},
    utils::{print_all_local_bodies_with_points_to, with_body},
};

pub fn analyze(
    tcx: TyCtxt,
    target_union_tys: &[LocalDefId],
    call_contexts: &FxHashMap<LocalDefId, UnionCallContext>,
    print_mir: bool,
    verbose: bool,
) -> UnionUseResult {
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx, false);

    let points_to_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: FxHashSet::default(),
    };

    let pre = andersen::pre_analyze(&points_to_config, &tss, tcx);

    let solutions = andersen::analyze(&points_to_config, &pre, &tss, tcx);

    let may_points_to = andersen::post_analyze(&points_to_config, pre, solutions, &tss, tcx);

    // for (def_id, writes) in &_may_points_to.writes {
    //     println!("Function {def_id:?} writes:");
    //     for write in writes {
    //         println!(
    //             "\t{write:?}"
    //         );
    //     }
    // }

    if print_mir {
        print_all_local_bodies_with_points_to(tcx, &may_points_to);
    }

    if verbose {
        println!("\nUnion use analysis result:");
    }

    identify_union_uses(tcx, target_union_tys, may_points_to, call_contexts, verbose)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnionAccessField {
    /// Access to a concrete union field index.
    Field(usize),
    /// Sound over-approximation when exact field cannot be resolved.
    Top,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UnionMemoryInstance {
    /// Root location of the union memory instance in points-to indexing.
    pub root: andersen::Loc,
    /// Inclusive end of the union memory instance (`ends[root]`).
    pub end: andersen::Loc,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UnionAccessSite {
    pub def_id: LocalDefId,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UnionRead {
    pub site: UnionAccessSite,
    pub field: UnionAccessField,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UnionWrite {
    pub site: UnionAccessSite,
    pub field: UnionAccessField,
}

pub fn format_access(tcx: TyCtxt<'_>, union_ty: DefId, access: &impl HasUnionField) -> String {
    match access.union_field() {
        UnionAccessField::Field(index) => {
            let ty = union_field_ty(tcx, union_ty, access.union_field())
                .map(|ty| format!("{ty:?}"))
                .unwrap_or_else(|| "?".to_string());
            format!("field#{index}\t({ty})")
        }
        UnionAccessField::Top => "top\t(unknown)".to_string(),
    }
}

pub fn union_field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: DefId,
    field: UnionAccessField,
) -> Option<Ty<'tcx>> {
    let UnionAccessField::Field(index) = field else {
        return None;
    };
    let adt = tcx.adt_def(union_ty);
    let field = adt.all_fields().nth(index)?;
    Some(tcx.type_of(field.did).instantiate_identity())
}

pub trait HasUnionField {
    fn union_field(&self) -> UnionAccessField;
}

impl HasUnionField for UnionRead {
    fn union_field(&self) -> UnionAccessField {
        self.field
    }
}

impl HasUnionField for UnionWrite {
    fn union_field(&self) -> UnionAccessField {
        self.field
    }
}

#[derive(Default)]
pub struct UnionInstanceUses {
    /// Read operations grouped by function for this union memory instance.
    pub reads: FxHashMap<LocalDefId, Vec<UnionRead>>,
    /// Write operations grouped by function for this union memory instance.
    pub writes: FxHashMap<LocalDefId, Vec<UnionWrite>>,
}

#[derive(Default)]
pub struct UnionInstanceMap {
    /// Memory-instance-level summary for this union type.
    pub instances: FxHashMap<UnionMemoryInstance, UnionInstanceUses>,
}

pub struct UnionUseResult {
    /// `union type def_id -> per-instance uses`.
    pub uses: FxHashMap<DefId, UnionInstanceMap>,
}

impl std::fmt::Debug for UnionInstanceUses {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "READ:")?;
        for (def_id, reads) in &self.reads {
            writeln!(f, "\t{def_id:?}:")?;
            for loc in reads.iter().map(|r| r.site.location) {
                writeln!(f, "\t\t{loc:?}")?;
            }
        }

        writeln!(f, "WRITE:")?;
        for (def_id, writes) in &self.writes {
            writeln!(f, "\t{def_id:?}:")?;
            for loc in writes.iter().map(|w| w.site.location) {
                writeln!(f, "\t\t{loc:?}")?;
            }
        }
        Ok(())
    }
}

impl std::fmt::Debug for UnionInstanceMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (instance, uses) in &self.instances {
            writeln!(
                f,
                "\tInstance L{}..=L{}:",
                instance.root.index(),
                instance.end.index()
            )?;
            let uses_str = format!("{uses:?}");
            for line in uses_str.lines() {
                writeln!(f, "\t\t{line}")?;
            }
        }
        Ok(())
    }
}

impl std::fmt::Debug for UnionUseResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (union_ty, type_uses) in &self.uses {
            writeln!(f, "UnionType {union_ty:?}:")?;
            let ty_uses_str = format!("{type_uses:?}");
            for line in ty_uses_str.lines() {
                writeln!(f, "\t{line}")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Identify union uses based on the points-to analysis result.
/// - For each union type
/// - For each union instance (memory)
fn identify_union_uses(
    tcx: TyCtxt<'_>,
    target_union_tys: &[LocalDefId],
    result: andersen::AnalysisResult,
    call_contexts: &FxHashMap<LocalDefId, UnionCallContext>,
    verbose: bool,
) -> UnionUseResult {
    let union_instances: Vec<UnionMemoryInstance> = result
        .union_offsets
        .keys()
        .copied()
        .filter_map(|root| union_instance_from_root(&result, root))
        .collect();
    let union_instance_set: FxHashSet<UnionMemoryInstance> =
        union_instances.iter().copied().collect();
    let target_union_ty_set: FxHashSet<DefId> = target_union_tys
        .iter()
        .map(|def_id| def_id.to_def_id())
        .collect();
    // if verbose {
    //     println!("Union Instances: {union_instances:?}");
    // }

    let mut target_fns: FxHashSet<LocalDefId> = FxHashSet::default();
    for ctx in call_contexts.values() {
        for &def_id in &ctx.target_fns {
            target_fns.insert(def_id);
        }
    }

    // Pass 1
    // Collect types of union instances
    // - construct `(union instance) -> union type` from local declarations
    let mut instance_to_union_ty: FxHashMap<UnionMemoryInstance, DefId> = FxHashMap::default();

    for &def_id in &target_fns {
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            unreachable!("Expected function, got {:?}", tcx.def_kind(def_id));
        }
        if !tcx.is_mir_available(def_id.to_def_id()) {
            continue;
        }

        with_body(tcx, def_id, |body| {
            for (local, decl) in body.local_decls.iter_enumerated() {
                let Some(node) = result.var_nodes.get(&(def_id, local)) else {
                    continue;
                };
                collect_union_instances_from_local(
                    tcx,
                    decl.ty,
                    *node,
                    &result,
                    &union_instance_set,
                    &target_union_ty_set,
                    &mut instance_to_union_ty,
                );
            }
        });
    }

    let union_instances: Vec<UnionMemoryInstance> = instance_to_union_ty.keys().copied().collect();

    // Pass 2
    // Collect union instance accesses and classify them
    // - collect accesses using the finalized instance-to-type map
    let mut all_accesses: Vec<DetectedAccess> = Vec::new();

    for &def_id in &target_fns {
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            unreachable!("Expected function, got {:?}", tcx.def_kind(def_id));
        }
        if !tcx.is_mir_available(def_id.to_def_id()) {
            continue;
        }

        let accesses = with_body(tcx, def_id, |body| {
            let mut collector = BodyUnionAccessCollector::new(
                tcx,
                body,
                def_id,
                &result,
                &union_instances,
                &instance_to_union_ty,
            );
            collector.visit_body(body);
            collector.accesses
        });
        all_accesses.extend(accesses);
    }

    // Pass 3
    // Merge stage
    // - Refine results to a map: type -> instance -> accesses
    let mut union_uses: FxHashMap<DefId, UnionInstanceMap> = FxHashMap::default();

    for (instance, union_ty) in &instance_to_union_ty {
        union_uses
            .entry(*union_ty)
            .or_default()
            .instances
            .entry(*instance)
            .or_default();
    }

    for access in all_accesses {
        let uses = union_uses
            .get_mut(&access.resolved_union_ty)
            .unwrap()
            .instances
            .get_mut(&access.instance)
            .unwrap();
        match access.kind {
            AccessKind::Read => uses
                .reads
                .entry(access.site.def_id)
                .or_default()
                .push(UnionRead {
                    site: access.site,
                    field: access.field,
                }),
            AccessKind::Write => {
                uses.writes
                    .entry(access.site.def_id)
                    .or_default()
                    .push(UnionWrite {
                        site: access.site,
                        field: access.field,
                    })
            }
        }
    }

    let res = UnionUseResult { uses: union_uses };
    if verbose {
        println!("{res:?}");
    }
    res
}

fn collect_union_instances_from_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    node: LocNode,
    result: &andersen::AnalysisResult,
    union_instance_set: &FxHashSet<UnionMemoryInstance>,
    target_union_ty_set: &FxHashSet<DefId>,
    out: &mut FxHashMap<UnionMemoryInstance, DefId>,
) {
    let TyKind::Adt(adt, args) = ty.kind() else {
        return;
    };

    if adt.is_union() {
        let Some(instance) = union_instance_from_root(result, node.index) else {
            return;
        };
        if union_instance_set.contains(&instance) && target_union_ty_set.contains(&adt.did()) {
            out.entry(instance).or_insert(adt.did());
        }
        // Ignore nested unions inside union fields for now.
        return;
    }

    if !adt.is_struct() {
        return;
    }

    let Some(LocEdges::Fields(succs)) = result.graph.get(&node) else {
        return;
    };

    for (field_idx, succ) in succs.iter().enumerate() {
        let Some(field) = adt.all_fields().nth(field_idx) else {
            continue;
        };
        let field_ty = field.ty(tcx, args);
        collect_union_instances_from_local(
            tcx,
            field_ty,
            *succ,
            result,
            union_instance_set,
            target_union_ty_set,
            out,
        );
    }
}

fn union_instance_from_root(
    result: &andersen::AnalysisResult,
    root: andersen::Loc,
) -> Option<UnionMemoryInstance> {
    // `union_offsets[root]` is [field_offset..., union_len].
    // Use union_len (not `result.ends[root]`) to avoid including non-union tail bytes
    // when a union shares the same root index with an enclosing struct at offset 0.
    let offsets = result.union_offsets.get(&root)?;
    let union_len = *offsets.last()?;
    if union_len == 0 {
        return None;
    }
    Some(UnionMemoryInstance {
        root,
        end: root + (union_len - 1),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum AccessKind {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DetectedAccess {
    kind: AccessKind,
    site: UnionAccessSite,
    field: UnionAccessField,
    instance: UnionMemoryInstance,
    resolved_union_ty: DefId,
}

/// Collect union accesses and classify them
struct BodyUnionAccessCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    def_id: LocalDefId,
    result: &'a andersen::AnalysisResult,
    union_instances: &'a [UnionMemoryInstance],
    instance_to_union_ty: &'a FxHashMap<UnionMemoryInstance, DefId>,
    seen: FxHashSet<DetectedAccess>,
    accesses: Vec<DetectedAccess>,
    init_lhs: FxHashMap<Location, Local>,
    skip_store_locations: FxHashSet<Location>,
    union_local_known_field: FxHashMap<Local, (DefId, UnionAccessField)>,
}

impl<'tcx> MirVisitor<'tcx> for BodyUnionAccessCollector<'tcx, '_> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        let mut local_field_update: Option<(Local, Option<(DefId, UnionAccessField)>)> = None;

        // Handle union init statement
        // i.e. let x = UnionType { field: ... };
        if let StatementKind::Assign(box (place, rvalue)) = &statement.kind
            && let Some((union_ty, field)) = self.is_union_init(*place, rvalue)
        {
            self.init_lhs.insert(location, place.local);
            self.skip_store_locations.insert(location);
            let site = UnionAccessSite {
                def_id: self.def_id,
                location,
            };
            self.push_access(*place, AccessKind::Write, site, 0, Some((union_ty, field)));
            local_field_update = Some((place.local, Some((union_ty, field))));
        } else if let StatementKind::Assign(box (place, rvalue)) = &statement.kind
            && place.projection.is_empty()
            && let Some(union_ty) = self.local_union_ty(place.local)
        {
            // Propagate known active field through simple union value moves/copies.
            let propagated = match rvalue {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if src.projection.is_empty() =>
                {
                    self.union_local_known_field.get(&src.local).copied()
                }
                _ => None,
            };
            let next = propagated.filter(|(src_ty, _)| *src_ty == union_ty);
            local_field_update = Some((place.local, next));
        }

        // Handle struct aggregate assignment that moves/copies a union value into a union field.
        // This lets us preserve concrete union field info across:
        //   _2 = U { b: ... };
        //   _1 = S { u: move _2, ... };
        if let StatementKind::Assign(box (dst_place, rvalue)) = &statement.kind
            && let Rvalue::Aggregate(box AggregateKind::Adt(_, _, _, _, _), operands) = rvalue
            && let TyKind::Adt(dst_adt, dst_args) = dst_place.ty(self.body, self.tcx).ty.kind()
            && dst_adt.is_struct()
        {
            let site = UnionAccessSite {
                def_id: self.def_id,
                location,
            };
            for (field_idx, field_def) in dst_adt.non_enum_variant().fields.iter_enumerated() {
                let field_ty = field_def.ty(self.tcx, dst_args);
                let TyKind::Adt(field_adt, _) = field_ty.kind() else {
                    continue;
                };
                if !field_adt.is_union() {
                    continue;
                }
                let Some((src_union_ty, src_field)) = operands
                    .get(field_idx)
                    .and_then(|op| self.known_union_field_from_operand(op))
                else {
                    continue;
                };
                if src_union_ty != field_adt.did() {
                    continue;
                }

                let union_field_place =
                    dst_place.project_deeper(&[PlaceElem::Field(field_idx, field_ty)], self.tcx);
                self.push_access(
                    union_field_place,
                    AccessKind::Write,
                    site,
                    0,
                    Some((src_union_ty, src_field)),
                );
                // Avoid adding an additional coarse Top write for the same Assign statement.
                self.skip_store_locations.insert(location);
            }
        }

        self.super_statement(statement, location);

        if let Some((local, state)) = local_field_update {
            match state {
                Some(state) => {
                    self.union_local_known_field.insert(local, state);
                }
                None => {
                    self.union_local_known_field.remove(&local);
                }
            }
        }
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        // Ignore lhs of union init (already handled in visit_statement)
        if self.skip_store_locations.contains(&location)
            && matches!(
                context,
                PlaceContext::MutatingUse(
                    MutatingUseContext::Store | MutatingUseContext::AsmOutput
                )
            )
        {
            return;
        }

        // Ignore lhs of union init (already handled in visit_statement)
        if self
            .init_lhs
            .get(&location)
            .is_some_and(|local| *local == place.local)
            && matches!(
                context,
                PlaceContext::MutatingUse(
                    MutatingUseContext::Store | MutatingUseContext::AsmOutput
                )
            )
            && place.projection.is_empty()
        {
            return;
        }

        // Classify read/write
        let Some(kind) = classify_access(context) else {
            return;
        };

        let site = UnionAccessSite {
            def_id: self.def_id,
            location,
        };
        self.push_access(*place, kind, site, 0, None);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        // Handle modelled functions
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind
            && let Some(callee) = self.resolve_callee(func)
            && !self.tcx.is_mir_available(callee)
            && let Some(fn_model) = model::lookup_fn_model(self.tcx, callee)
        {
            for effect in fn_model.arg_effects {
                let Some(arg) = args.get(effect.arg_index) else {
                    continue;
                };
                let Some(place) = arg.node.place() else {
                    continue;
                };
                let kind = match effect.kind {
                    ArgEffectKind::Read => AccessKind::Read,
                    ArgEffectKind::Write => AccessKind::Write,
                };
                let site = UnionAccessSite {
                    def_id: self.def_id,
                    location,
                };
                self.push_access(place, kind, site, effect.deref_count, None);
            }
        }
        self.super_terminator(terminator, location);
    }
}

impl<'tcx, 'a> BodyUnionAccessCollector<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        def_id: LocalDefId,
        result: &'a andersen::AnalysisResult,
        union_instances: &'a [UnionMemoryInstance],
        instance_to_union_ty: &'a FxHashMap<UnionMemoryInstance, DefId>,
    ) -> Self {
        Self {
            tcx,
            body,
            def_id,
            result,
            union_instances,
            instance_to_union_ty,
            seen: FxHashSet::default(),
            accesses: Vec::new(),
            init_lhs: FxHashMap::default(),
            skip_store_locations: FxHashSet::default(),
            union_local_known_field: FxHashMap::default(),
        }
    }

    /// Apply a projection on each node
    fn project_nodes(&self, nodes: Vec<LocNode>, elem: PlaceElem<'tcx>) -> Vec<LocNode> {
        let mut next = Vec::new();
        match elem {
            PlaceElem::Deref => {
                for node in nodes {
                    if let Some(LocEdges::Deref(succs)) = self.result.graph.get(&node) {
                        next.extend(succs.iter().copied());
                        continue;
                    }
                    let p0 = LocNode {
                        prefix: 0,
                        index: node.index,
                    };
                    if let Some(LocEdges::Deref(succs)) = self.result.graph.get(&p0) {
                        next.extend(succs.iter().copied());
                    }
                }
            }
            PlaceElem::Field(field, _) => {
                for node in nodes {
                    if let Some(LocEdges::Fields(succs)) = self.result.graph.get(&node)
                        && field.index() < succs.len()
                    {
                        next.push(succs[field]);
                    }
                }
            }
            PlaceElem::Index(_) => {
                for node in nodes {
                    if let Some(LocEdges::Index(succ)) = self.result.graph.get(&node) {
                        next.push(*succ);
                    }
                }
            }
            _ => {
                next = nodes;
            }
        }

        let mut seen = FxHashSet::default();
        next.retain(|n| seen.insert(*n));
        next
    }

    fn alias_target_locs(
        &self,
        place: Place<'tcx>,
        implicit_deref_count: usize,
    ) -> Vec<andersen::Loc> {
        let Some(start) = self.result.var_nodes.get(&(self.def_id, place.local)) else {
            return vec![];
        };
        let mut frontier = vec![*start];

        for elem in place.projection.iter() {
            frontier = self.project_nodes(frontier, elem);
            if frontier.is_empty() {
                return vec![];
            }
        }

        // handle implicit deref at modelled functions
        for _ in 0..implicit_deref_count {
            frontier = self.project_nodes(frontier, PlaceElem::Deref);
            if frontier.is_empty() {
                return vec![];
            }
        }

        let mut out = Vec::new();
        let mut seen = FxHashSet::default();
        for loc in frontier.into_iter().map(|n| n.index) {
            if seen.insert(loc) {
                out.push(loc);
            }
        }
        out
    }

    fn find_aliasing_union_instances(
        &self,
        place: Place<'tcx>,
        implicit_deref_count: usize,
    ) -> Vec<UnionMemoryInstance> {
        let mut out = vec![];
        for target in self.alias_target_locs(place, implicit_deref_count) {
            let target_end = self.result.ends[target];
            for instance in self.union_instances {
                if ranges_overlap(target, target_end, instance.root, instance.end) {
                    out.push(*instance);
                }
            }
        }

        let mut seen = FxHashSet::default();
        out.retain(|i| seen.insert(*i));
        out
    }

    fn field_for_offset(offset: usize, offsets: &[usize]) -> Option<usize> {
        if offsets.len() < 2 {
            return None;
        }
        if offset >= *offsets.last().unwrap() {
            return None;
        }
        (0..(offsets.len() - 1)).find(|&i| offsets[i] <= offset && offset < offsets[i + 1])
    }

    fn detect_field_from_syntax(
        &self,
        place: Place<'tcx>,
        union_ty: Option<DefId>,
    ) -> Option<UnionAccessField> {
        for i in 0..place.projection.len() {
            let ty = if i == 0 {
                self.body.local_decls[place.local].ty
            } else {
                Place::ty_from(
                    place.local,
                    &place.projection[..i],
                    &self.body.local_decls,
                    self.tcx,
                )
                .ty
            };

            let TyKind::Adt(adt, _) = ty.kind() else {
                continue;
            };
            if !adt.is_union() {
                continue;
            }
            if union_ty.is_some_and(|union_ty| union_ty != adt.did()) {
                return None;
            }

            if let PlaceElem::Field(field_idx, _) = place.projection[i] {
                return Some(UnionAccessField::Field(field_idx.as_usize()));
            }

            return Some(UnionAccessField::Top);
        }

        let ty = place.ty(self.body, self.tcx).ty;
        if let TyKind::Adt(adt, _) = ty.kind()
            && adt.is_union()
        {
            if union_ty.is_some_and(|union_ty| union_ty != adt.did()) {
                return None;
            }
            if place.projection.is_empty()
                && let Some((known_union_ty, known_field)) =
                    self.union_local_known_field.get(&place.local).copied()
                && known_union_ty == adt.did()
            {
                return Some(known_field);
            }
            return Some(UnionAccessField::Top);
        }
        None
    }

    fn local_union_ty(&self, local: Local) -> Option<DefId> {
        let ty = self.body.local_decls[local].ty;
        let TyKind::Adt(adt, _) = ty.kind() else {
            return None;
        };
        if adt.is_union() {
            Some(adt.did())
        } else {
            None
        }
    }

    fn known_union_field_from_operand(
        &self,
        op: &Operand<'tcx>,
    ) -> Option<(DefId, UnionAccessField)> {
        let place = match *op {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        self.union_local_known_field.get(&place.local).copied()
    }

    fn detect_field_from_points_to(
        &self,
        place: Place<'tcx>,
        instance: UnionMemoryInstance,
        implicit_deref_count: usize,
    ) -> UnionAccessField {
        let Some(offsets) = self.result.union_offsets.get(&instance.root) else {
            unreachable!("Expected union instance to have offsets");
            // return UnionAccessField::Top;
        };

        let mut found: Option<usize> = None;
        for target in self.alias_target_locs(place, implicit_deref_count) {
            let target_end = self.result.ends[target];
            if !ranges_overlap(target, target_end, instance.root, instance.end) {
                continue;
            }
            let start =
                std::cmp::max(target.index(), instance.root.index()) - instance.root.index();
            let end =
                std::cmp::min(target_end.index(), instance.end.index()) - instance.root.index();
            for off in start..=end {
                let Some(field) = Self::field_for_offset(off, offsets) else {
                    return UnionAccessField::Top;
                };
                match found {
                    None => found = Some(field),
                    Some(prev) if prev == field => {}
                    Some(_) => return UnionAccessField::Top,
                }
            }
        }
        // println!(
        //     "Detecting field for access at {place:?} of field {found:?} in function {:?}:",
        //     self.def_id
        // );
        found.map_or(UnionAccessField::Top, UnionAccessField::Field)
    }

    fn detect_field(
        &self,
        place: Place<'tcx>,
        instance: UnionMemoryInstance,
        implicit_deref_count: usize,
    ) -> Option<(DefId, UnionAccessField)> {
        let instance_union_ty = self.instance_to_union_ty.get(&instance).copied();
        let union_ty = instance_union_ty?;
        if let Some(syntax_field) = self.detect_field_from_syntax(place, instance_union_ty) {
            return Some((union_ty, syntax_field));
        }
        Some((
            union_ty,
            self.detect_field_from_points_to(place, instance, implicit_deref_count),
        ))
    }

    /// Push an access to the collector
    /// - If field is none, it trys to detect the accessed field
    fn push_access(
        &mut self,
        place: Place<'tcx>,
        kind: AccessKind,
        site: UnionAccessSite,
        implicit_deref_count: usize,
        type_field: Option<(DefId, UnionAccessField)>,
    ) {
        let instances = self.find_aliasing_union_instances(place, implicit_deref_count);
        if instances.is_empty() {
            return;
        }

        for instance in instances {
            let mapped_union_ty = self.instance_to_union_ty.get(&instance).copied();
            let (union_ty, field) = match type_field {
                Some((union_ty, field)) => {
                    // A place may alias multiple union instances.
                    // Use the provided field only for matching instance type,
                    // otherwise fall back to per-instance field detection.
                    if let Some(mapped_union_ty) = mapped_union_ty
                        && mapped_union_ty == union_ty
                    {
                        (Some(mapped_union_ty), field)
                    } else {
                        let Some((detected_union_ty, detected_field)) =
                            self.detect_field(place, instance, implicit_deref_count)
                        else {
                            continue;
                        };
                        (Some(detected_union_ty), detected_field)
                    }
                }
                None => {
                    let Some((union_ty, field)) =
                        self.detect_field(place, instance, implicit_deref_count)
                    else {
                        continue;
                    };
                    (Some(union_ty), field)
                }
            };

            let access = DetectedAccess {
                kind,
                site,
                field,
                instance,
                resolved_union_ty: union_ty
                    .expect("union type should be resolved before pushing access"),
            };
            if self.seen.insert(access) {
                self.accesses.push(access);
            }
        }
    }

    fn is_union_init(
        &self,
        place: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Option<(DefId, UnionAccessField)> {
        let TyKind::Adt(adt, _) = self.body.local_decls[place.local].ty.kind() else {
            return None;
        };
        if !adt.is_union() || !place.projection.is_empty() {
            return None;
        }

        let Rvalue::Aggregate(box AggregateKind::Adt(_, _, _, _, Some(field_idx)), _) = rvalue
        else {
            return None;
        };

        Some((adt.did(), UnionAccessField::Field(field_idx.as_usize())))
    }

    fn resolve_callee(&self, func: &Operand<'tcx>) -> Option<DefId> {
        if let Some((callee, _)) = func.const_fn_def() {
            return Some(callee);
        }
        let place = func.place()?;
        let ty = place.ty(self.body, self.tcx).ty;
        if let TyKind::FnDef(def_id, _) = ty.kind() {
            Some(*def_id)
        } else {
            None
        }
    }
}

fn classify_access(context: PlaceContext) -> Option<AccessKind> {
    match context {
        PlaceContext::NonUse(_) => None,
        PlaceContext::MutatingUse(MutatingUseContext::Store | MutatingUseContext::AsmOutput) => {
            Some(AccessKind::Write)
        }
        PlaceContext::MutatingUse(MutatingUseContext::Projection)
        | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) => None,
        PlaceContext::NonMutatingUse(
            NonMutatingUseContext::Copy
            | NonMutatingUseContext::Inspect
            | NonMutatingUseContext::Move,
        ) => Some(AccessKind::Read),
        _ => None,
    }
}

fn ranges_overlap(
    a_start: andersen::Loc,
    a_end: andersen::Loc,
    b_start: andersen::Loc,
    b_end: andersen::Loc,
) -> bool {
    a_start <= b_end && b_start <= a_end
}
