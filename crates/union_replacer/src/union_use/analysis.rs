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
    ty::{TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;
use utils::ty_shape;

use super::model::{self, ArgEffectKind};
use crate::union_use::callgraph::CondensationGraph;

pub fn analyze(
    tcx: TyCtxt,
    condensation_graphs: &FxHashMap<LocalDefId, CondensationGraph>,
    print_mir: bool,
    use_optimized_mir: bool,
    verbose: bool,
) -> UnionUses {
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx, use_optimized_mir);

    let points_to_config = andersen::Config {
        use_optimized_mir,
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
        _print_all_local_bodies_with_points_to(tcx, &may_points_to, use_optimized_mir);
    }

    if verbose {
        println!("\nUnion use analysis result:");
    }

    identify_union_uses(
        tcx,
        may_points_to,
        condensation_graphs,
        use_optimized_mir,
        verbose,
    )
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

#[derive(Default)]
pub struct UnionInstanceUses {
    /// Read operations grouped by function for this union memory instance.
    pub reads: FxHashMap<LocalDefId, Vec<UnionRead>>,
    /// Write operations grouped by function for this union memory instance.
    pub writes: FxHashMap<LocalDefId, Vec<UnionWrite>>,
}

#[derive(Default)]
pub struct UnionTypeUses {
    /// Memory-instance-level summary for this union type.
    pub instances: FxHashMap<UnionMemoryInstance, UnionInstanceUses>,
}

pub struct UnionUses {
    /// `union type def_id -> per-instance uses`.
    pub uses: FxHashMap<DefId, UnionTypeUses>,
}

impl std::fmt::Debug for UnionInstanceUses {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "READ:")?;
        let mut read_entries = self.reads.iter().collect::<Vec<_>>();
        read_entries.sort_by_key(|(def_id, _)| format!("{def_id:?}"));
        for (def_id, reads) in read_entries {
            writeln!(f, "\t{def_id:?}:")?;
            let mut locs = reads.iter().map(|r| r.site.location).collect::<Vec<_>>();
            locs.sort_by_key(|loc| (loc.block.index(), loc.statement_index));
            for loc in locs {
                writeln!(f, "\t\t{loc:?}")?;
            }
        }

        writeln!(f, "WRITE:")?;
        let mut write_entries = self.writes.iter().collect::<Vec<_>>();
        write_entries.sort_by_key(|(def_id, _)| format!("{def_id:?}"));
        for (def_id, writes) in write_entries {
            writeln!(f, "\t{def_id:?}:")?;
            let mut locs = writes.iter().map(|w| w.site.location).collect::<Vec<_>>();
            locs.sort_by_key(|loc| (loc.block.index(), loc.statement_index));
            for loc in locs {
                writeln!(f, "\t\t{loc:?}")?;
            }
        }
        Ok(())
    }
}

impl std::fmt::Debug for UnionTypeUses {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut instances = self.instances.iter().collect::<Vec<_>>();
        instances.sort_by_key(|(instance, _)| instance.root.index());
        for (instance, uses) in instances {
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

impl std::fmt::Debug for UnionUses {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut entries = self.uses.iter().collect::<Vec<_>>();
        entries.sort_by_key(|(def_id, _)| format!("{def_id:?}"));
        for (union_ty, type_uses) in entries {
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
    result: andersen::AnalysisResult,
    condensation_graphs: &FxHashMap<LocalDefId, CondensationGraph>,
    use_optimized_mir: bool,
    verbose: bool,
) -> UnionUses {
    let mut union_uses: FxHashMap<DefId, UnionTypeUses> = FxHashMap::default();
    let mut instance_to_union_ty: FxHashMap<UnionMemoryInstance, DefId> = FxHashMap::default();
    let mut all_accesses: Vec<DetectedAccess> = Vec::new();
    let union_instances: Vec<_> = result
        .union_offsets
        .keys()
        .copied()
        .map(|root| UnionMemoryInstance {
            root,
            end: result.ends[root],
        })
        .collect();
    // if verbose {
    //     println!("Union Instances: {union_instances:?}");
    // }

    let mut target_fns: FxHashSet<LocalDefId> = FxHashSet::default();
    for graph in condensation_graphs.values() {
        for node in &graph.nodes {
            for def_id in &node.members {
                if let Some(local_def_id) = def_id.as_local() {
                    target_fns.insert(local_def_id);
                }
            }
        }
    }

    // Collect stage:
    // - seed instance->type from local declarations
    // - collect accesses/hints from body traversal
    for def_id in target_fns {
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            unreachable!(
                "Expected function or assoc function, got {:?}",
                tcx.def_kind(def_id)
            );
        }
        if !tcx.is_mir_available(def_id.to_def_id()) {
            continue;
        }

        _with_body(tcx, def_id, use_optimized_mir, |body| {
            for (local, decl) in body.local_decls.iter_enumerated() {
                let Some(node) = result.var_nodes.get(&(def_id, local)) else {
                    continue;
                };
                if let TyKind::Adt(adt, _) = decl.ty.kind()
                    && adt.is_union()
                {
                    let instance = UnionMemoryInstance {
                        root: node.index,
                        end: result.ends[node.index],
                    };
                    if result.union_offsets.contains_key(&instance.root) {
                        instance_to_union_ty.entry(instance).or_insert(adt.did());
                    }
                }
            }
        });

        let (accesses, hints) = _with_body(tcx, def_id, use_optimized_mir, |body| {
            let mut collector =
                BodyUnionAccessCollector::new(tcx, body, def_id, &result, &union_instances);
            collector.visit_body(body);
            (collector.accesses, collector.instance_union_tys)
        });

        for (instance, union_ty) in hints {
            instance_to_union_ty.entry(instance).or_insert(union_ty);
        }
        all_accesses.extend(accesses);
    }

    // if verbose {
    //     println!("instance->type map: {instance_to_union_ty:?}");
    // }

    // Merge stage:
    // - assign union types to accesses based on hints and instance->type map
    for access in &all_accesses {
        if let Some(union_ty) = access.resolved_union_ty {
            instance_to_union_ty
                .entry(access.instance)
                .or_insert(union_ty);
        }
    }
    for access in all_accesses {
        let union_ty = access
            .resolved_union_ty
            .or_else(|| instance_to_union_ty.get(&access.instance).copied());
        let Some(union_ty) = union_ty else {
            continue;
        };
        let uses = union_uses
            .entry(union_ty)
            .or_default()
            .instances
            .entry(access.instance)
            .or_default();
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

    let res = UnionUses { uses: union_uses };
    if verbose {
        println!("{res:?}");
    }
    res
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
    resolved_union_ty: Option<DefId>,
}

struct BodyUnionAccessCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    def_id: LocalDefId,
    result: &'a andersen::AnalysisResult,
    union_instances: &'a [UnionMemoryInstance],
    seen: FxHashSet<DetectedAccess>,
    accesses: Vec<DetectedAccess>,
    instance_union_tys: FxHashMap<UnionMemoryInstance, DefId>,
    init_lhs_overrides: FxHashMap<Location, Local>,
}

impl<'tcx> MirVisitor<'tcx> for BodyUnionAccessCollector<'tcx, '_> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if let StatementKind::Assign(box (place, rvalue)) = &statement.kind
            && let Some((union_ty, field)) = self.detect_union_init_field(*place, rvalue)
        {
            self.harvest_instance_hint(*place);
            self.init_lhs_overrides.insert(location, place.local);
            let site = UnionAccessSite {
                def_id: self.def_id,
                location,
            };
            self.push_access_with_override(
                *place,
                AccessKind::Write,
                site,
                0,
                Some((union_ty, field)),
            );
        }

        self.super_statement(statement, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if matches!(
            context,
            PlaceContext::MutatingUse(MutatingUseContext::Store | MutatingUseContext::AsmOutput)
        ) && place.projection.is_empty()
            && self
                .init_lhs_overrides
                .get(&location)
                .is_some_and(|local| *local == place.local)
        {
            self.harvest_instance_hint(*place);
            return;
        }

        self.harvest_instance_hint(*place);

        let Some(kind) = Self::classify(context) else {
            return;
        };
        let site = UnionAccessSite {
            def_id: self.def_id,
            location,
        };
        self.push_access(*place, kind, site, 0);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind
            && let Some(callee) = self.resolve_call_callee(func)
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
                self.push_access(place, kind, site, effect.deref_count);
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
    ) -> Self {
        Self {
            tcx,
            body,
            def_id,
            result,
            union_instances,
            seen: FxHashSet::default(),
            accesses: Vec::new(),
            instance_union_tys: FxHashMap::default(),
            init_lhs_overrides: FxHashMap::default(),
        }
    }

    fn classify(context: PlaceContext) -> Option<AccessKind> {
        match context {
            PlaceContext::NonUse(_) => None,
            PlaceContext::MutatingUse(
                MutatingUseContext::Store | MutatingUseContext::AsmOutput,
            ) => Some(AccessKind::Write),
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
        next.sort_by_key(|n| (n.index.index(), n.prefix));
        next.dedup();
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
        for _ in 0..implicit_deref_count {
            frontier = self.project_nodes(frontier, PlaceElem::Deref);
            if frontier.is_empty() {
                return vec![];
            }
        }
        for elem in place.projection.iter() {
            frontier = self.project_nodes(frontier, elem);
            if frontier.is_empty() {
                return vec![];
            }
        }
        let mut out: Vec<_> = frontier.into_iter().map(|n| n.index).collect();
        out.sort_by_key(|l| l.index());
        out.dedup();
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
                if Self::ranges_overlap(target, target_end, instance.root, instance.end) {
                    out.push(*instance);
                }
            }
        }
        out.sort_by_key(|i| i.root.index());
        out.dedup();
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

    fn detect_field_from_points_to(
        &self,
        place: Place<'tcx>,
        instance: UnionMemoryInstance,
        implicit_deref_count: usize,
    ) -> UnionAccessField {
        let Some(offsets) = self.result.union_offsets.get(&instance.root) else {
            return UnionAccessField::Top;
        };
        let mut found: Option<usize> = None;
        for target in self.alias_target_locs(place, implicit_deref_count) {
            let target_end = self.result.ends[target];
            if !Self::ranges_overlap(target, target_end, instance.root, instance.end) {
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
        found.map_or(UnionAccessField::Top, UnionAccessField::Field)
    }

    fn push_access(
        &mut self,
        place: Place<'tcx>,
        kind: AccessKind,
        site: UnionAccessSite,
        implicit_deref_count: usize,
    ) {
        self.push_access_with_override(place, kind, site, implicit_deref_count, None);
    }

    fn push_access_with_override(
        &mut self,
        place: Place<'tcx>,
        kind: AccessKind,
        site: UnionAccessSite,
        implicit_deref_count: usize,
        override_field: Option<(DefId, UnionAccessField)>,
    ) {
        let instances = self.find_aliasing_union_instances(place, implicit_deref_count);
        if instances.is_empty() {
            return;
        }
        let (resolved_union_ty, syntax_field) = match override_field {
            Some((union_ty, field)) => (Some(union_ty), field),
            None => self.detect_union_field_and_type(place),
        };
        for instance in instances {
            let field = match syntax_field {
                UnionAccessField::Top => {
                    self.detect_field_from_points_to(place, instance, implicit_deref_count)
                }
                UnionAccessField::Field(_) => syntax_field,
            };
            let access = DetectedAccess {
                kind,
                site,
                field,
                instance,
                resolved_union_ty,
            };
            if self.seen.insert(access) {
                self.accesses.push(access);
            }
        }
    }

    fn detect_union_init_field(
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

    fn harvest_instance_hint(&mut self, place: Place<'tcx>) {
        let (resolved_union_ty, _) = self.detect_union_field_and_type(place);
        let Some(resolved_union_ty) = resolved_union_ty else {
            return;
        };
        for instance in self.find_aliasing_union_instances(place, 0) {
            self.instance_union_tys
                .entry(instance)
                .or_insert(resolved_union_ty);
        }
    }

    fn detect_union_field_and_type(&self, place: Place<'tcx>) -> (Option<DefId>, UnionAccessField) {
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

            if let PlaceElem::Field(field_idx, _) = place.projection[i] {
                return (
                    Some(adt.did()),
                    UnionAccessField::Field(field_idx.as_usize()),
                );
            }

            return (Some(adt.did()), UnionAccessField::Top);
        }

        let ty = place.ty(self.body, self.tcx).ty;
        if let TyKind::Adt(adt, _) = ty.kind()
            && adt.is_union()
        {
            return (Some(adt.did()), UnionAccessField::Top);
        }
        (None, UnionAccessField::Top)
    }

    fn resolve_call_callee(&self, func: &Operand<'tcx>) -> Option<DefId> {
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

fn _with_body<'tcx, R, F: FnOnce(&Body<'tcx>) -> R>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    use_optimized_mir: bool,
    f: F,
) -> R {
    if use_optimized_mir {
        f(tcx.optimized_mir(def_id.to_def_id()))
    } else {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();
        f(body)
    }
}

#[derive(Clone, Copy)]
struct LocalLocInfo {
    owner: LocalDefId,
    local: Local,
    root: andersen::Loc,
    end: andersen::Loc,
}

fn _build_local_loc_infos(result: &andersen::AnalysisResult) -> Vec<LocalLocInfo> {
    let mut infos = Vec::with_capacity(result.var_nodes.len());
    for ((owner, local), node) in &result.var_nodes {
        let root = node.index;
        let end = result.ends[root];
        infos.push(LocalLocInfo {
            owner: *owner,
            local: *local,
            root,
            end,
        });
    }
    infos.sort_by_key(|info| info.root.index());
    infos
}

fn _find_local_loc_info(loc: andersen::Loc, infos: &[LocalLocInfo]) -> Option<LocalLocInfo> {
    infos
        .iter()
        .copied()
        .find(|info| info.root <= loc && loc <= info.end)
}

fn _format_target_loc(
    loc: andersen::Loc,
    result: &andersen::AnalysisResult,
    infos: &[LocalLocInfo],
) -> String {
    let end = result.ends[loc];
    if let Some(info) = _find_local_loc_info(loc, infos) {
        let owner = info.owner;
        let local = info.local;
        let offset = loc.index() - info.root.index();
        if offset == 0 {
            format!("{owner:?}::{local:?} [L{}..=L{}]", loc.index(), end.index())
        } else {
            format!(
                "{owner:?}::{local:?}+{offset} [L{}..=L{}]",
                loc.index(),
                end.index()
            )
        }
    } else {
        format!("L{}..=L{}", loc.index(), end.index())
    }
}

fn _print_local_points_to<'a>(
    def_id: LocalDefId,
    body: &Body<'a>,
    _tcx: TyCtxt<'a>,
    result: &andersen::AnalysisResult,
    infos: &[LocalLocInfo],
) {
    println!("\tLOCAL MAY-POINTS-TO:");
    for (local, decl) in body.local_decls.iter_enumerated() {
        let Some(node) = result.var_nodes.get(&(def_id, local)) else {
            println!("\t\t{local:?}: {:?} -> no index", decl.ty);
            continue;
        };
        let root = node.index;
        let root_end = result.ends[root];
        let sols = &result.solutions[root];
        if sols.is_empty() {
            println!(
                "\t\t{local:?}: {:?} [L{}..=L{}] -> {{}}",
                decl.ty,
                root.index(),
                root_end.index()
            );
            continue;
        }

        let mut targets = Vec::new();
        for target in sols.iter() {
            targets.push(_format_target_loc(target, result, infos));
        }
        println!(
            "\t\t{local:?}: {:?} [L{}..=L{}] -> {{{}}}",
            decl.ty,
            root.index(),
            root_end.index(),
            targets.join(", ")
        );
    }
}

fn _print_all_local_bodies_with_points_to<'a>(
    tcx: TyCtxt<'a>,
    result: &andersen::AnalysisResult,
    use_optimized_mir: bool,
) {
    let infos = _build_local_loc_infos(result);
    for def_id in tcx.hir_body_owners() {
        let _ = _print_local_body(def_id, tcx, result, true, &infos, use_optimized_mir);
    }
}

fn _print_body<'a>(
    def_id: LocalDefId,
    tcx: TyCtxt<'a>,
    body: &Body<'a>,
    result: &andersen::AnalysisResult,
    print_mir: bool,
    infos: &[LocalLocInfo],
    func_calls: &mut Vec<DefId>,
) {
    if print_mir {
        let args: FxHashSet<_> = body.args_iter().collect();
        for (local, decl) in body.local_decls.iter_enumerated() {
            if local == Local::from_usize(0) {
                println!("\tRETURN: {local:?} -> {:?}", decl.ty);
            } else if args.contains(&local) {
                println!("\tARG: {local:?} -> {:?}", decl.ty);
            } else {
                println!("\tLOCAL: {local:?} -> {:?}", decl.ty);
            }
        }
    }
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        if print_mir {
            println!("\tBB: {bb:?}");
        }
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            if print_mir && let StatementKind::Assign(box (place, _)) = &stmt.kind {
                let ty = place.ty(body, tcx).ty;
                println!("\t\tSTMT {stmt_idx}: {stmt:?}\n\t\t{ty:?}\n");
            }
        }
        if print_mir {
            println!("\t\tTERM: {:?}", bbd.terminator().kind);
            if let TerminatorKind::Call {
                func, destination, ..
            } = &bbd.terminator().kind
            {
                let ty = destination.ty(body, tcx).ty;
                println!("\t\t{ty:?}");

                if let Some((func_def_id, _)) = func.const_fn_def() {
                    func_calls.push(func_def_id);
                }
            }
        }
    }
    if print_mir {
        _print_local_points_to(def_id, body, tcx, result, infos);
    }
}

/// Print the MIR body of a local function definition.
/// Return: a list of function DefIds called within the body.
fn _print_local_body<'a>(
    def_id: LocalDefId,
    tcx: TyCtxt<'a>,
    result: &andersen::AnalysisResult,
    print_mir: bool,
    infos: &[LocalLocInfo],
    use_optimized_mir: bool,
) -> Option<Vec<DefId>> {
    let mut func_calls = Vec::new();
    if tcx.def_kind(def_id) != DefKind::Fn {
        return None;
    }
    if print_mir {
        println!("\nDEF: {def_id:?}");
    }

    if use_optimized_mir {
        let body: &Body<'_> = tcx.optimized_mir(def_id.to_def_id());
        _print_body(def_id, tcx, body, result, print_mir, infos, &mut func_calls);
    } else {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();
        _print_body(def_id, tcx, body, result, print_mir, infos, &mut func_calls);
    }
    Some(func_calls)
}
