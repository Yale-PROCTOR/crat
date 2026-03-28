// use etrace::some_or;
use points_to::{
    andersen,
    andersen::{LocEdges, LocNode},
};
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, Body, Local, Location, Operand, Place, PlaceElem, RETURN_PLACE, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor as MirVisitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;
use utils::ty_shape;

use super::{
    callgraph::{ReturnLocs, UnionCallContext},
    model::{self, ArgEffectKind},
    utils::{print_all_local_bodies_with_points_to, with_body},
};

pub fn analyze(
    tcx: TyCtxt,
    target_union_tys: &[LocalDefId],
    call_contexts: &FxHashMap<LocalDefId, UnionCallContext>,
    return_locs: &ReturnLocs,
    print_mir: bool,
    verbose: bool,
    c_exposed_fns: &FxHashSet<String>,
) -> UnionUseResult {
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx, false);

    let points_to_config = andersen::Config {
        use_optimized_mir: false,
        // c_exposed_fns: FxHashSet::from([].into_iter().collect()),
        c_exposed_fns: c_exposed_fns.clone(),
    };

    let pre = andersen::pre_analyze(&points_to_config, &tss, tcx);

    let solutions = andersen::analyze(&points_to_config, &pre, &tss, tcx);

    let may_points_to = andersen::post_analyze(&points_to_config, pre, solutions, &tss, tcx);

    if print_mir {
        print_all_local_bodies_with_points_to(tcx, &may_points_to);
    }

    if verbose {
        println!("\nUnion use analysis result:");
    }

    identify_union_uses(
        tcx,
        target_union_tys,
        may_points_to,
        call_contexts,
        return_locs,
        verbose,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnionAccessField {
    /// Access to a concrete union field index.
    Field(usize),
    /// Access may refer to one of multiple concrete union fields.
    Fields(u64),
    /// Sound over-approximation when exact field cannot be resolved.
    Top,
}

impl UnionAccessField {
    fn from_bit_mask(bit_mask: u64) -> Self {
        match bit_mask.count_ones() {
            0 => Self::Top,
            1 => Self::Field(bit_mask.trailing_zeros() as usize),
            _ => Self::Fields(bit_mask),
        }
    }

    pub fn to_fields(self, tcx: TyCtxt<'_>, union_ty: DefId) -> FxHashSet<usize> {
        let field_count = tcx.adt_def(union_ty).all_fields().count();
        match self {
            Self::Field(index) => std::iter::once(index).collect(),
            Self::Fields(bit_mask) => (0..field_count)
                .filter(|&index| index < u64::BITS as usize && (bit_mask & (1u64 << index)) != 0)
                .collect(),
            Self::Top => (0..field_count).collect(),
        }
    }

    pub fn format_for_union(self, tcx: TyCtxt<'_>, union_ty: DefId) -> String {
        match self {
            Self::Field(index) => {
                let ty = union_field_ty(tcx, union_ty, self)
                    .map(|ty| format!("{ty:?}"))
                    .unwrap_or_else(|| "?".to_string());
                format!("field#{index}\t({ty})")
            }
            Self::Fields(bit_mask) => {
                let adt = tcx.adt_def(union_ty);
                let field_count = adt.all_fields().count();
                let all_fields_bit_mask = if field_count == 0 {
                    0
                } else if field_count >= u64::BITS as usize {
                    u64::MAX
                } else {
                    (1u64 << field_count) - 1
                };
                if bit_mask == all_fields_bit_mask {
                    return "top\t(unknown)".to_string();
                }
                let mut parts = Vec::new();
                for (index, _) in adt.all_fields().enumerate() {
                    if index >= u64::BITS as usize {
                        break;
                    }
                    if bit_mask & (1u64 << index) == 0 {
                        continue;
                    }
                    let ty = union_field_ty(tcx, union_ty, Self::Field(index))
                        .map(|ty| format!("{ty:?}"))
                        .unwrap_or_else(|| "?".to_string());
                    parts.push(format!("field#{index} ({ty})"));
                }
                if parts.is_empty() {
                    "fields\t(?)".to_string()
                } else {
                    format!("fields\t({})", parts.join(", "))
                }
            }
            Self::Top => "top\t(unknown)".to_string(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UnionMemoryInstance {
    /// Root location of the union memory instance in points-to indexing.
    pub root: andersen::Loc,
    /// Inclusive end of the union memory instance (`ends[root]`).
    pub end: andersen::Loc,
}

#[derive(Clone)]
struct UnionLayout {
    offsets: Vec<usize>,
    len: usize,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CopyPoint {
    Entry(LocalDefId),
    Location {
        def_id: LocalDefId,
        location: Location,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CopySource {
    pub point: CopyPoint,
    pub source_instance: UnionMemoryInstance,
    pub source_site: UnionAccessSite,
}

pub fn format_access(tcx: TyCtxt<'_>, union_ty: DefId, access: &impl HasUnionField) -> String {
    access.union_field().format_for_union(tcx, union_ty)
}

pub fn union_field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: DefId,
    field: UnionAccessField,
) -> Option<Ty<'tcx>> {
    match field {
        UnionAccessField::Field(index) => {
            let adt = tcx.adt_def(union_ty);
            let field = adt.all_fields().nth(index)?;
            Some(tcx.type_of(field.did).instantiate_identity())
        }
        UnionAccessField::Fields(_) | UnionAccessField::Top => None,
    }
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
    /// Value-copy boundaries whose source writes should be inherited by this instance.
    pub copies: Vec<CopySource>,
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
            for (loc, field) in reads.iter().map(|r| (r.site.location, r.field)) {
                writeln!(f, "\t\t{loc:?}-{field:?}")?;
            }
        }

        writeln!(f, "WRITE:")?;
        for (def_id, writes) in &self.writes {
            writeln!(f, "\t{def_id:?}:")?;
            for (loc, field) in writes.iter().map(|w| (w.site.location, w.field)) {
                writeln!(f, "\t\t{loc:?}-{field:?}")?;
            }
        }
        writeln!(f, "COPY_INIT:")?;
        for copy in &self.copies {
            writeln!(f, "\t\t{copy:?}")?;
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
    return_locs: &ReturnLocs,
    verbose: bool,
) -> UnionUseResult {
    let target_union_ty_set: FxHashSet<DefId> = target_union_tys
        .iter()
        .map(|def_id| def_id.to_def_id())
        .collect();
    let union_layouts = build_union_layouts(tcx, target_union_tys);

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
                    &target_union_ty_set,
                    &union_layouts,
                    &mut instance_to_union_ty,
                );
            }

            let mut collector = BodyUnionInstanceCollector::new(
                tcx,
                body,
                def_id,
                &result,
                &target_union_ty_set,
                &union_layouts,
                &mut instance_to_union_ty,
            );
            collector.visit_body(body);
        });
    }

    let union_instances: Vec<UnionMemoryInstance> = instance_to_union_ty.keys().copied().collect();

    // Pass 2
    // Collect union instance accesses and classify them
    // - collect accesses using the finalized instance-to-type map
    let mut all_accesses: Vec<DetectedAccess> = Vec::new();
    let mut all_copies: Vec<PendingCopy> = Vec::new();

    for &def_id in &target_fns {
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            unreachable!("Expected function, got {:?}", tcx.def_kind(def_id));
        }
        if !tcx.is_mir_available(def_id.to_def_id()) {
            continue;
        }

        let (accesses, copies) = with_body(tcx, def_id, |body| {
            let mut collector = BodyUnionAccessCollector::new(
                tcx,
                body,
                def_id,
                BodyUnionAccessContext {
                    result: &result,
                    union_instances: &union_instances,
                    instance_to_union_ty: &instance_to_union_ty,
                    union_layouts: &union_layouts,
                },
                return_locs,
            );
            collector.visit_body(body);
            (collector.accesses, collector.copies)
        });
        all_accesses.extend(accesses);
        all_copies.extend(copies);
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

    for copy_init in all_copies {
        union_uses
            .entry(copy_init.union_ty)
            .or_default()
            .instances
            .entry(copy_init.target_instance)
            .or_default()
            .copies
            .push(CopySource {
                point: copy_init.point,
                source_instance: copy_init.source_instance,
                source_site: copy_init.source_site,
            });
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
    target_union_ty_set: &FxHashSet<DefId>,
    union_layouts: &FxHashMap<DefId, UnionLayout>,
    out: &mut FxHashMap<UnionMemoryInstance, DefId>,
) {
    let TyKind::Adt(adt, args) = ty.kind() else {
        return;
    };

    if adt.is_union() {
        let Some(instance) = union_instance_from_root_and_ty(node.index, adt.did(), union_layouts)
        else {
            return;
        };
        if target_union_ty_set.contains(&adt.did()) {
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
            target_union_ty_set,
            union_layouts,
            out,
        );
    }
}

fn union_instance_from_root_and_ty(
    root: andersen::Loc,
    union_ty: DefId,
    union_layouts: &FxHashMap<DefId, UnionLayout>,
) -> Option<UnionMemoryInstance> {
    let union_len = union_layouts.get(&union_ty)?.len;
    if union_len == 0 {
        return None;
    }
    Some(UnionMemoryInstance {
        root,
        end: root + (union_len - 1),
    })
}

fn build_union_layouts(
    tcx: TyCtxt<'_>,
    target_union_tys: &[LocalDefId],
) -> FxHashMap<DefId, UnionLayout> {
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx, false);
    target_union_tys
        .iter()
        .filter_map(|def_id| {
            let ty = tcx.type_of(def_id.to_def_id()).instantiate_identity();
            let ty_shape = tss.tys.get(&ty)?;
            let ty_shape::TyShape::Struct(len, fields, is_union) = ty_shape else {
                return None;
            };
            if !is_union {
                return None;
            }
            let mut offsets: Vec<usize> = fields.iter().map(|(offset, _)| *offset).collect();
            offsets.push(*len);
            Some((def_id.to_def_id(), UnionLayout { offsets, len: *len }))
        })
        .collect()
}

struct BodyUnionInstanceCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    def_id: LocalDefId,
    result: &'a andersen::AnalysisResult,
    target_union_ty_set: &'a FxHashSet<DefId>,
    union_layouts: &'a FxHashMap<DefId, UnionLayout>,
    out: &'a mut FxHashMap<UnionMemoryInstance, DefId>,
}

impl<'tcx> MirVisitor<'tcx> for BodyUnionInstanceCollector<'tcx, '_> {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
        self.collect_union_instances_from_place(*place, 0);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
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
                self.collect_union_instances_from_place(place, effect.deref_count);
            }
        }
        self.super_terminator(terminator, location);
    }
}

impl<'tcx, 'a> BodyUnionInstanceCollector<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        def_id: LocalDefId,
        result: &'a andersen::AnalysisResult,
        target_union_ty_set: &'a FxHashSet<DefId>,
        union_layouts: &'a FxHashMap<DefId, UnionLayout>,
        out: &'a mut FxHashMap<UnionMemoryInstance, DefId>,
    ) -> Self {
        Self {
            tcx,
            body,
            def_id,
            result,
            target_union_ty_set,
            union_layouts,
            out,
        }
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

    fn collect_union_instances_from_place(
        &mut self,
        place: Place<'tcx>,
        implicit_deref_count: usize,
    ) {
        let mut prefix = Place::from(place.local);
        let mut current_ty = self.body.local_decls[place.local].ty;
        self.record_union_place(prefix, current_ty);
        for elem in place.projection.iter() {
            prefix = prefix.project_deeper(&[elem], self.tcx);
            let Some(next_ty) = projected_ty(current_ty, elem) else {
                return;
            };
            current_ty = next_ty;
            self.record_union_place(prefix, current_ty);
        }
        for _ in 0..implicit_deref_count {
            let elem = PlaceElem::Deref;
            prefix = prefix.project_deeper(&[elem], self.tcx);
            let Some(next_ty) = projected_ty(current_ty, elem) else {
                return;
            };
            current_ty = next_ty;
            self.record_union_place(prefix, current_ty);
        }
    }

    fn record_union_place(&mut self, place: Place<'tcx>, ty: Ty<'tcx>) {
        let TyKind::Adt(adt, _) = ty.kind() else {
            return;
        };
        if !adt.is_union() || !self.target_union_ty_set.contains(&adt.did()) {
            return;
        }
        let targets =
            alias_target_locs_with_tys(self.result, self.body, self.tcx, self.def_id, place, 0);
        for root in targets {
            if let Some(instance) =
                union_instance_from_root_and_ty(root, adt.did(), self.union_layouts)
            {
                self.out.entry(instance).or_insert(adt.did());
            }
        }
    }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct PendingCopy {
    point: CopyPoint,
    target_instance: UnionMemoryInstance,
    source_instance: UnionMemoryInstance,
    union_ty: DefId,
    source_site: UnionAccessSite,
}

struct BodyUnionAccessContext<'a> {
    result: &'a andersen::AnalysisResult,
    union_instances: &'a [UnionMemoryInstance],
    instance_to_union_ty: &'a FxHashMap<UnionMemoryInstance, DefId>,
    union_layouts: &'a FxHashMap<DefId, UnionLayout>,
}

/// Collect union accesses and classify them
struct BodyUnionAccessCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    def_id: LocalDefId,
    context: BodyUnionAccessContext<'a>,
    return_locs: &'a ReturnLocs,
    seen: FxHashSet<DetectedAccess>,
    accesses: Vec<DetectedAccess>,
    init_lhs: FxHashMap<Location, Local>,
    skip_locations: FxHashSet<Location>,
    local_known_union_fields:
        FxHashMap<Local, FxHashMap<KnownUnionPath, (DefId, UnionAccessField)>>,
    instance_syntax_field_cache: FxHashMap<(UnionMemoryInstance, DefId), Option<UnionAccessField>>,
    seen_copies: FxHashSet<PendingCopy>,
    copies: Vec<PendingCopy>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum KnownUnionPathElem {
    Deref,
    Field(usize),
}

type KnownUnionPath = Vec<KnownUnionPathElem>;

type LocFieldUpdate = (
    Local,
    Option<FxHashMap<KnownUnionPath, (DefId, UnionAccessField)>>,
);

impl<'tcx> MirVisitor<'tcx> for BodyUnionAccessCollector<'tcx, '_> {
    /// Priority 1: handle special assignments before generic access classification.
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        let mut local_field_update: Option<LocFieldUpdate> = None;

        // Handle union init statement
        // i.e. let x = UnionType { field: ... };
        if let StatementKind::Assign(box (place, rvalue)) = &statement.kind
            && let Some((union_ty, field)) = self.is_union_init(*place, rvalue)
        {
            self.init_lhs.insert(location, place.local);
            self.skip_locations.insert(location);
            let site = UnionAccessSite {
                def_id: self.def_id,
                location,
            };
            self.push_access(*place, AccessKind::Write, site, 0, Some((union_ty, field)));
            let mut known_fields = FxHashMap::default();
            known_fields.insert(vec![], (union_ty, field));
            local_field_update = Some((place.local, Some(known_fields)));
        // Handle writes that copy a known union field into another union path.
        // s.u = v; where u, v is the same union and last written field of v is known
        } else if let StatementKind::Assign(box (dst_place, rvalue)) = &statement.kind
            && let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue
            && (!dst_place.projection.is_empty() || !src.projection.is_empty())
            && let Some((dst_union_ty, dst_path)) = self.union_path_of_place(*dst_place)
            && let Some((src_union_ty, src_field)) = self.known_field(*src)
            && src_union_ty == dst_union_ty
        {
            let site = UnionAccessSite {
                def_id: self.def_id,
                location,
            };
            self.push_access(
                *dst_place,
                AccessKind::Write,
                site,
                0,
                Some((dst_union_ty, src_field)),
            );
            self.skip_locations.insert(location);
            self.set_known_field_for_path(dst_place.local, dst_path, (dst_union_ty, src_field));
        // Handle whole-local assignments that propagate known union field state.
        // dst = src if last written field of rvalue is known (src: local or aggregate)
        } else if let StatementKind::Assign(box (dst_place, rvalue)) = &statement.kind
            && dst_place.projection.is_empty()
        {
            match rvalue {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if src.projection.is_empty() =>
                {
                    let site = UnionAccessSite {
                        def_id: self.def_id,
                        location,
                    };

                    self.record_copy(
                        CopyRecord {
                            body: self.body,
                            def_id: self.def_id,
                            place: *src,
                        },
                        CopyRecord {
                            body: self.body,
                            def_id: self.def_id,
                            place: *dst_place,
                        },
                        CopyPoint::Location {
                            def_id: self.def_id,
                            location,
                        },
                        site,
                    );

                    self.skip_locations.insert(location);

                    local_field_update = Some((
                        dst_place.local,
                        self.local_known_union_fields.get(&src.local).cloned(),
                    ));
                }
                Rvalue::Aggregate(box AggregateKind::Adt(_, _, _, _, _), operands) if matches!(dst_place.ty(self.body, self.tcx).ty.kind(), TyKind::Adt(adt, _) if adt.is_struct()) =>
                {
                    let site = UnionAccessSite {
                        def_id: self.def_id,
                        location,
                    };
                    let mut known_fields = FxHashMap::default();
                    let TyKind::Adt(dst_adt, dst_args) =
                        dst_place.ty(self.body, self.tcx).ty.kind()
                    else {
                        unreachable!();
                    };
                    for (field_idx, field_def) in
                        dst_adt.non_enum_variant().fields.iter_enumerated()
                    {
                        let field_ty = field_def.ty(self.tcx, dst_args);
                        let path_prefix = vec![KnownUnionPathElem::Field(field_idx.as_usize())];

                        if let TyKind::Adt(field_adt, _) = field_ty.kind()
                            && field_adt.is_union()
                            && let Some((src_union_ty, src_field)) = operands
                                .get(field_idx)
                                .and_then(|op| self.operand_known_field(op))
                            && src_union_ty == field_adt.did()
                        {
                            let union_field_place = dst_place
                                .project_deeper(&[PlaceElem::Field(field_idx, field_ty)], self.tcx);
                            self.push_access(
                                union_field_place,
                                AccessKind::Write,
                                site,
                                0,
                                Some((src_union_ty, src_field)),
                            );
                            known_fields.insert(path_prefix, (src_union_ty, src_field));
                            self.skip_locations.insert(location);
                            continue;
                        }

                        let Some(src_paths) = operands
                            .get(field_idx)
                            .and_then(|op| self.operand_known_fields(op))
                        else {
                            continue;
                        };

                        for (src_path, state) in src_paths {
                            let mut dst_path = path_prefix.clone();
                            dst_path.extend(src_path);
                            if let Some(union_place) =
                                self.place_for_local_field_path(dst_place.local, &dst_path)
                            {
                                self.push_access(
                                    union_place,
                                    AccessKind::Write,
                                    site,
                                    0,
                                    Some(state),
                                );
                                self.skip_locations.insert(location);
                            }
                            known_fields.insert(dst_path, state);
                        }
                    }

                    local_field_update = Some((
                        dst_place.local,
                        if known_fields.is_empty() {
                            None
                        } else {
                            Some(known_fields)
                        },
                    ));
                }
                _ => {
                    local_field_update = Some((dst_place.local, None));
                }
            }
        }

        self.super_statement(statement, location);

        if let Some((local, state)) = local_field_update {
            self.instance_syntax_field_cache.clear();
            match state {
                Some(state) => {
                    self.local_known_union_fields.insert(local, state);
                }
                None => {
                    self.local_known_union_fields.remove(&local);
                }
            }
        }
    }

    /// Priority 2: classify ordinary MIR place accesses not already handled above.
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if self.skip_locations.contains(&location) {
            return;
        }

        // Ignore lhs of union init (already handled in visit_statement)
        if self.skip_locations.contains(&location)
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
        self.set_known_field_from_syntax(*place);
    }

    /// Priority 3: synthesize accesses for extern calls without MIR bodies.
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
            && let Some(callee) = self.resolve_callee(func)
            && let Some(callee_local) = callee.as_local()
            && self.tcx.is_mir_available(callee)
        {
            with_body(self.tcx, callee_local, |callee_body| {
                let mut handled_copy = false;
                for (param_local, arg) in callee_body.args_iter().zip(args.iter()) {
                    let Some(arg_place) = arg.node.place() else {
                        continue;
                    };
                    handled_copy |= self.record_copy(
                        CopyRecord {
                            body: self.body,
                            def_id: self.def_id,
                            place: arg_place,
                        },
                        CopyRecord {
                            body: callee_body,
                            def_id: callee_local,
                            place: Place::from(param_local),
                        },
                        CopyPoint::Entry(callee_local),
                        UnionAccessSite {
                            def_id: self.def_id,
                            location,
                        },
                    );
                }

                for &ret_loc in self.return_locs.get(&callee_local).into_iter().flatten() {
                    handled_copy |= self.record_copy(
                        CopyRecord {
                            body: callee_body,
                            def_id: callee_local,
                            place: Place::from(RETURN_PLACE),
                        },
                        CopyRecord {
                            body: self.body,
                            def_id: self.def_id,
                            place: *destination,
                        },
                        CopyPoint::Location {
                            def_id: self.def_id,
                            location,
                        },
                        UnionAccessSite {
                            def_id: callee_local,
                            location: ret_loc,
                        },
                    );
                }

                if handled_copy {
                    self.skip_locations.insert(location);
                }
            });
        }

        // Handle modelled functions
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind
            && let Some(callee) = self.resolve_callee(func)
            && !self.tcx.is_mir_available(callee)
            && let Some(fn_model) = model::lookup_fn_model(self.tcx, callee)
        {
            let site = UnionAccessSite {
                def_id: self.def_id,
                location,
            };
            let mut handled_copy = false;

            'copy_effects: for effect in fn_model.copy_effects {
                // Suppose length 1 for now
                let Some(dst_arg) = args.get(effect.dst_arg_index) else {
                    continue;
                };
                let Some(src_arg) = args.get(effect.src_arg_index) else {
                    continue;
                };
                let Some(mut dst_place) = dst_arg.node.place() else {
                    continue;
                };
                let Some(mut src_place) = src_arg.node.place() else {
                    continue;
                };

                for _ in 0..effect.deref_count {
                    if projected_ty(dst_place.ty(self.body, self.tcx).ty, PlaceElem::Deref)
                        .is_none()
                        || projected_ty(src_place.ty(self.body, self.tcx).ty, PlaceElem::Deref)
                            .is_none()
                    {
                        continue 'copy_effects;
                    }
                    dst_place = dst_place.project_deeper(&[PlaceElem::Deref], self.tcx);
                    src_place = src_place.project_deeper(&[PlaceElem::Deref], self.tcx);
                }

                if !self.record_copy(
                    CopyRecord {
                        body: self.body,
                        def_id: self.def_id,
                        place: src_place,
                    },
                    CopyRecord {
                        body: self.body,
                        def_id: self.def_id,
                        place: dst_place,
                    },
                    CopyPoint::Location {
                        def_id: self.def_id,
                        location,
                    },
                    site,
                ) {
                    continue;
                }

                handled_copy = true;
                self.skip_locations.insert(location);
            }

            if !handled_copy {
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
                    self.push_access(place, kind, site, effect.deref_count, None);
                }
                return;
            }
        }
        self.super_terminator(terminator, location);
    }
}

struct CopyRecord<'tcx, 'b> {
    body: &'b Body<'tcx>,
    def_id: LocalDefId,
    place: Place<'tcx>,
}

impl<'tcx, 'a> BodyUnionAccessCollector<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        def_id: LocalDefId,
        context: BodyUnionAccessContext<'a>,
        return_locs: &'a ReturnLocs,
    ) -> Self {
        Self {
            tcx,
            body,
            def_id,
            context,
            return_locs,
            seen: FxHashSet::default(),
            accesses: Vec::new(),
            init_lhs: FxHashMap::default(),
            skip_locations: FxHashSet::default(),
            local_known_union_fields: FxHashMap::default(),
            instance_syntax_field_cache: FxHashMap::default(),
            seen_copies: FxHashSet::default(),
            copies: Vec::new(),
        }
    }

    fn aliasing_instances(
        &self,
        body: &Body<'tcx>,
        def_id: LocalDefId,
        place: Place<'tcx>,
        implicit_deref_count: usize,
    ) -> Vec<UnionMemoryInstance> {
        let mut out = vec![];
        for target in alias_target_locs_with_tys(
            self.context.result,
            body,
            self.tcx,
            def_id,
            place,
            implicit_deref_count,
        ) {
            let target_end = self.context.result.ends[target];
            for instance in self.context.union_instances {
                if ranges_overlap(target, target_end, instance.root, instance.end) {
                    out.push(*instance);
                }
            }
        }

        let mut seen = FxHashSet::default();
        out.retain(|i| seen.insert(*i));
        out
    }

    fn record_copy<'s, 't>(
        &mut self,
        source_record: CopyRecord<'tcx, 's>,
        target_record: CopyRecord<'tcx, 't>,
        point: CopyPoint,
        source_site: UnionAccessSite,
    ) -> bool {
        let mut added = false;

        let source_ty = source_record.place.ty(source_record.body, self.tcx).ty;
        let target_ty = target_record.place.ty(target_record.body, self.tcx).ty;

        if source_ty == target_ty {
            let union_paths = union_paths_in(self.tcx, source_ty);
            for (path, union_ty) in union_paths {
                let Some(source_union_place) =
                    project_path(source_record.place, source_record.body, self.tcx, &path)
                else {
                    continue;
                };
                let Some(target_union_place) =
                    project_path(target_record.place, target_record.body, self.tcx, &path)
                else {
                    continue;
                };

                let source_instances = self.aliasing_instances(
                    source_record.body,
                    source_record.def_id,
                    source_union_place,
                    0,
                );
                let target_instances = self.aliasing_instances(
                    target_record.body,
                    target_record.def_id,
                    target_union_place,
                    0,
                );

                for source_instance in source_instances.iter().copied() {
                    if self
                        .context
                        .instance_to_union_ty
                        .get(&source_instance)
                        .is_some_and(|mapped| *mapped != union_ty)
                    {
                        continue;
                    }
                    for target_instance in target_instances.iter().copied() {
                        if self
                            .context
                            .instance_to_union_ty
                            .get(&target_instance)
                            .is_some_and(|mapped| *mapped != union_ty)
                        {
                            continue;
                        }
                        let copy_init = PendingCopy {
                            point,
                            target_instance,
                            source_instance,
                            union_ty,
                            source_site,
                        };
                        if self.seen_copies.insert(copy_init) {
                            self.copies.push(copy_init);
                            added = true;
                        }
                    }
                }
            }
        }

        if !added {
            let source_instances = self.aliasing_instances(
                source_record.body,
                source_record.def_id,
                source_record.place,
                0,
            );
            let target_instances = self.aliasing_instances(
                target_record.body,
                target_record.def_id,
                target_record.place,
                0,
            );

            for source_instance in source_instances.iter().copied() {
                let Some(union_ty) = self
                    .context
                    .instance_to_union_ty
                    .get(&source_instance)
                    .copied()
                else {
                    continue;
                };
                for target_instance in target_instances.iter().copied() {
                    if self
                        .context
                        .instance_to_union_ty
                        .get(&target_instance)
                        .is_some_and(|mapped| *mapped == union_ty)
                    {
                        let copy_init = PendingCopy {
                            point,
                            target_instance,
                            source_instance,
                            union_ty,
                            source_site,
                        };
                        if self.seen_copies.insert(copy_init) {
                            self.copies.push(copy_init);
                            added = true;
                        }
                    }
                }
            }
        }

        added
    }

    fn union_field_at_offset(offset: usize, offsets: &[usize]) -> Option<usize> {
        if offsets.len() < 2 {
            return None;
        }
        if offset >= *offsets.last().unwrap() {
            return None;
        }
        (0..(offsets.len() - 1)).find(|&i| offsets[i] <= offset && offset < offsets[i + 1])
    }

    /// Field fallback priority 1: prefer the field name that is explicit in the place syntax.
    /// Field fallbacks are skipped if field identification at visit_statement succeeds
    fn resolve_field_from_syntax(
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

            for elem in &place.projection[i..] {
                if let PlaceElem::Field(field_idx, _) = elem {
                    return Some(UnionAccessField::Field(field_idx.as_usize()));
                }
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
            return Some(UnionAccessField::Top);
        }
        None
    }

    fn local_known_field(&self, local: Local) -> Option<(DefId, UnionAccessField)> {
        self.local_known_union_fields
            .get(&local)
            .and_then(|paths| paths.get(&Vec::new()).copied())
    }

    fn union_path_of_place(&self, place: Place<'tcx>) -> Option<(DefId, KnownUnionPath)> {
        let mut path = Vec::new();

        for i in 0..=place.projection.len() {
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

            if let TyKind::Adt(adt, _) = ty.kind()
                && adt.is_union()
            {
                return Some((adt.did(), path));
            }

            let Some(elem) = place.projection.get(i) else {
                break;
            };
            match elem {
                PlaceElem::Deref => path.push(KnownUnionPathElem::Deref),
                PlaceElem::Field(field_idx, _) => {
                    path.push(KnownUnionPathElem::Field(field_idx.as_usize()))
                }
                _ => return None,
            }
        }

        None
    }

    fn set_known_field_for_path(
        &mut self,
        local: Local,
        path: KnownUnionPath,
        state: (DefId, UnionAccessField),
    ) {
        self.instance_syntax_field_cache.clear();
        self.local_known_union_fields
            .entry(local)
            .or_default()
            .insert(path, state);
    }

    fn set_known_field_from_syntax(&mut self, place: Place<'tcx>) {
        let Some((union_ty, path)) = self.union_path_of_place(place) else {
            return;
        };
        let Some(field) = self.resolve_field_from_syntax(place, Some(union_ty)) else {
            return;
        };
        if matches!(field, UnionAccessField::Top) {
            return;
        }
        self.set_known_field_for_path(place.local, path, (union_ty, field));
    }

    fn operand_known_field(&self, op: &Operand<'tcx>) -> Option<(DefId, UnionAccessField)> {
        let place = match *op {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        self.local_known_field(place.local)
    }

    fn operand_known_fields(
        &self,
        op: &Operand<'tcx>,
    ) -> Option<FxHashMap<KnownUnionPath, (DefId, UnionAccessField)>> {
        let place = match *op {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        self.local_known_union_fields.get(&place.local).cloned()
    }

    /// Field fallback priority 2: reuse statement-propagated field state for this place.
    fn known_field(&self, place: Place<'tcx>) -> Option<(DefId, UnionAccessField)> {
        let (union_ty, path) = self.union_path_of_place(place)?;
        if let Some(field) = self.resolve_field_from_syntax(place, Some(union_ty))
            && !matches!(field, UnionAccessField::Top)
        {
            return Some((union_ty, field));
        }
        self.local_known_union_fields
            .get(&place.local)
            .and_then(|paths| paths.get(&path).copied())
            .filter(|(known_union_ty, _)| *known_union_ty == union_ty)
    }

    // fn local_path_nodes(&self, local: Local, path: &[KnownUnionPathElem]) -> Vec<LocNode> {
    //     let Some(start) = self.context.result.var_nodes.get(&(self.def_id, local)) else {
    //         return vec![];
    //     };

    //     let mut frontier = vec![*start];
    //     for elem in path {
    //         let mut next = Vec::new();
    //         for node in frontier {
    //             match elem {
    //                 KnownUnionPathElem::Deref => {
    //                     if let Some(LocEdges::Deref(succs)) = self.context.result.graph.get(&node) {
    //                         next.extend(succs.iter().copied());
    //                         continue;
    //                     }
    //                     let p0 = LocNode {
    //                         prefix: 0,
    //                         index: node.index,
    //                     };
    //                     if let Some(LocEdges::Deref(succs)) = self.context.result.graph.get(&p0) {
    //                         next.extend(succs.iter().copied());
    //                     }
    //                 }
    //                 KnownUnionPathElem::Field(field_idx) => {
    //                     if let Some(LocEdges::Fields(succs)) = self.context.result.graph.get(&node)
    //                         && *field_idx < succs.len()
    //                     {
    //                         next.push(succs[FieldIdx::from_usize(*field_idx)]);
    //                     }
    //                 }
    //             }
    //         }
    //         if next.is_empty() {
    //             return vec![];
    //         }
    //         let mut seen = FxHashSet::default();
    //         next.retain(|n| seen.insert(*n));
    //         frontier = next;
    //     }

    //     frontier
    // }

    // fn local_path_aliases_instance(
    //     &self,
    //     local: Local,
    //     path: &[KnownUnionPathElem],
    //     instance: UnionMemoryInstance,
    // ) -> bool {
    //     self.local_path_nodes(local, path).into_iter().any(|node| {
    //         let target = node.index;
    //         let target_end = self.context.result.ends[target];
    //         ranges_overlap(target, target_end, instance.root, instance.end)
    //     })
    // }

    // fn unique_known<I>(&self, states: I) -> Option<(DefId, UnionAccessField)>
    // where I: IntoIterator<Item = (DefId, UnionAccessField)> {
    //     let mut found = None;
    //     for state in states {
    //         match found {
    //             None => found = Some(state),
    //             Some(prev) if prev == state => {}
    //             Some(_) => return None,
    //         }
    //     }
    //     found
    // }

    // fn local_union_field(&self, local: Local, union_ty: DefId) -> Option<UnionAccessField> {
    //     self.unique_known(
    //         self.local_known_union_fields
    //             .get(&local)?
    //             .values()
    //             .copied()
    //             .filter(|(known_union_ty, _)| *known_union_ty == union_ty),
    //     )
    //     .map(|(_, field)| field)
    // }

    // fn instance_known_field(
    //     &self,
    //     local: Local,
    //     instance: UnionMemoryInstance,
    // ) -> Option<(DefId, UnionAccessField)> {
    //     self.unique_known(
    //         self.local_known_union_fields
    //             .get(&local)?
    //             .iter()
    //             .filter(|(path, _)| self.local_path_aliases_instance(local, path, instance))
    //             .map(|(_, state)| *state),
    //     )
    // }

    fn place_for_local_field_path(
        &self,
        local: Local,
        path: &[KnownUnionPathElem],
    ) -> Option<Place<'tcx>> {
        let mut place = Place::from(local);
        for elem in path {
            match elem {
                KnownUnionPathElem::Deref => {
                    place = place.project_deeper(&[PlaceElem::Deref], self.tcx);
                }
                KnownUnionPathElem::Field(field_idx) => {
                    let ty = place.ty(self.body, self.tcx).ty;
                    let TyKind::Adt(adt, args) = ty.kind() else {
                        return None;
                    };
                    let field_def = adt.all_fields().nth(*field_idx)?;
                    let field_ty = field_def.ty(self.tcx, args);
                    place = place.project_deeper(
                        &[PlaceElem::Field(FieldIdx::from_usize(*field_idx), field_ty)],
                        self.tcx,
                    );
                }
            }
        }
        Some(place)
    }

    // fn push_known_union_writes_for_local(
    //     &mut self,
    //     local: Local,
    //     known_fields: &FxHashMap<KnownUnionPath, (DefId, UnionAccessField)>,
    //     site: UnionAccessSite,
    // ) {
    //     for (path, state) in known_fields {
    //         if let Some(union_place) = self.place_for_local_field_path(local, path) {
    //             self.push_access(union_place, AccessKind::Write, site, 0, Some(*state));
    //         }
    //     }
    // }

    /// Field fallback priority 3: infer the field from overlapping points-to offsets.
    fn resolve_field_from_points_to(
        &self,
        place: Place<'tcx>,
        instance: UnionMemoryInstance,
        implicit_deref_count: usize,
    ) -> UnionAccessField {
        let Some(union_ty) = self.context.instance_to_union_ty.get(&instance).copied() else {
            return UnionAccessField::Top;
        };
        if let Some(field) =
            self.resolve_field_from_access_ty(union_ty, place, implicit_deref_count)
        {
            return field;
        }
        let Some(offsets) = self
            .context
            .union_layouts
            .get(&union_ty)
            .map(|layout| &layout.offsets)
        else {
            return UnionAccessField::Top;
        };
        let mut found_bit_mask = 0u64;
        for target in alias_target_locs_with_tys(
            self.context.result,
            self.body,
            self.tcx,
            self.def_id,
            place,
            implicit_deref_count,
        ) {
            let target_end = self.context.result.ends[target];
            if !ranges_overlap(target, target_end, instance.root, instance.end) {
                continue;
            }
            let start =
                std::cmp::max(target.index(), instance.root.index()) - instance.root.index();
            let end =
                std::cmp::min(target_end.index(), instance.end.index()) - instance.root.index();
            for off in start..=end {
                let Some(field) = Self::union_field_at_offset(off, offsets) else {
                    return UnionAccessField::Top;
                };
                if field >= u64::BITS as usize {
                    return UnionAccessField::Top;
                }
                found_bit_mask |= 1u64 << field;
            }
        }
        UnionAccessField::from_bit_mask(found_bit_mask)
    }

    // fn known_access_field(
    //     &self,
    //     place: Place<'tcx>,
    //     instance: UnionMemoryInstance,
    //     union_ty: DefId,
    //     implicit_deref_count: usize,
    // ) -> Option<UnionAccessField> {
    //     if implicit_deref_count != 0 {
    //         return None;
    //     }
    //     if place.projection.is_empty()
    //         && let Some(field) = self.local_union_field(place.local, union_ty)
    //     {
    //         return Some(field);
    //     }
    //     if let Some((known_union_ty, known_field)) = self.known_field(place)
    //         && known_union_ty == union_ty
    //     {
    //         return Some(known_field);
    //     }
    //     if place.projection.is_empty()
    //         && let Some((known_union_ty, known_field)) =
    //             self.instance_known_field(place.local, instance)
    //         && known_union_ty == union_ty
    //     {
    //         return Some(known_field);
    //     }
    //     None
    // }

    // fn single_field_from_instance_known_syntax(
    //     &mut self,
    //     instance: UnionMemoryInstance,
    //     union_ty: DefId,
    // ) -> Option<UnionAccessField> {
    //     if let Some(cached) = self.instance_syntax_field_cache.get(&(instance, union_ty)) {
    //         return *cached;
    //     }

    //     let mut candidate_bit_mask = 0u64;
    //     for (local, paths) in &self.local_known_union_fields {
    //         for (path, (known_union_ty, known_field)) in paths {
    //             if *known_union_ty != union_ty
    //                 || !self.local_path_aliases_instance(*local, path, instance)
    //             {
    //                 continue;
    //             }
    //             match *known_field {
    //                 UnionAccessField::Field(field) if field < u64::BITS as usize => {
    //                     candidate_bit_mask |= 1u64 << field;
    //                 }
    //                 UnionAccessField::Fields(bit_mask) => {
    //                     candidate_bit_mask |= bit_mask;
    //                 }
    //                 UnionAccessField::Field(_) | UnionAccessField::Top => {
    //                     self.instance_syntax_field_cache
    //                         .insert((instance, union_ty), None);
    //                     return None;
    //                 }
    //             }
    //         }
    //     }

    //     let resolved = if candidate_bit_mask.count_ones() == 1 {
    //         Some(UnionAccessField::Field(
    //             candidate_bit_mask.trailing_zeros() as usize
    //         ))
    //     } else {
    //         None
    //     };

    //     self.instance_syntax_field_cache
    //         .insert((instance, union_ty), resolved);
    //     resolved
    // }

    fn resolve_field_from_access_ty(
        &self,
        union_ty: DefId,
        place: Place<'tcx>,
        implicit_deref_count: usize,
    ) -> Option<UnionAccessField> {
        let mut access_ty = place.ty(self.body, self.tcx).ty;
        for _ in 0..implicit_deref_count {
            access_ty = projected_ty(access_ty, PlaceElem::Deref)?;
        }

        let adt = self.tcx.adt_def(union_ty);
        let mut matched_bit_mask = 0u64;
        let mut matched_count = 0usize;

        for (index, field) in adt.all_fields().enumerate() {
            let field_ty = self.tcx.type_of(field.did).instantiate_identity();
            if !field_matches_access_ty(field_ty, access_ty) {
                continue;
            }
            if index >= u64::BITS as usize {
                return Some(UnionAccessField::Top);
            }
            matched_bit_mask |= 1u64 << index;
            matched_count += 1;
        }

        if matched_count == 0 {
            None
        } else {
            Some(UnionAccessField::from_bit_mask(matched_bit_mask))
        }
    }

    fn resolve_field_for_access(
        &mut self,
        place: Place<'tcx>,
        instance: UnionMemoryInstance,
        implicit_deref_count: usize,
    ) -> Option<(DefId, UnionAccessField)> {
        let union_ty = self.context.instance_to_union_ty.get(&instance).copied()?;
        let syntax_field = self.resolve_field_from_syntax(place, Some(union_ty));
        if let Some(field) = syntax_field
            && !matches!(field, UnionAccessField::Top)
        {
            return Some((union_ty, field));
        }
        // if let Some(field) = self.single_field_from_instance_known_syntax(instance, union_ty) {
        //     return Some((union_ty, field));
        // }
        let points_to_field =
            self.resolve_field_from_points_to(place, instance, implicit_deref_count);
        if !matches!(points_to_field, UnionAccessField::Top) {
            return Some((union_ty, points_to_field));
        }
        // if let Some(field) =
        //     self.known_access_field(place, instance, union_ty, implicit_deref_count)
        //     && !matches!(field, UnionAccessField::Top)
        // {
        //     return Some((union_ty, field));
        // }
        // if let Some(field) = syntax_field {
        //     return Some((union_ty, field));
        // }
        // if let Some(field) =
        //     self.known_access_field(place, instance, union_ty, implicit_deref_count)
        // {
        //     return Some((union_ty, field));
        // }
        Some((union_ty, points_to_field))
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
        let instances =
            self.aliasing_instances(self.body, self.def_id, place, implicit_deref_count);
        if instances.is_empty() {
            return;
        }

        for instance in instances {
            let mapped_union_ty = self.context.instance_to_union_ty.get(&instance).copied();
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
                            self.resolve_field_for_access(place, instance, implicit_deref_count)
                        else {
                            continue;
                        };
                        (Some(detected_union_ty), detected_field)
                    }
                }
                None => {
                    let Some((union_ty, field)) =
                        self.resolve_field_for_access(place, instance, implicit_deref_count)
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

fn union_paths_in<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Vec<(KnownUnionPath, DefId)> {
    fn walk<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
        path: &mut KnownUnionPath,
        out: &mut Vec<(KnownUnionPath, DefId)>,
    ) {
        let TyKind::Adt(adt, args) = ty.kind() else {
            return;
        };
        if adt.is_union() {
            out.push((path.clone(), adt.did()));
            return;
        }
        if !adt.is_struct() {
            return;
        }
        for (field_idx, field) in adt.all_fields().enumerate() {
            path.push(KnownUnionPathElem::Field(field_idx));
            walk(tcx, field.ty(tcx, args), path, out);
            path.pop();
        }
    }

    let mut out = Vec::new();
    let mut path = Vec::new();
    walk(tcx, ty, &mut path, &mut out);
    out
}

fn project_path<'tcx>(
    mut place: Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    path: &[KnownUnionPathElem],
) -> Option<Place<'tcx>> {
    for elem in path {
        match elem {
            KnownUnionPathElem::Deref => {
                place = place.project_deeper(&[PlaceElem::Deref], tcx);
            }
            KnownUnionPathElem::Field(field_idx) => {
                let ty = place.ty(body, tcx).ty;
                let TyKind::Adt(adt, args) = ty.kind() else {
                    return None;
                };
                let field_def = adt.all_fields().nth(*field_idx)?;
                let field_ty = field_def.ty(tcx, args);
                place = place.project_deeper(
                    &[PlaceElem::Field(FieldIdx::from_usize(*field_idx), field_ty)],
                    tcx,
                );
            }
        }
    }
    Some(place)
}

fn project_nodes(
    result: &andersen::AnalysisResult,
    nodes: Vec<LocNode>,
    elem: PlaceElem<'_>,
) -> Vec<LocNode> {
    let mut next = Vec::new();
    match elem {
        PlaceElem::Deref => {
            for node in nodes {
                if let Some(LocEdges::Deref(succs)) = result.graph.get(&node) {
                    next.extend(succs.iter().copied());
                    continue;
                }
                let p0 = LocNode {
                    prefix: 0,
                    index: node.index,
                };
                if let Some(LocEdges::Deref(succs)) = result.graph.get(&p0) {
                    next.extend(succs.iter().copied());
                }
            }
        }
        PlaceElem::Field(field, _) => {
            for node in nodes {
                if let Some(LocEdges::Fields(succs)) = result.graph.get(&node)
                    && field.index() < succs.len()
                {
                    next.push(succs[field]);
                }
            }
        }
        PlaceElem::Index(_) => {
            for node in nodes {
                if let Some(LocEdges::Index(succ)) = result.graph.get(&node) {
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

fn project_nodes_with_tys<'tcx>(
    result: &andersen::AnalysisResult,
    nodes: Vec<LocNode>,
    elem: PlaceElem<'tcx>,
    base_ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Vec<LocNode> {
    let mut next = project_nodes(result, nodes.clone(), elem);
    if matches!(elem, PlaceElem::Field(_, _)) && next.is_empty() {
        let PlaceElem::Field(field, _) = elem else { unreachable!() };
        if let Some(offset) = field_offset_for_ty(tcx, base_ty, field.index()) {
            next = nodes
                .into_iter()
                .filter_map(|node| {
                    let index = node.index + offset;
                    if index > result.ends[node.index] {
                        return None;
                    }
                    Some(LocNode {
                        prefix: node.prefix,
                        index,
                    })
                })
                .collect();
        }
    }
    let mut seen = FxHashSet::default();
    next.retain(|n| seen.insert(*n));
    next
}

fn projected_ty<'tcx>(ty: Ty<'tcx>, elem: PlaceElem<'tcx>) -> Option<Ty<'tcx>> {
    match elem {
        PlaceElem::Deref => match ty.kind() {
            TyKind::Ref(_, inner, _) => Some(*inner),
            TyKind::RawPtr(inner, _) => Some(*inner),
            _ => None,
        },
        PlaceElem::Field(_, field_ty) => Some(field_ty),
        PlaceElem::Index(_) => match ty.kind() {
            TyKind::Array(inner, _) | TyKind::Slice(inner) => Some(*inner),
            _ => None,
        },
        _ => None,
    }
}

// Return locs that may alias the given place
fn alias_target_locs_with_tys<'tcx>(
    result: &andersen::AnalysisResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    place: Place<'tcx>,
    implicit_deref_count: usize,
) -> Vec<andersen::Loc> {
    let Some(start) = result.var_nodes.get(&(def_id, place.local)) else {
        return vec![];
    };
    let mut frontier = vec![*start];
    let mut current_ty = body.local_decls[place.local].ty;

    for elem in place.projection.iter() {
        frontier = project_nodes_with_tys(result, frontier, elem, current_ty, tcx);
        if frontier.is_empty() {
            return vec![];
        }
        let Some(next_ty) = projected_ty(current_ty, elem) else {
            return vec![];
        };
        current_ty = next_ty;
    }

    for _ in 0..implicit_deref_count {
        let elem = PlaceElem::Deref;
        frontier = project_nodes(result, frontier, elem);
        if frontier.is_empty() {
            return vec![];
        }
        let Some(next_ty) = projected_ty(current_ty, elem) else {
            return vec![];
        };
        current_ty = next_ty;
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

fn field_offset_for_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, field_index: usize) -> Option<usize> {
    let TyKind::Adt(adt, args) = ty.kind() else {
        return None;
    };
    if !adt.is_struct() && !adt.is_union() {
        return None;
    }
    let mut offset = 0;
    for (i, field) in adt.all_fields().enumerate() {
        if i == field_index {
            return Some(offset);
        }
        offset += ty_len(field.ty(tcx, args), tcx);
    }
    None
}

fn ty_len<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> usize {
    match ty.kind() {
        TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) => 1,
        TyKind::Array(inner, len) => {
            ty_len(*inner, tcx) * len.try_to_target_usize(tcx).unwrap_or(0) as usize
        }
        TyKind::Adt(adt, args) => {
            let mut len = 0;
            for field in adt.all_fields() {
                len += ty_len(field.ty(tcx, args), tcx);
            }
            len.max(1)
        }
        _ => 1,
    }
}

fn field_matches_access_ty<'tcx>(field_ty: Ty<'tcx>, access_ty: Ty<'tcx>) -> bool {
    if field_ty == access_ty {
        return true;
    }

    match field_ty.kind() {
        TyKind::Array(elem, _) | TyKind::Slice(elem) => *elem == access_ty,
        _ => false,
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
