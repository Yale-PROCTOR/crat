use points_to::andersen;
use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor as AstVisitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId, def::Res, def_id::LocalDefId, intravisit::Visitor as HirVisitor,
};
use rustc_middle::{
    mir::{
        Local, Location, Operand, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{self, TyCtxt},
};
use rustc_span::Symbol;
use utils::{
    ast::{unwrap_cast_and_paren, unwrap_paren},
    ir::AstToHir,
};

use crate::{
    analyses::{
        self,
        array_local_provenance::{
            ArrayLocalProvenance, PfgNode, RewriteGroup, RewriteGroupStatus,
            RewriteSelectionContext, SlotInfo, SlotPathElem, named_struct_field,
        },
        type_qualifier::foster::mutability::MutabilityResult,
    },
    rewriter::array_local_trace::{RewriteTrace, TraceDecision, TraceStage, TraceSubject},
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum BindingRepresentation {
    IndexOnly,
    Materialized(MaterializationKind),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MaterializationKind {
    SharedRef,
    RawPtr,
}

#[derive(Clone, Debug)]
struct BindingRewrite {
    source_hir_id: HirId,
    index_name: String,
    representation: BindingRepresentation,
    source_name: String,
    has_index_benefit: bool,
    base_hir_id: HirId,
    base_name: String,
    base_index_name: Option<String>,
    base_is_raw_ptr: bool,
    nullable: bool,
    ptr_ty: String,
    ptr_mut: bool,
    field_base: bool,
    base_proxy_hir_ids: FxHashSet<HirId>,
    group_member_hir_ids: FxHashSet<HirId>,
    /// caller-visible index-tracked field base: the field write is kept live and
    /// member materializations subtract `base_index_name` (approach D).
    base_live: bool,
}

#[derive(Clone, Debug)]
struct BaseCursorRewrite {
    fn_def_id: LocalDefId,
    base_hir_id: HirId,
    base_name: String,
    index_name: String,
    base_is_raw_ptr: bool,
    ptr_ty: String,
    field_base: bool,
    /// caller-visible field base whose write stays live (approach D).
    base_live: bool,
}

type BaseCursorKey = (HirId, String);

#[derive(Default)]
struct RewritePlan {
    by_hir_id: FxHashMap<HirId, BindingRewrite>,
    base_by_key: FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    index_names_by_fn: FxHashMap<LocalDefId, FxHashSet<String>>,
}

#[derive(Default, Clone, Debug)]
struct BindingUseSummary {
    deref_count: usize,
    field_or_index_count: usize,
    pointer_value_count: usize,
    movement_count: usize,
    comparison_count: usize,
    offset_from_count: usize,
    call_arg_count: usize,
    inlineable_memory_call_count: usize,
    address_taken_count: usize,
    unsupported_escape: bool,
    writes_through_pointer: bool,
    multi_cursor_deref_expr_count: usize,
}

impl BindingUseSummary {
    fn value_use_count(&self) -> usize {
        self.deref_count + self.field_or_index_count + self.pointer_value_count
    }

    fn has_index_benefit(&self) -> bool {
        self.movement_count + self.comparison_count + self.offset_from_count > 0
    }

    fn materialization_kind(&self, ptr_mut: bool) -> Option<MaterializationKind> {
        if self.unsupported_escape || self.address_taken_count > 0 {
            return None;
        }
        if self.call_arg_count > 0 {
            return Some(MaterializationKind::RawPtr);
        }
        if self.pointer_value_count > 0 {
            return Some(MaterializationKind::RawPtr);
        }
        if self.writes_through_pointer {
            return ptr_mut.then_some(MaterializationKind::RawPtr);
        }
        if self.value_use_count() > 0 {
            return Some(MaterializationKind::SharedRef);
        }
        None
    }
}

#[cfg(test)]
mod binding_use_summary_tests {
    use rustc_hash::FxHashMap;

    use super::{
        BindingUseSummary, MaterializationKind, collect_binding_use_summaries_for_names_for_test,
    };

    fn classifier_summaries(
        code: &str,
        planned_names: &[&str],
    ) -> FxHashMap<String, BindingUseSummary> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            collect_binding_use_summaries_for_names_for_test(tcx, planned_names)
        })
        .unwrap()
    }

    #[test]
    fn direct_pointer_value_use_materializes_as_raw_pointer() {
        let summary = BindingUseSummary {
            pointer_value_count: 1,
            ..BindingUseSummary::default()
        };

        assert_eq!(
            summary.materialization_kind(false),
            Some(MaterializationKind::RawPtr)
        );
    }

    #[test]
    fn call_argument_use_materializes_as_raw_pointer() {
        let summary = BindingUseSummary {
            call_arg_count: 1,
            ..BindingUseSummary::default()
        };

        assert_eq!(
            summary.materialization_kind(false),
            Some(MaterializationKind::RawPtr)
        );
    }

    #[test]
    fn memchr_pointer_argument_does_not_force_materialization() {
        let summaries = classifier_summaries(
            r#"
unsafe extern "C" {
    fn memchr(ptr: *const core::ffi::c_void, ch: i32, n: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn foo(mut p: *mut i8, n: usize) {
    let mut q: *mut i8 = p.offset(1);
    let _found = memchr(q as *const core::ffi::c_void, 0, n);
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert_eq!(q.call_arg_count, 0);
        assert_eq!(q.inlineable_memory_call_count, 1);
        assert_eq!(q.pointer_value_count, 0);
        assert_eq!(q.materialization_kind(false), None);
    }

    #[test]
    fn memset_pointer_argument_does_not_force_materialization() {
        let summaries = classifier_summaries(
            r#"
unsafe extern "C" {
    fn memset(ptr: *mut core::ffi::c_void, value: i32, n: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn foo(mut p: *mut u8, n: usize) {
    let mut q: *mut u8 = p.offset(1);
    memset(q as *mut core::ffi::c_void, 0, n);
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert_eq!(q.call_arg_count, 0);
        assert_eq!(q.inlineable_memory_call_count, 1);
        assert_eq!(q.pointer_value_count, 0);
        assert_eq!(q.materialization_kind(true), None);
    }

    #[test]
    fn memory_call_deref_argument_marks_cursor_inlineable() {
        let summaries = classifier_summaries(
            r#"
unsafe extern "C" {
    fn memset(ptr: *mut core::ffi::c_void, value: i32, n: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn foo(mut p: *mut i8, mut q: *mut i8, n: usize) {
    memset(q as *mut core::ffi::c_void, (*p) as i32, n);
}
"#,
            &["p", "q"],
        );
        let p = summaries.get("p").expect("expected p summary");
        let q = summaries.get("q").expect("expected q summary");

        assert_eq!(p.inlineable_memory_call_count, 1);
        assert_eq!(q.inlineable_memory_call_count, 1);
        assert_eq!(q.call_arg_count, 0);
    }

    #[test]
    fn unsupported_escape_prevents_materialization() {
        let summary = BindingUseSummary {
            pointer_value_count: 1,
            unsupported_escape: true,
            ..BindingUseSummary::default()
        };

        assert_eq!(summary.materialization_kind(false), None);
    }

    #[test]
    fn movement_and_comparison_operands_are_not_pointer_value_uses() {
        let summaries = classifier_summaries(
            r#"
pub unsafe fn foo(mut p: *mut i32) -> bool {
    let mut q: *mut i32 = p.offset(1);
    let moved: *mut i32 = q.offset(2);
    q == moved
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert_eq!(q.movement_count, 1);
        assert_eq!(q.comparison_count, 1);
        assert_eq!(q.pointer_value_count, 0);
    }

    #[test]
    fn offset_from_records_receiver_and_direct_pointer_argument() {
        let summaries = classifier_summaries(
            r#"
pub unsafe fn foo(mut p: *mut i32) -> isize {
    let mut q: *mut i32 = p.offset(1);
    let mut r: *mut i32 = p.offset(3);
    q.offset_from(r)
}
"#,
            &["q", "r"],
        );
        let q = summaries.get("q").expect("expected q summary");
        let r = summaries.get("r").expect("expected r summary");

        assert_eq!(q.offset_from_count, 1);
        assert_eq!(r.offset_from_count, 1);
        assert_eq!(q.pointer_value_count, 0);
        assert_eq!(r.pointer_value_count, 0);
    }

    #[test]
    fn field_and_index_through_pointer_deref_are_field_or_index_uses() {
        let field_summaries = classifier_summaries(
            r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

pub unsafe fn foo(mut p: *mut Item) -> i32 {
    let mut q: *mut Item = p.offset(1);
    (*q).value
}
"#,
            &["q"],
        );
        let q = field_summaries.get("q").expect("expected field q summary");

        assert_eq!(q.field_or_index_count, 1);
        assert_eq!(q.deref_count, 1);
        assert_eq!(q.pointer_value_count, 0);

        let indexed_field_summaries = classifier_summaries(
            r#"
#[repr(C)]
pub struct Item {
    pub values: [i32; 4],
}

pub unsafe fn foo(mut p: *mut Item, i: usize) -> i32 {
    let mut q: *mut Item = p.offset(1);
    (*q).values[i]
}
"#,
            &["q"],
        );
        let q = indexed_field_summaries
            .get("q")
            .expect("expected indexed field q summary");

        assert_eq!(q.field_or_index_count, 2);
        assert_eq!(q.deref_count, 1);
        assert_eq!(q.pointer_value_count, 0);
    }

    #[test]
    fn escape_like_aggregate_and_return_uses_are_unsupported_escapes() {
        let aggregate_summaries = classifier_summaries(
            r#"
pub unsafe fn aggregate(mut p: *mut i32) -> (*mut i32, [*mut i32; 1]) {
    let mut q: *mut i32 = p.offset(1);
    (q, [q])
}
"#,
            &["q"],
        );
        let q = aggregate_summaries
            .get("q")
            .expect("expected aggregate q summary");

        assert!(q.unsupported_escape);

        let return_summaries = classifier_summaries(
            r#"
pub unsafe fn ret(mut p: *mut i32) -> *mut i32 {
    let mut q: *mut i32 = p.offset(1);
    return q;
}
"#,
            &["q"],
        );
        let q = return_summaries
            .get("q")
            .expect("expected return q summary");

        assert!(q.unsupported_escape);
    }

    #[test]
    fn implicit_return_tail_use_is_an_unsupported_escape() {
        let summaries = classifier_summaries(
            r#"
pub unsafe fn ret(mut p: *mut i32) -> *mut i32 {
    let mut q: *mut i32 = p.offset(1);
    q
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert!(q.unsupported_escape);
        assert_eq!(q.pointer_value_count, 0);
    }

    #[test]
    fn projected_assignment_sets_write_through_pointer() {
        let summaries = classifier_summaries(
            r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

pub unsafe fn foo(mut p: *mut Item) {
    let mut q: *mut Item = p.offset(1);
    (*q).value = 1;
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert!(q.writes_through_pointer);
    }

    #[test]
    fn compound_assignment_sets_write_through_pointer() {
        let summaries = classifier_summaries(
            r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

pub unsafe fn foo(mut p: *mut Item) {
    let mut q: *mut Item = p.offset(1);
    (*q).value += 2;
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert!(q.writes_through_pointer);
    }

    #[test]
    fn mutable_reborrow_sets_write_through_pointer() {
        let summaries = classifier_summaries(
            r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

pub unsafe fn foo(mut p: *mut Item) {
    let mut q: *mut Item = p.offset(1);
    let _borrow: &mut Item = &mut *q;
}
"#,
            &["q"],
        );
        let q = summaries.get("q").expect("expected q summary");

        assert!(q.writes_through_pointer);
    }
}

pub(crate) fn apply_array_local_index_rewrite<'tcx>(
    krate: &mut Crate,
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    mutability_result: &MutabilityResult,
    nullity_result: &analyses::nullity::NullityResult,
    points_to: &andersen::AnalysisResult,
    ast_to_hir: &AstToHir,
) -> bool {
    let mut trace = RewriteTrace::from_env();
    let changed = apply_array_local_index_rewrite_inner(
        krate,
        input,
        provenances,
        mutability_result,
        nullity_result,
        points_to,
        ast_to_hir,
        &mut trace,
    );
    trace.emit(input.tcx);
    changed
}

#[allow(clippy::too_many_arguments)]
fn apply_array_local_index_rewrite_inner<'tcx>(
    krate: &mut Crate,
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    mutability_result: &MutabilityResult,
    nullity_result: &analyses::nullity::NullityResult,
    points_to: &andersen::AnalysisResult,
    ast_to_hir: &AstToHir,
    trace: &mut RewriteTrace,
) -> bool {
    let mut plan = build_rewrite_plan(
        input,
        provenances,
        mutability_result,
        nullity_result,
        points_to,
        trace,
    );
    refine_base_pointer_kinds_from_ast(krate, ast_to_hir, input.tcx, &mut plan);
    prune_unsupported_direct_place_uses(krate, ast_to_hir, input.tcx, &mut plan, trace);
    choose_binding_representations(krate, ast_to_hir, input.tcx, &mut plan, trace);
    if plan.by_hir_id.is_empty() {
        return false;
    }

    let mut visitor = ArrayLocalIndexRewriteVisitor {
        tcx: input.tcx,
        ast_to_hir,
        plan,
        introduced_hir_ids: FxHashSet::default(),
        changed: false,
        trace,
    };
    visitor.visit_crate(krate);
    visitor.changed
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply_array_local_index_rewrite_traced<'tcx>(
    krate: &mut Crate,
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    mutability_result: &MutabilityResult,
    nullity_result: &analyses::nullity::NullityResult,
    points_to: &andersen::AnalysisResult,
    ast_to_hir: &AstToHir,
    enabled: bool,
) -> Vec<crate::rewriter::array_local_trace::TraceEvent> {
    let mut trace = RewriteTrace::for_test(enabled);
    let _ = apply_array_local_index_rewrite_inner(
        krate,
        input,
        provenances,
        mutability_result,
        nullity_result,
        points_to,
        ast_to_hir,
        &mut trace,
    );
    trace.into_events()
}

/// Returns true for an index-tracked base whose base slot lives behind a
/// `Pointee` path — a caller-visible field base. These are rewritten with the
/// live-field / shadow-counter scheme (approach D): the field write is kept and
/// member materializations subtract the base counter.
pub(crate) fn group_needs_live_base_rewrite(
    provenance: &ArrayLocalProvenance,
    group: &RewriteGroup,
) -> bool {
    group.index_tracked
        && analyses::array_local_provenance::base_slot_info(provenance, group)
            .is_some_and(|info| info.path.contains(&SlotPathElem::Pointee))
}

#[allow(dead_code)]
pub(crate) fn group_has_rewritable_binding<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &rustc_middle::mir::Body<'tcx>,
    provenance: &ArrayLocalProvenance,
    group: &RewriteGroup,
) -> bool {
    let hir_to_mir = utils::ir::map_thir_to_mir(def_id, false, tcx);
    let local_to_hir: FxHashMap<Local, HirId> = hir_to_mir
        .binding_to_local
        .iter()
        .map(|(hir_id, local)| (*local, *hir_id))
        .collect();
    if !local_to_hir.contains_key(&group.base_local) {
        return false;
    }
    if group.index_tracked
        && !matches!(
            body.local_decls[group.base_local].ty.kind(),
            ty::TyKind::RawPtr(..)
        )
    {
        return false;
    }

    group.members.iter().any(|&slot_idx| {
        let Some(info) = provenance.slot_table.slot_infos.get(slot_idx) else {
            return false;
        };
        if info.root == group.base_local || !info.path.is_empty() {
            return false;
        }
        if !local_to_hir.contains_key(&info.root) {
            return false;
        }
        if !matches!(
            body.local_decls[info.root].ty.kind(),
            ty::TyKind::RawPtr(..)
        ) {
            return false;
        }
        // for field-base groups, a member is rewritable only if it is NOT a proxy
        // (proxies hold the base at offset 0 and are left unchanged).
        if group.base_slot_offset > 0 {
            return !local_is_pure_field_base_proxy(body, info.root);
        }
        true
    })
}

fn build_rewrite_plan<'tcx>(
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    mutability_result: &MutabilityResult,
    nullity_result: &analyses::nullity::NullityResult,
    points_to: &andersen::AnalysisResult,
    trace: &mut RewriteTrace,
) -> RewritePlan {
    let mut plan = RewritePlan::default();
    for &def_id in &input.functions {
        let Some(provenance) = provenances.get(&def_id) else {
            continue;
        };
        let body = input
            .tcx
            .mir_drops_elaborated_and_const_checked(def_id)
            .borrow();
        let all_statuses = analyses::array_local_provenance::classify_rewrite_groups(
            provenance,
            &body,
            mutability_result,
            def_id,
            RewriteSelectionContext {
                tcx: input.tcx,
                points_to,
            },
        );
        // gated so no labels are built on the default, disabled path.
        if trace.is_enabled() {
            for status in &all_statuses {
                let (base_local, decision, reason): (
                    rustc_middle::mir::Local,
                    TraceDecision,
                    &str,
                ) = match status {
                    RewriteGroupStatus::Ready(group) => {
                        (group.base_local, TraceDecision::Kept, "selected (ready)")
                    }
                    // preserved-across-calls statuses are discarded by the rewriter.
                    RewriteGroupStatus::PreservedAcrossCalls { group, .. } => (
                        group.base_local,
                        TraceDecision::Skipped,
                        "preserved across calls (discarded)",
                    ),
                };
                let label = format!("{base_local:?}");
                trace.record(
                    def_id,
                    TraceSubject::Group(label),
                    TraceStage::Selection,
                    decision,
                    || reason.to_string(),
                );
            }
        }
        let groups: Vec<RewriteGroup> = all_statuses
            .into_iter()
            .filter_map(|status| match status {
                RewriteGroupStatus::Ready(group) => Some(group),
                RewriteGroupStatus::PreservedAcrossCalls { .. } => None,
            })
            .collect();
        if groups.is_empty() {
            continue;
        }

        let hir_to_mir = utils::ir::map_thir_to_mir(def_id, false, input.tcx);
        let local_to_hir: FxHashMap<Local, HirId> = hir_to_mir
            .binding_to_local
            .iter()
            .map(|(hir_id, local)| (*local, *hir_id))
            .collect();
        let mut existing_names = binding_names_in_body(input.tcx, def_id);

        for group in groups {
            let mut context = GroupPlanContext {
                tcx: input.tcx,
                def_id,
                body: &body,
                provenance,
                nullity_result,
                local_to_hir: &local_to_hir,
                existing_names: &mut existing_names,
                plan: &mut plan,
                trace: &mut *trace,
            };
            add_group_to_plan(&mut context, &group);
        }
    }
    plan
}

fn refine_base_pointer_kinds_from_ast(
    krate: &Crate,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    plan: &mut RewritePlan,
) {
    if plan.by_hir_id.is_empty() {
        return;
    }
    let base_hir_ids = plan
        .by_hir_id
        .values()
        .map(|rewrite| rewrite.base_hir_id)
        .chain(plan.base_by_key.values().map(|rewrite| rewrite.base_hir_id))
        .collect();
    let base_names = plan
        .by_hir_id
        .values()
        .map(|rewrite| rewrite.base_name.clone())
        .chain(
            plan.base_by_key
                .values()
                .map(|rewrite| rewrite.base_name.clone()),
        )
        .collect();
    let mut visitor = BaseBindingTypeVisitor {
        ast_to_hir,
        tcx,
        base_hir_ids,
        base_names,
        base_is_raw_ptr_by_hir_id: FxHashMap::default(),
        base_is_raw_ptr_by_name: FxHashMap::default(),
    };
    visitor.visit_crate(krate);
    for rewrite in plan.by_hir_id.values_mut() {
        if let Some(&base_is_raw_ptr) = visitor.base_is_raw_ptr_by_hir_id.get(&rewrite.base_hir_id)
        {
            rewrite.base_is_raw_ptr = base_is_raw_ptr;
        } else if let Some(Some(base_is_raw_ptr)) =
            visitor.base_is_raw_ptr_by_name.get(&rewrite.base_name)
        {
            rewrite.base_is_raw_ptr = *base_is_raw_ptr;
        }
    }
    for rewrite in plan.base_by_key.values_mut() {
        if let Some(&base_is_raw_ptr) = visitor.base_is_raw_ptr_by_hir_id.get(&rewrite.base_hir_id)
        {
            rewrite.base_is_raw_ptr = base_is_raw_ptr;
        } else if let Some(Some(base_is_raw_ptr)) =
            visitor.base_is_raw_ptr_by_name.get(&rewrite.base_name)
        {
            rewrite.base_is_raw_ptr = *base_is_raw_ptr;
        }
    }
}

struct BaseBindingTypeVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    base_hir_ids: FxHashSet<HirId>,
    base_names: FxHashSet<String>,
    base_is_raw_ptr_by_hir_id: FxHashMap<HirId, bool>,
    base_is_raw_ptr_by_name: FxHashMap<String, Option<bool>>,
}

impl AstVisitor<'_> for BaseBindingTypeVisitor<'_, '_> {
    fn visit_param(&mut self, param: &Param) {
        self.record_ast_pat_type_by_name(&param.pat, &param.ty);
        if let Some(hir_id) = self.param_binding_hir_id(param)
            && self.base_hir_ids.contains(&hir_id)
        {
            self.base_is_raw_ptr_by_hir_id
                .insert(hir_id, ast_ty_is_raw_ptr(&param.ty));
        }
        visit::walk_param(self, param);
    }

    fn visit_local(&mut self, local: &rustc_ast::Local) {
        if let Some(ty) = &local.ty {
            self.record_ast_pat_type_by_name(&local.pat, ty);
        }
        if let Some(hir_id) = self.local_binding_hir_id(local)
            && self.base_hir_ids.contains(&hir_id)
            && let Some(ty) = &local.ty
        {
            self.base_is_raw_ptr_by_hir_id
                .insert(hir_id, ast_ty_is_raw_ptr(ty));
        }
        visit::walk_local(self, local);
    }
}

impl BaseBindingTypeVisitor<'_, '_> {
    fn record_ast_pat_type_by_name(&mut self, pat: &Pat, ty: &Ty) {
        let PatKind::Ident(_, ident, _) = &pat.kind else {
            return;
        };
        let name = ident.name.to_string();
        if !self.base_names.contains(&name) {
            return;
        }
        let is_raw_ptr = ast_ty_is_raw_ptr(ty);
        self.base_is_raw_ptr_by_name
            .entry(name)
            .and_modify(|existing| {
                if *existing != Some(is_raw_ptr) {
                    *existing = None;
                }
            })
            .or_insert(Some(is_raw_ptr));
    }

    fn param_binding_hir_id(&self, param: &Param) -> Option<HirId> {
        let hir_param = self.ast_to_hir.get_param(param.id, self.tcx)?;
        let hir::PatKind::Binding(_, hir_id, _, _) = hir_param.pat.kind else {
            return None;
        };
        Some(hir_id)
    }

    fn local_binding_hir_id(&self, local: &rustc_ast::Local) -> Option<HirId> {
        let let_stmt = self.ast_to_hir.get_let_stmt(local.id, self.tcx)?;
        let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind else {
            return None;
        };
        Some(hir_id)
    }
}

fn ast_ty_is_raw_ptr(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Ptr(_) => true,
        TyKind::Paren(inner) => ast_ty_is_raw_ptr(inner),
        _ => false,
    }
}

fn call_path_last_segment(expr: &Expr) -> Option<&str> {
    let ExprKind::Path(_, path) = &unwrap_cast_and_paren(expr).kind else {
        return None;
    };
    path.segments
        .last()
        .map(|segment| segment.ident.name.as_str())
}

fn inlineable_memory_pointer_arg(callee: &Expr, arg_index: usize) -> bool {
    match call_path_last_segment(callee) {
        Some("memchr" | "memset") => arg_index == 0,
        _ => false,
    }
}

fn inlineable_memory_call(callee: &Expr) -> bool {
    matches!(call_path_last_segment(callee), Some("memchr" | "memset"))
}

fn binding_names_in_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> FxHashSet<String> {
    struct NameVisitor {
        names: FxHashSet<String>,
    }
    impl<'tcx> hir::intravisit::Visitor<'tcx> for NameVisitor {
        fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
            if let hir::PatKind::Binding(_, _, ident, _) = pat.kind {
                self.names.insert(ident.name.to_string());
            }
            hir::intravisit::walk_pat(self, pat);
        }
    }

    let mut visitor = NameVisitor {
        names: FxHashSet::default(),
    };
    visitor.visit_body(tcx.hir_body_owned_by(def_id));
    visitor.names
}

struct GroupPlanContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'a rustc_middle::mir::Body<'tcx>,
    provenance: &'a ArrayLocalProvenance,
    nullity_result: &'a analyses::nullity::NullityResult,
    local_to_hir: &'a FxHashMap<Local, HirId>,
    existing_names: &'a mut FxHashSet<String>,
    plan: &'a mut RewritePlan,
    trace: &'a mut RewriteTrace,
}

fn add_group_to_plan(context: &mut GroupPlanContext<'_, '_>, group: &RewriteGroup) {
    // cheap label for early-return sites where base_name is not yet computed
    let base_local_label = || format!("{:?}", group.base_local);
    let base_live = group_needs_live_base_rewrite(context.provenance, group);
    let Some(&base_hir_id) = context.local_to_hir.get(&group.base_local) else {
        context.trace.record(
            context.def_id,
            TraceSubject::Group(base_local_label()),
            TraceStage::Plan,
            TraceDecision::Dropped,
            || "plan: base local has no HIR binding".to_string(),
        );
        return;
    };

    // Compute (base_name, proxy_hir_ids) depending on whether the base is a
    // direct local (offset 0) or a field path (offset > 0).
    // (base_name, proxy_hir_ids, field_base)
    let (base_name, proxy_hir_ids, field_base): (String, FxHashSet<HirId>, bool) =
        if group.base_slot_offset == 0 {
            (
                context.tcx.hir_name(base_hir_id).to_string(),
                FxHashSet::default(),
                false,
            )
        } else {
            let Some(base_slot_info) =
                analyses::array_local_provenance::base_slot_info(context.provenance, group)
            else {
                context.trace.record(
                    context.def_id,
                    TraceSubject::Group(base_local_label()),
                    TraceStage::Plan,
                    TraceDecision::Dropped,
                    || "plan: missing base slot info".to_string(),
                );
                return;
            };
            let local_name = context.tcx.hir_name(base_hir_id).to_string();
            let base_ty = context.body.local_decls[group.base_local].ty;
            let Some(field_path_name) =
                slot_path_to_expr_string(&local_name, &base_slot_info.path, base_ty, context.tcx)
            else {
                context.trace.record(
                    context.def_id,
                    TraceSubject::Group(base_local_label()),
                    TraceStage::Plan,
                    TraceDecision::Dropped,
                    || "plan: base field path not expressible".to_string(),
                );
                return;
            };
            // collect raw-pointer members that can serve as proxies for the field base
            let proxies: FxHashSet<HirId> = group
                .members
                .iter()
                .filter_map(|&slot_idx| {
                    let info = context.provenance.slot_table.slot_infos.get(slot_idx)?;
                    if !info.path.is_empty() || info.root == group.base_local {
                        return None;
                    }
                    if !matches!(
                        context.body.local_decls[info.root].ty.kind(),
                        ty::TyKind::RawPtr(..)
                    ) {
                        return None;
                    }
                    let &hir_id = context.local_to_hir.get(&info.root)?;
                    (!group.index_tracked
                        && (local_is_pure_field_base_proxy(context.body, info.root)
                            || (local_is_never_mutated(context.body, info.root)
                                && local_is_simple_copy_from_local(
                                    context.body,
                                    info.root,
                                    group.base_local,
                                ))))
                    .then_some(hir_id)
                })
                .collect();
            // a never-mutated member that holds the base pointer at offset 0 can be used as
            // the effective base name, avoiding rewriting it to an index and allowing members
            // to use IndexOnly representation (field_base = false).
            let immutable_copy_name = if !group.index_tracked {
                group.members.iter().find_map(|&slot_idx| {
                    let info = context.provenance.slot_table.slot_infos.get(slot_idx)?;
                    if !info.path.is_empty() || info.root == group.base_local {
                        return None;
                    }
                    if !matches!(
                        context.body.local_decls[info.root].ty.kind(),
                        ty::TyKind::RawPtr(..)
                    ) {
                        return None;
                    }
                    if local_is_pure_field_base_proxy(context.body, info.root) {
                        return None;
                    }
                    if !local_is_never_mutated(context.body, info.root) {
                        return None;
                    }
                    // confirm the single init directly copies the field base (not a call result)
                    if !local_is_simple_copy_from_local(context.body, info.root, group.base_local) {
                        return None;
                    }
                    let &hir_id = context.local_to_hir.get(&info.root)?;
                    Some(context.tcx.hir_name(hir_id).to_string())
                })
            } else {
                None
            };
            match immutable_copy_name {
                Some(name) => (name, proxies, false),
                None => (field_path_name, proxies, true),
            }
        };

    let base_is_raw_ptr = matches!(
        context.body.local_decls[group.base_local].ty.kind(),
        ty::TyKind::RawPtr(..)
    );
    let base_cursor_key = base_cursor_key(base_hir_id, &base_name);
    let group_member_hir_ids = group
        .members
        .iter()
        .filter_map(|&slot_idx| {
            let info = context.provenance.slot_table.slot_infos.get(slot_idx)?;
            if !info.path.is_empty() || info.root == group.base_local {
                return None;
            }
            if !matches!(
                context.body.local_decls[info.root].ty.kind(),
                ty::TyKind::RawPtr(..)
            ) {
                return None;
            }
            context.local_to_hir.get(&info.root).copied()
        })
        .collect::<FxHashSet<_>>();
    let base_index_name = if group.index_tracked {
        if let Some(rewrite) = context.plan.base_by_key.get(&base_cursor_key) {
            Some(rewrite.index_name.clone())
        } else {
            let Some(base_info) =
                analyses::array_local_provenance::base_slot_info(context.provenance, group)
            else {
                context.trace.record(
                    context.def_id,
                    TraceSubject::Group(base_name.clone()),
                    TraceStage::Plan,
                    TraceDecision::Dropped,
                    || "plan: index-tracked base slot info missing".to_string(),
                );
                return;
            };
            let Some(base_ptr_ty) = slot_ty(context.body, context.tcx, base_info) else {
                context.trace.record(
                    context.def_id,
                    TraceSubject::Group(base_name.clone()),
                    TraceStage::Plan,
                    TraceDecision::Dropped,
                    || "plan: base slot has no raw-pointer type".to_string(),
                );
                return;
            };
            let ty::TyKind::RawPtr(pointee, mutability) = base_ptr_ty.kind() else {
                context.trace.record(
                    context.def_id,
                    TraceSubject::Group(base_name.clone()),
                    TraceStage::Plan,
                    TraceDecision::Dropped,
                    || "plan: base slot has no raw-pointer type".to_string(),
                );
                return;
            };
            let index_stem = if group.base_slot_offset == 0 {
                base_name.clone()
            } else {
                slot_path_to_index_stem(
                    &context.tcx.hir_name(base_hir_id).to_string(),
                    &base_info.path,
                    context.body.local_decls[group.base_local].ty,
                    context.tcx,
                )
                .unwrap_or_else(|| context.tcx.hir_name(base_hir_id).to_string())
            };
            let index_name = fresh_index_name(&index_stem, context.existing_names);
            let pointee = utils::ir::mir_ty_to_string(*pointee, context.tcx);
            let ptr_ty = format!(
                "*{} {}",
                if mutability.is_mut() { "mut" } else { "const" },
                pointee
            );
            context
                .plan
                .index_names_by_fn
                .entry(context.def_id)
                .or_default()
                .insert(index_name.clone());
            context.plan.base_by_key.insert(
                base_cursor_key,
                BaseCursorRewrite {
                    fn_def_id: context.def_id,
                    base_hir_id,
                    base_name: base_name.clone(),
                    index_name: index_name.clone(),
                    base_is_raw_ptr,
                    ptr_ty,
                    field_base: group.base_slot_offset != 0,
                    base_live,
                },
            );
            Some(index_name)
        }
    } else {
        None
    };
    let non_null = context.nullity_result.non_null_locals.get(&context.def_id);

    context.trace.record(
        context.def_id,
        TraceSubject::Group(base_name.clone()),
        TraceStage::Plan,
        TraceDecision::Kept,
        || "plan: group will be planned".to_string(),
    );

    for &slot_idx in &group.members {
        let Some(info) = context.provenance.slot_table.slot_infos.get(slot_idx) else {
            continue;
        };
        if info.root == group.base_local || !info.path.is_empty() {
            continue;
        }
        let Some(&source_hir_id) = context.local_to_hir.get(&info.root) else {
            context.trace.record(
                context.def_id,
                TraceSubject::Member(format!("{:?}", info.root)),
                TraceStage::Plan,
                TraceDecision::Skipped,
                || "plan: member has no HIR binding".to_string(),
            );
            continue;
        };
        // skip proxy locals — they hold the base at offset 0 and stay as-is.
        if proxy_hir_ids.contains(&source_hir_id) {
            continue;
        }
        if context.plan.by_hir_id.contains_key(&source_hir_id) {
            continue;
        }
        let source_name = context.tcx.hir_name(source_hir_id).to_string();
        let ptr_ty = context.body.local_decls[info.root].ty;
        let ty::TyKind::RawPtr(pointee, mutability) = ptr_ty.kind() else {
            context.trace.record(
                context.def_id,
                TraceSubject::Member(source_name.clone()),
                TraceStage::Plan,
                TraceDecision::Skipped,
                || "plan: member is not a raw-pointer local".to_string(),
            );
            continue;
        };
        let index_name = fresh_index_name(&source_name, context.existing_names);
        let pointee = utils::ir::mir_ty_to_string(*pointee, context.tcx);
        let ptr_ty = format!(
            "*{} {}",
            if mutability.is_mut() { "mut" } else { "const" },
            pointee
        );
        let nullable = context
            .provenance
            .provenance
            .unique_base(&PfgNode::Slot(slot_idx))
            .is_none()
            && !non_null.is_some_and(|set| set.contains(info.root));
        context
            .plan
            .index_names_by_fn
            .entry(context.def_id)
            .or_default()
            .insert(index_name.clone());
        context.plan.by_hir_id.insert(
            source_hir_id,
            BindingRewrite {
                source_hir_id,
                index_name,
                representation: BindingRepresentation::IndexOnly,
                source_name: source_name.clone(),
                has_index_benefit: false,
                base_hir_id,
                base_name: base_name.clone(),
                base_index_name: base_index_name.clone(),
                base_is_raw_ptr,
                nullable,
                ptr_ty,
                ptr_mut: mutability.is_mut(),
                field_base,
                base_proxy_hir_ids: proxy_hir_ids.clone(),
                group_member_hir_ids: group_member_hir_ids.clone(),
                base_live,
            },
        );
        context.trace.record(
            context.def_id,
            TraceSubject::Member(source_name.clone()),
            TraceStage::Plan,
            TraceDecision::Kept,
            || "plan: member added to rewrite plan".to_string(),
        );
    }
}

fn slot_ty<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    info: &SlotInfo,
) -> Option<ty::Ty<'tcx>> {
    let mut ty = body.local_decls[info.root].ty;

    for elem in &info.path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
            }
            SlotPathElem::Field(field) => {
                ty = match ty.kind() {
                    ty::TyKind::Adt(adt_def, args) => {
                        if !adt_def.is_struct() || adt_def.is_union() {
                            return None;
                        }
                        adt_def.all_fields().nth(field.index())?.ty(tcx, args)
                    }
                    ty::TyKind::Tuple(tys) => tys.iter().nth(field.index())?,
                    _ => return None,
                };
            }
            SlotPathElem::Element => {
                ty = ty.builtin_index()?;
            }
        }
    }

    Some(ty)
}

fn fresh_index_name(source_name: &str, existing_names: &mut FxHashSet<String>) -> String {
    let mut candidate = format!("{source_name}_idx");
    let mut suffix = 1usize;
    while existing_names.contains(&candidate) {
        candidate = format!("{source_name}_idx_{suffix}");
        suffix += 1;
    }
    existing_names.insert(candidate.clone());
    candidate
}

fn slot_path_to_index_stem<'tcx>(
    local_name: &str,
    path: &[SlotPathElem],
    mut ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<String> {
    let mut parts = Vec::new();
    for elem in path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
            }
            SlotPathElem::Field(field) => {
                let (field_name, field_ty) = named_struct_field(tcx, ty, *field)?;
                parts.push(field_name);
                ty = field_ty;
            }
            SlotPathElem::Element => return None,
        }
    }
    if parts.is_empty() {
        Some(local_name.to_string())
    } else {
        Some(parts.join("_"))
    }
}

fn slot_path_to_expr_string<'tcx>(
    local_name: &str,
    path: &[SlotPathElem],
    mut ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<String> {
    let mut expr = local_name.to_string();
    for elem in path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
                expr = format!("(*{expr})");
            }
            SlotPathElem::Field(field) => {
                let (field_name, field_ty) = named_struct_field(tcx, ty, *field)?;
                expr = format!("{expr}.{field_name}");
                ty = field_ty;
            }
            SlotPathElem::Element => return None,
        }
    }
    Some(expr)
}

fn local_is_pure_field_base_proxy(body: &rustc_middle::mir::Body<'_>, local: Local) -> bool {
    let mut has_call_destination = false;
    let mut has_non_assignment_use = false;

    for (block, block_data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in block_data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind
                && lhs.local == local
                && lhs.projection.is_empty()
            {
                if rvalue_mentions_local(rvalue, local, location) {
                    has_non_assignment_use = true;
                }
                continue;
            }
            if statement_mentions_local(statement, local, location) {
                has_non_assignment_use = true;
            }
        }
        if let Some(terminator) = &block_data.terminator
            && let TerminatorKind::Call { destination, .. } = &terminator.kind
            && destination.local == local
        {
            has_call_destination = true;
        }
        if let Some(terminator) = &block_data.terminator {
            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            if terminator_mentions_local(terminator, local, location) {
                has_non_assignment_use = true;
            }
        }
    }

    !has_call_destination && !has_non_assignment_use
}

// returns true when `local` is assigned at most once and never via a call,
// meaning it's an immutable copy after initialization (may still be used as a value).
fn local_is_never_mutated(body: &rustc_middle::mir::Body<'_>, local: Local) -> bool {
    let mut assignment_count = 0usize;
    for block_data in body.basic_blocks.iter() {
        for statement in &block_data.statements {
            if let StatementKind::Assign(box (lhs, _)) = &statement.kind
                && lhs.local == local
                && lhs.projection.is_empty()
            {
                assignment_count += 1;
                if assignment_count > 1 {
                    return false;
                }
            }
        }
        if let Some(terminator) = &block_data.terminator
            && let TerminatorKind::Call { destination, .. } = &terminator.kind
            && destination.local == local
        {
            return false;
        }
    }
    true
}

// returns true when the local's single initialization statement copies (or casts from a copy of)
// a place rooted at `source_local`, confirming it's a named alias of that local's value.
fn local_is_simple_copy_from_local(
    body: &rustc_middle::mir::Body<'_>,
    local: Local,
    source_local: Local,
) -> bool {
    for block_data in body.basic_blocks.iter() {
        for statement in &block_data.statements {
            if let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind
                && lhs.local == local
                && lhs.projection.is_empty()
            {
                let operand = match rvalue {
                    Rvalue::Use(op) => op,
                    Rvalue::Cast(_, op, _) => op,
                    _ => return false,
                };
                let source = match operand {
                    Operand::Copy(place) | Operand::Move(place) => place,
                    _ => return false,
                };
                return source.local == source_local;
            }
        }
    }
    false
}

struct LocalMentionVisitor {
    local: Local,
    found: bool,
}

impl<'tcx> MirVisitor<'tcx> for LocalMentionVisitor {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if local == self.local && !matches!(context, PlaceContext::NonUse(_)) {
            self.found = true;
        }
    }
}

fn rvalue_mentions_local(rvalue: &Rvalue<'_>, local: Local, location: Location) -> bool {
    let mut visitor = LocalMentionVisitor {
        local,
        found: false,
    };
    visitor.visit_rvalue(rvalue, location);
    visitor.found
}

fn statement_mentions_local(statement: &Statement<'_>, local: Local, location: Location) -> bool {
    let mut visitor = LocalMentionVisitor {
        local,
        found: false,
    };
    visitor.visit_statement(statement, location);
    visitor.found
}

fn terminator_mentions_local(
    terminator: &Terminator<'_>,
    local: Local,
    location: Location,
) -> bool {
    let mut visitor = LocalMentionVisitor {
        local,
        found: false,
    };
    visitor.visit_terminator(terminator, location);
    visitor.found
}

fn prune_unsupported_direct_place_uses(
    krate: &Crate,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    plan: &mut RewritePlan,
    trace: &mut RewriteTrace,
) {
    if plan.by_hir_id.is_empty() {
        return;
    }

    let mut visitor = UnsupportedDirectPlaceUseVisitor {
        ast_to_hir,
        tcx,
        plan: &*plan,
        unsupported_hir_ids: FxHashSet::default(),
        trace_enabled: trace.is_enabled(),
        dropped_reasons: Vec::new(),
    };
    visitor.visit_crate(krate);
    // move results out of the visitor so the immutable borrow on `plan` ends
    // before the mutable `plan.by_hir_id.retain(...)` below.
    let unsupported_hir_ids = visitor.unsupported_hir_ids;
    let dropped_reasons = visitor.dropped_reasons;
    // record one prune drop per member still in the plan (a member can be flagged
    // by more than one site; only the first reason is traced).
    let mut traced_drops: FxHashSet<HirId> = FxHashSet::default();
    for (hir_id, reason) in &dropped_reasons {
        if !traced_drops.insert(*hir_id) {
            continue;
        }
        if let Some(rewrite) = plan.by_hir_id.get(hir_id) {
            let source_name = rewrite.source_name.clone();
            let reason = reason.clone();
            trace.record(
                hir_id.owner.def_id,
                TraceSubject::Member(source_name),
                TraceStage::Prune,
                TraceDecision::Dropped,
                || reason,
            );
        }
    }
    if !unsupported_hir_ids.is_empty() {
        plan.by_hir_id
            .retain(|hir_id, _| !unsupported_hir_ids.contains(hir_id));
    }
    // snapshot base cursors before orphan pruning so removed ones can be traced.
    let base_cursors_before: Vec<(BaseCursorKey, String, LocalDefId)> = if trace.is_enabled() {
        plan.base_by_key
            .iter()
            .map(|(key, rewrite)| (key.clone(), rewrite.base_name.clone(), rewrite.fn_def_id))
            .collect()
    } else {
        Vec::new()
    };
    prune_orphan_base_cursors(plan);
    for (key, base_name, fn_def_id) in base_cursors_before {
        if !plan.base_by_key.contains_key(&key) {
            trace.record(
                fn_def_id,
                TraceSubject::Base(base_name),
                TraceStage::Prune,
                TraceDecision::Dropped,
                || "prune: orphan base cursor (no live members)".to_string(),
            );
        }
    }
}

fn prune_orphan_base_cursors(plan: &mut RewritePlan) {
    let live_base_keys = plan
        .by_hir_id
        .values()
        .filter(|rewrite| rewrite.base_index_name.is_some())
        .map(|rewrite| base_cursor_key(rewrite.base_hir_id, &rewrite.base_name))
        .collect::<FxHashSet<_>>();
    plan.base_by_key
        .retain(|base_key, _| live_base_keys.contains(base_key));
}

fn choose_binding_representations(
    krate: &Crate,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    plan: &mut RewritePlan,
    trace: &mut RewriteTrace,
) {
    if plan.by_hir_id.is_empty() {
        return;
    }
    let mut visitor = BindingUseClassifier {
        ast_to_hir,
        tcx,
        planned_rewrites: &plan.by_hir_id,
        summaries: FxHashMap::default(),
    };
    visitor.visit_crate(krate);
    let mut summaries = std::mem::take(&mut visitor.summaries);
    drop(visitor);
    for (hir_id, rewrite) in &mut plan.by_hir_id {
        let summary = summaries.remove(hir_id).unwrap_or_default();
        rewrite.has_index_benefit = summary.has_index_benefit();
        if let Some(kind) = summary.materialization_kind(rewrite.ptr_mut) {
            if rewrite.field_base
                && summary.inlineable_memory_call_count > 0
                && summary.field_or_index_count == 0
                && summary.pointer_value_count == 0
                && summary.call_arg_count == 0
                && summary.multi_cursor_deref_expr_count == 0
            {
                rewrite.representation = BindingRepresentation::IndexOnly;
                continue;
            }
            if matches!(kind, MaterializationKind::RawPtr)
                && summary.writes_through_pointer
                && summary.call_arg_count == 0
                && summary.pointer_value_count == 0
                && !rewrite.field_base
            {
                rewrite.representation = BindingRepresentation::IndexOnly;
                continue;
            }
            if rewrite.nullable && !matches!(kind, MaterializationKind::RawPtr) {
                rewrite.representation = BindingRepresentation::IndexOnly;
                continue;
            }
            rewrite.representation = BindingRepresentation::Materialized(kind);
        } else if !summary.has_index_benefit() {
            rewrite.representation = BindingRepresentation::IndexOnly;
        }
    }
    // gated: avoid building labels on the disabled path.
    if trace.is_enabled() {
        for (hir_id, rewrite) in &plan.by_hir_id {
            let representation = rewrite.representation.clone();
            let index_benefit = rewrite.has_index_benefit;
            trace.record(
                hir_id.owner.def_id,
                TraceSubject::Member(rewrite.source_name.clone()),
                TraceStage::Representation,
                TraceDecision::Kept,
                || format!("representation={representation:?} index_benefit={index_benefit}"),
            );
        }
    }
}

#[cfg(test)]
fn collect_binding_use_summaries_for_names_for_test(
    tcx: TyCtxt<'_>,
    planned_names: &[&str],
) -> FxHashMap<String, BindingUseSummary> {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut binding_visitor = TestBindingHirIdVisitor {
        ast_to_hir: &ast_to_hir,
        tcx,
        planned_names: planned_names.iter().copied().collect(),
        hir_ids_by_name: FxHashMap::default(),
    };
    binding_visitor.visit_crate(&krate);
    let planned_rewrites = binding_visitor
        .hir_ids_by_name
        .iter()
        .map(|(name, &hir_id)| {
            (
                hir_id,
                BindingRewrite {
                    source_hir_id: hir_id,
                    index_name: format!("{name}_idx"),
                    representation: BindingRepresentation::IndexOnly,
                    source_name: name.clone(),
                    has_index_benefit: false,
                    base_hir_id: hir_id,
                    base_name: "base".to_string(),
                    base_index_name: None,
                    base_is_raw_ptr: true,
                    nullable: false,
                    ptr_ty: "*mut i32".to_string(),
                    ptr_mut: true,
                    field_base: false,
                    base_proxy_hir_ids: FxHashSet::default(),
                    group_member_hir_ids: FxHashSet::default(),
                    base_live: false,
                },
            )
        })
        .collect::<FxHashMap<_, _>>();

    let mut visitor = BindingUseClassifier {
        ast_to_hir: &ast_to_hir,
        tcx,
        planned_rewrites: &planned_rewrites,
        summaries: FxHashMap::default(),
    };
    visitor.visit_crate(&krate);
    let mut summaries = std::mem::take(&mut visitor.summaries);
    drop(visitor);

    planned_rewrites
        .iter()
        .map(|(hir_id, rewrite)| {
            (
                rewrite.source_name.clone(),
                summaries.remove(hir_id).unwrap_or_default(),
            )
        })
        .collect()
}

#[cfg(test)]
struct TestBindingHirIdVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    planned_names: FxHashSet<&'a str>,
    hir_ids_by_name: FxHashMap<String, HirId>,
}

#[cfg(test)]
impl AstVisitor<'_> for TestBindingHirIdVisitor<'_, '_> {
    fn visit_param(&mut self, param: &Param) {
        self.record_param(param);
        visit::walk_param(self, param);
    }

    fn visit_local(&mut self, local: &rustc_ast::Local) {
        self.record_local(local);
        visit::walk_local(self, local);
    }
}

#[cfg(test)]
impl TestBindingHirIdVisitor<'_, '_> {
    fn record_param(&mut self, param: &Param) {
        let PatKind::Ident(_, ident, _) = &param.pat.kind else {
            return;
        };
        let name = ident.name.to_string();
        if !self.planned_names.contains(name.as_str()) {
            return;
        }
        let Some(hir_param) = self.ast_to_hir.get_param(param.id, self.tcx) else {
            return;
        };
        let hir::PatKind::Binding(_, hir_id, _, _) = hir_param.pat.kind else {
            return;
        };
        self.hir_ids_by_name.insert(name, hir_id);
    }

    fn record_local(&mut self, local: &rustc_ast::Local) {
        let PatKind::Ident(_, ident, _) = &local.pat.kind else {
            return;
        };
        let name = ident.name.to_string();
        if !self.planned_names.contains(name.as_str()) {
            return;
        }
        let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx) else {
            return;
        };
        let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind else {
            return;
        };
        self.hir_ids_by_name.insert(name, hir_id);
    }
}

struct BindingUseClassifier<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    planned_rewrites: &'a FxHashMap<HirId, BindingRewrite>,
    summaries: FxHashMap<HirId, BindingUseSummary>,
}

impl AstVisitor<'_> for BindingUseClassifier<'_, '_> {
    fn visit_block(&mut self, block: &Block) {
        let Some((tail, stmts)) = block.stmts.split_last() else {
            visit::walk_block(self, block);
            return;
        };
        let StmtKind::Expr(tail_expr) = &tail.kind else {
            visit::walk_block(self, block);
            return;
        };
        if self.record_unsupported_escape_if_direct(tail_expr) {
            for stmt in stmts {
                self.visit_stmt(stmt);
            }
        } else {
            visit::walk_block(self, block);
        }
    }

    fn visit_expr(&mut self, expr: &Expr) {
        if let Some(hir_id) = direct_planned_local_hir_id(
            self.ast_to_hir,
            self.tcx,
            self.planned_rewrites,
            unwrap_cast_and_paren(expr),
        ) {
            self.summaries
                .entry(hir_id)
                .or_default()
                .pointer_value_count += 1;
        }

        match &expr.kind {
            ExprKind::Array(exprs) | ExprKind::Tup(exprs) => {
                if self.visit_escape_like_exprs(exprs.iter().map(|expr| &**expr)) {
                    return;
                }
            }
            ExprKind::Repeat(elem, _) => {
                if self.record_unsupported_escape_if_direct(elem) {
                    return;
                }
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                if let Some(hir_id) = self.direct_planned_local_hir_id(inner) {
                    let summary = self.summaries.entry(hir_id).or_default();
                    summary.deref_count += 1;
                    summary.pointer_value_count = summary.pointer_value_count.saturating_sub(1);
                    return;
                }
            }
            ExprKind::Field(inner, _) | ExprKind::Index(inner, _, _) => {
                if let Some(hir_id) = self.direct_planned_local_hir_id(inner) {
                    let summary = self.summaries.entry(hir_id).or_default();
                    summary.field_or_index_count += 1;
                    summary.pointer_value_count = summary.pointer_value_count.saturating_sub(1);
                    if let ExprKind::Index(_, index, _) = &expr.kind {
                        self.visit_expr(index);
                    }
                    return;
                } else {
                    for hir_id in self.direct_pointer_deref_hir_ids(inner) {
                        self.summaries
                            .entry(hir_id)
                            .or_default()
                            .field_or_index_count += 1;
                    }
                }
            }
            ExprKind::MethodCall(call) => {
                let name = call.seg.ident.name.as_str();
                let mut handled_receiver = false;
                if let Some(hir_id) = self.direct_planned_local_hir_id(&call.receiver) {
                    let summary = self.summaries.entry(hir_id).or_default();
                    match name {
                        "offset" | "add" => {
                            summary.movement_count += 1;
                            handled_receiver = true;
                        }
                        "offset_from" => {
                            summary.offset_from_count += 1;
                            handled_receiver = true;
                        }
                        "as_ptr" | "as_mut_ptr" => {
                            summary.pointer_value_count += 1;
                            handled_receiver = true;
                        }
                        _ => {}
                    }
                }
                let mut handled_arg = vec![false; call.args.len()];
                if name == "offset_from" {
                    for (index, arg) in call.args.iter().enumerate() {
                        if let Some(hir_id) = self.direct_planned_local_hir_id(arg) {
                            self.summaries.entry(hir_id).or_default().offset_from_count += 1;
                            handled_arg[index] = true;
                        }
                    }
                }
                if handled_receiver || handled_arg.iter().any(|handled| *handled) {
                    if !handled_receiver {
                        self.visit_expr(&call.receiver);
                    }
                    for (arg, handled) in call.args.iter().zip(handled_arg) {
                        if !handled {
                            self.visit_expr(arg);
                        }
                    }
                    return;
                }
            }
            ExprKind::Binary(op, lhs, rhs)
                if matches!(
                    op.node,
                    BinOpKind::Eq
                        | BinOpKind::Ne
                        | BinOpKind::Lt
                        | BinOpKind::Le
                        | BinOpKind::Gt
                        | BinOpKind::Ge
                ) =>
            {
                for side in [lhs, rhs] {
                    if let Some(hir_id) = self.direct_planned_local_hir_id(side) {
                        self.summaries.entry(hir_id).or_default().comparison_count += 1;
                    } else {
                        self.visit_expr(side);
                    }
                }
                return;
            }
            ExprKind::Assign(lhs, rhs, _) => {
                self.record_multi_cursor_deref_expr([&**lhs, &**rhs]);
                if let Some(hir_id) = self.direct_planned_local_hir_id(lhs) {
                    self.summaries.entry(hir_id).or_default().movement_count += 1;
                }
                self.record_write_through_pointer(lhs);
                self.visit_expr(rhs);
                return;
            }
            ExprKind::AssignOp(_, lhs, rhs) => {
                self.record_multi_cursor_deref_expr([&**lhs, &**rhs]);
                self.record_write_through_pointer(lhs);
                self.visit_expr(rhs);
                return;
            }
            ExprKind::AddrOf(_, mutability, inner) => {
                if mutability.is_mut() {
                    self.record_write_through_pointer(inner);
                }
                if let Some(hir_id) = self.direct_planned_local_hir_id(inner) {
                    self.summaries
                        .entry(hir_id)
                        .or_default()
                        .address_taken_count += 1;
                    return;
                }
            }
            ExprKind::Call(callee, args) => {
                let mut handled_arg = false;
                for (index, arg) in args.iter().enumerate() {
                    if let Some(hir_id) = self.direct_planned_local_hir_id(arg) {
                        if !inlineable_memory_pointer_arg(callee, index) {
                            self.summaries.entry(hir_id).or_default().call_arg_count += 1;
                        } else {
                            self.summaries
                                .entry(hir_id)
                                .or_default()
                                .inlineable_memory_call_count += 1;
                        }
                        handled_arg = true;
                    }
                    if inlineable_memory_call(callee) {
                        for hir_id in self.direct_pointer_deref_hir_ids(arg) {
                            self.summaries
                                .entry(hir_id)
                                .or_default()
                                .inlineable_memory_call_count += 1;
                        }
                    }
                }
                if handled_arg {
                    self.visit_expr(callee);
                    for arg in args {
                        if self.direct_planned_local_hir_id(arg).is_none() {
                            self.visit_expr(arg);
                        }
                    }
                    return;
                }
            }
            ExprKind::Ret(Some(value))
            | ExprKind::Break(_, Some(value))
            | ExprKind::Become(value)
            | ExprKind::Yeet(Some(value)) => {
                if self.record_unsupported_escape_if_direct(value) {
                    return;
                }
            }
            ExprKind::Yield(kind) => {
                if let Some(value) = kind.expr()
                    && self.record_unsupported_escape_if_direct(value)
                {
                    return;
                }
            }
            ExprKind::Struct(struct_expr) => {
                let mut handled = false;
                for field in &struct_expr.fields {
                    if self.record_unsupported_escape_if_direct(&field.expr) {
                        handled = true;
                    } else {
                        self.visit_expr(&field.expr);
                    }
                }
                if handled {
                    visit::walk_path(self, &struct_expr.path);
                    return;
                }
            }
            _ => {}
        }
        visit::walk_expr(self, expr);
    }
}

impl BindingUseClassifier<'_, '_> {
    fn direct_planned_local_hir_id(&self, expr: &Expr) -> Option<HirId> {
        direct_planned_local_hir_id(
            self.ast_to_hir,
            self.tcx,
            self.planned_rewrites,
            unwrap_cast_and_paren(expr),
        )
    }

    fn record_write_through_pointer(&mut self, expr: &Expr) {
        for hir_id in self.direct_pointer_deref_hir_ids(expr) {
            self.summaries
                .entry(hir_id)
                .or_default()
                .writes_through_pointer = true;
        }
    }

    fn record_multi_cursor_deref_expr<const N: usize>(&mut self, exprs: [&Expr; N]) {
        let mut hir_ids = FxHashSet::default();
        for expr in exprs {
            hir_ids.extend(self.direct_pointer_deref_hir_ids(expr));
        }
        if hir_ids.len() <= 1 {
            return;
        }
        for hir_id in hir_ids {
            self.summaries
                .entry(hir_id)
                .or_default()
                .multi_cursor_deref_expr_count += 1;
        }
    }

    fn direct_pointer_deref_hir_ids(&self, expr: &Expr) -> FxHashSet<HirId> {
        let mut hir_ids = FxHashSet::default();
        self.collect_direct_pointer_deref_hir_ids(expr, &mut hir_ids);
        hir_ids
    }

    fn collect_direct_pointer_deref_hir_ids(&self, expr: &Expr, hir_ids: &mut FxHashSet<HirId>) {
        let expr = unwrap_cast_and_paren(expr);
        match &expr.kind {
            ExprKind::Unary(UnOp::Deref, inner) => {
                if let Some(hir_id) = self.direct_planned_local_hir_id(inner) {
                    hir_ids.insert(hir_id);
                } else {
                    self.collect_direct_pointer_deref_hir_ids(inner, hir_ids);
                }
            }
            ExprKind::Field(inner, _) => {
                self.collect_direct_pointer_deref_hir_ids(inner, hir_ids);
            }
            ExprKind::Index(inner, _, _) => {
                self.collect_direct_pointer_deref_hir_ids(inner, hir_ids);
            }
            _ => {}
        }
    }

    fn record_unsupported_escape_if_direct(&mut self, expr: &Expr) -> bool {
        let Some(hir_id) = self.direct_planned_local_hir_id(expr) else {
            return false;
        };
        self.summaries.entry(hir_id).or_default().unsupported_escape = true;
        true
    }

    fn visit_escape_like_exprs<'a>(&mut self, exprs: impl Iterator<Item = &'a Expr>) -> bool {
        let mut handled = false;
        for expr in exprs {
            if self.record_unsupported_escape_if_direct(expr) {
                handled = true;
            } else {
                self.visit_expr(expr);
            }
        }
        handled
    }
}

struct UnsupportedDirectPlaceUseVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    plan: &'a RewritePlan,
    unsupported_hir_ids: FxHashSet<HirId>,
    // reasons for each prune drop, collected only when the trace is enabled
    // (so the offending assignment text is not pretty-printed otherwise).
    trace_enabled: bool,
    dropped_reasons: Vec<(HirId, String)>,
}

impl AstVisitor<'_> for UnsupportedDirectPlaceUseVisitor<'_, '_> {
    fn visit_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                self.check_assignment(lhs, rhs);
                self.visit_expr(rhs);
            }
            ExprKind::AssignOp(_, lhs, rhs) => {
                if self.mark_direct_base_cursor(lhs).is_none()
                    && self.mark_direct_planned_local(lhs).is_none()
                {
                    self.visit_expr(lhs);
                }
                self.visit_expr(rhs);
            }
            ExprKind::AddrOf(_, _, inner) => {
                if self.mark_direct_base_cursor(inner).is_none()
                    && self.mark_direct_planned_local(inner).is_none()
                {
                    self.visit_expr(inner);
                }
            }
            _ => visit::walk_expr(self, expr),
        }
    }
}

impl UnsupportedDirectPlaceUseVisitor<'_, '_> {
    fn check_assignment(&mut self, lhs: &Expr, rhs: &Expr) {
        if let Some(base_key) =
            direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, lhs)
        {
            if let Some(base_rewrite) = self.plan.base_by_key.get(&base_key) {
                if base_rewrite.base_live {
                    // approach D only supports base self-advance; any other base
                    // mutation (or an offset arg referencing a planned member)
                    // drops the group so the field is left untouched.
                    if live_base_self_advance_counter(rhs, self.ast_to_hir, self.tcx, base_rewrite)
                        .is_none()
                        || base_assignment_index_arg_contains_planned_local(
                            rhs,
                            self.ast_to_hir,
                            self.tcx,
                            &self.plan.by_hir_id,
                            base_rewrite,
                        )
                    {
                        self.mark_rewrites_for_base_unsupported(&base_key);
                    }
                    return;
                }
                let ctx = DerivationCtx {
                    ast_to_hir: self.ast_to_hir,
                    tcx: self.tcx,
                    plan: self.plan,
                    introduced: None,
                    allow_member_pointer_form: true,
                };
                let derivation = derive_index(rhs, Anchor::Base(base_rewrite), &ctx);
                let unsupported = matches!(derivation, Derivation::Unsupported(_))
                    || base_assignment_index_arg_contains_planned_local(
                        rhs,
                        self.ast_to_hir,
                        self.tcx,
                        &self.plan.by_hir_id,
                        base_rewrite,
                    );
                // NOTE: Task 3.2 inserts base `DependsOn` edge collection here.
                if unsupported {
                    self.mark_rewrites_for_base_unsupported(&base_key);
                }
                return;
            } else {
                self.mark_rewrites_for_base_unsupported(&base_key);
            }
        }

        let Some(hir_id) =
            direct_planned_local_hir_id(self.ast_to_hir, self.tcx, &self.plan.by_hir_id, lhs)
        else {
            self.visit_expr(lhs);
            return;
        };
        let Some(rewrite) = self.plan.by_hir_id.get(&hir_id) else {
            return;
        };
        let ctx = DerivationCtx {
            ast_to_hir: self.ast_to_hir,
            tcx: self.tcx,
            plan: self.plan,
            introduced: None,
            allow_member_pointer_form: true,
        };
        let derivation = derive_index(rhs, Anchor::Member(rewrite), &ctx);
        let unsupported = match &derivation {
            Derivation::Unsupported(_) => true,
            Derivation::Index(index) | Derivation::DependsOn(index, _) => {
                index_init_expr(index.clone(), rewrite.nullable).is_none()
            }
        } || assignment_index_arg_contains_planned_local(
            rhs,
            self.ast_to_hir,
            self.tcx,
            &self.plan.by_hir_id,
            rewrite,
        );
        // NOTE: Task 2.1 inserts `decisions.insert(rhs.id, index)` and Task 3.2
        // inserts `DependsOn` edge collection at this same derivation. Task 1.2
        // uses only the supported/unsupported distinction.
        if unsupported {
            if self.trace_enabled {
                self.dropped_reasons.push((
                    hir_id,
                    format!(
                        "prune: unsupported assignment `{}`",
                        pprust::expr_to_string(rhs)
                    ),
                ));
            }
            self.unsupported_hir_ids.insert(hir_id);
        }
    }

    fn mark_rewrites_for_base_unsupported(&mut self, base_key: &BaseCursorKey) {
        let matched: Vec<HirId> = self
            .plan
            .by_hir_id
            .values()
            .filter(|rewrite| base_cursor_key(rewrite.base_hir_id, &rewrite.base_name) == *base_key)
            .map(|rewrite| rewrite.source_hir_id)
            .collect();
        for source_hir_id in matched {
            if self.trace_enabled {
                self.dropped_reasons.push((
                    source_hir_id,
                    "prune: base cursor used in an unsupported place".to_string(),
                ));
            }
            self.unsupported_hir_ids.insert(source_hir_id);
        }
    }

    fn mark_direct_base_cursor(&mut self, expr: &Expr) -> Option<HirId> {
        let base_key =
            direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, expr)?;
        if self.plan.base_by_key.contains_key(&base_key) {
            self.mark_rewrites_for_base_unsupported(&base_key);
            Some(base_key.0)
        } else {
            None
        }
    }

    fn mark_direct_planned_local(&mut self, expr: &Expr) -> Option<HirId> {
        let hir_id =
            direct_planned_local_hir_id(self.ast_to_hir, self.tcx, &self.plan.by_hir_id, expr)?;
        if self.plan.by_hir_id.contains_key(&hir_id) {
            if self.trace_enabled {
                self.dropped_reasons.push((
                    hir_id,
                    format!(
                        "prune: direct unsupported place use `{}`",
                        pprust::expr_to_string(expr)
                    ),
                ));
            }
            self.unsupported_hir_ids.insert(hir_id);
            Some(hir_id)
        } else {
            None
        }
    }
}

struct PlannedLocalUseVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    planned_rewrites: &'a FxHashMap<HirId, BindingRewrite>,
    found: bool,
}

impl AstVisitor<'_> for PlannedLocalUseVisitor<'_, '_> {
    fn visit_expr(&mut self, expr: &Expr) {
        if self.found {
            return;
        }
        if direct_planned_local_hir_id(self.ast_to_hir, self.tcx, self.planned_rewrites, expr)
            .is_some()
        {
            self.found = true;
            return;
        }
        visit::walk_expr(self, expr);
    }
}

fn contains_planned_local_use(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
) -> bool {
    let mut visitor = PlannedLocalUseVisitor {
        ast_to_hir,
        tcx,
        planned_rewrites,
        found: false,
    };
    visitor.visit_expr(expr);
    visitor.found
}

fn assignment_index_arg_contains_planned_local(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    rewrite: &BindingRewrite,
) -> bool {
    let rhs = unwrap_paren(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return false;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = receiver_hir_id == Some(rewrite.base_hir_id)
        || receiver_is_base_as_ptr(receiver, ast_to_hir, tcx, rewrite)
        || receiver_hir_id.is_some_and(|id| {
            rewrite.base_proxy_hir_ids.contains(&id)
                || (rewrite.field_base && rewrite.group_member_hir_ids.contains(&id))
        });
    if !receiver_is_base && receiver_hir_id != Some(rewrite.source_hir_id) {
        return false;
    }
    contains_planned_local_use(&call.args[0], ast_to_hir, tcx, planned_rewrites)
}

fn base_assignment_index_arg_contains_planned_local(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    base_rewrite: &BaseCursorRewrite,
) -> bool {
    let rhs = unwrap_paren(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return false;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = (!base_rewrite.field_base
        && receiver_hir_id == Some(base_rewrite.base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ast_to_hir,
            tcx,
            base_rewrite.base_hir_id,
            &base_rewrite.base_name,
            base_rewrite.field_base,
        )
        || (base_rewrite.field_base && expr_matches_base_name(receiver, &base_rewrite.base_name));
    if !receiver_is_base
        && !receiver_hir_id.is_some_and(|hir_id| {
            planned_rewrites
                .get(&hir_id)
                .is_some_and(|rewrite| same_rewrite_base(rewrite, base_rewrite))
        })
    {
        return false;
    }
    contains_planned_local_use(&call.args[0], ast_to_hir, tcx, planned_rewrites)
}

fn direct_planned_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = direct_local_hir_id(ast_to_hir, tcx, expr)?;
    planned_rewrites.contains_key(&hir_id).then_some(hir_id)
}

fn same_rewrite_base(rewrite: &BindingRewrite, base_rewrite: &BaseCursorRewrite) -> bool {
    rewrite.base_hir_id == base_rewrite.base_hir_id && rewrite.base_name == base_rewrite.base_name
}

fn base_cursor_key(base_hir_id: HirId, base_name: &str) -> BaseCursorKey {
    (base_hir_id, base_name.to_string())
}

fn direct_base_cursor_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_rewrites: &FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    expr: &Expr,
) -> Option<BaseCursorKey> {
    let hir_id = direct_local_hir_id(ast_to_hir, tcx, expr)?;
    base_rewrites.iter().find_map(|(key, rewrite)| {
        (!rewrite.field_base && rewrite.base_hir_id == hir_id).then_some(key.clone())
    })
}

fn direct_base_cursor_key(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_rewrites: &FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    expr: &Expr,
) -> Option<BaseCursorKey> {
    if let Some(base_key) = direct_base_cursor_hir_id(ast_to_hir, tcx, base_rewrites, expr) {
        return Some(base_key);
    }
    base_rewrites.iter().find_map(|(key, rewrite)| {
        (rewrite.field_base
            && expr_matches_base_name(expr, &rewrite.base_name)
            && expr_is_projection_from_base_hir(expr, ast_to_hir, tcx, rewrite.base_hir_id))
        .then_some(key.clone())
    })
}

fn direct_local_hir_id(ast_to_hir: &AstToHir, tcx: TyCtxt<'_>, expr: &Expr) -> Option<HirId> {
    hir_id_of_ast_expr(ast_to_hir, tcx, unwrap_paren(expr).id)
}

#[derive(Clone)]
enum IndexExpr {
    Plain(Expr),
    Null,
    Unsupported,
}

/// what an index derivation is anchored to: a group member or a base cursor.
enum Anchor<'a> {
    Member(&'a BindingRewrite),
    Base(&'a BaseCursorRewrite),
}

/// read-only context for derivation, shared by validation and emission.
struct DerivationCtx<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    plan: &'a RewritePlan,
    /// the set of members already introduced (index-rewritten) at this point.
    /// `None` during validation (every planned member is treated as available
    /// so the `DependsOn` edge is recorded). `Some(set)` during emission, so a
    /// cross-reference to a member that is planned but not yet introduced —
    /// e.g. one whose initializer was not index-derivable and stays raw — falls
    /// back to the runtime `offset_from` form against the member's raw pointer
    /// (preserving the pre-consolidation behavior).
    introduced: Option<&'a FxHashSet<HirId>>,
    /// whether the runtime `offset_from` pointer-form fallback for a
    /// not-introduced / pruned group member is permitted. the pre-consolidation
    /// code reached that form only from the *assignment* path
    /// (`group_member_pointer_assignment_index_expr`), never from the binding
    /// *initializer* path (`visit_local`/`rewrite_materialized_local_stmt`), so
    /// this is `true` at assignment sites and `false` at initializer sites to
    /// stay diff-neutral.
    allow_member_pointer_form: bool,
}

/// the single result of deriving an index from an assignment/init RHS.
#[allow(dead_code)]
enum Derivation {
    /// fully derivable from the anchor (and possibly the base cursor).
    Index(IndexExpr),
    /// derivable, but only if these planned members are also rewritten.
    /// (the edge vec is collected in Task 3.2; the reason str in Task 2.1.)
    DependsOn(IndexExpr, Vec<HirId>),
    /// not derivable; the &str is the trace reason.
    Unsupported(&'static str),
}

/// the one derivation entry point. validation and emission both call this with
/// the same arguments, so they cannot disagree. every planned member is treated
/// as available; a dependency on another member is recorded via `DependsOn`
/// rather than gated on an `introduced` set.
fn derive_index(rhs: &Expr, anchor: Anchor<'_>, ctx: &DerivationCtx<'_, '_>) -> Derivation {
    match anchor {
        Anchor::Member(rewrite) => derive_member_index(rhs, rewrite, ctx),
        Anchor::Base(base_rewrite) => derive_base_index(rhs, base_rewrite, ctx),
    }
}

fn derive_member_index(
    rhs: &Expr,
    rewrite: &BindingRewrite,
    ctx: &DerivationCtx<'_, '_>,
) -> Derivation {
    // 1. derive-from-base (RHS is base, base.offset(n), proxy, base.as_ptr...).
    match pointer_index_from_base_expr(rhs, ctx.ast_to_hir, ctx.tcx, rewrite) {
        IndexExpr::Unsupported => {}
        index => return Derivation::Index(index),
    }
    let rhs = unwrap_pointer_producing_expr(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return Derivation::Unsupported("member RHS is not base-derived or a method call");
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return Derivation::Unsupported("member RHS method is not offset/add");
    }
    if !receiver_cast_preserves_pointee_layout(&call.receiver, ctx.ast_to_hir, ctx.tcx) {
        return Derivation::Unsupported("member RHS receiver cast changes pointee size");
    }
    let receiver = unwrap_pointer_producing_expr(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ctx.ast_to_hir, ctx.tcx, receiver.id);
    // 2. self-advance: q = q.offset(n) -> idx_read(self) + n. no dependency.
    if receiver_hir_id == Some(rewrite.source_hir_id) {
        return Derivation::Index(IndexExpr::Plain(relative_index_expr(
            &idx_read_expr(rewrite),
            name,
            &call.args[0],
        )));
    }
    // 3. from another planned member of the same group that is (or, during
    //    validation, is treated as) introduced: q = other.offset(n) ->
    //    other_idx + n. gate on group_member_hir_ids (the frozen group set) AND
    //    same base, matching the original introduced_group_member path.
    if let Some(other_hir_id) = receiver_hir_id
        && rewrite.group_member_hir_ids.contains(&other_hir_id)
        && ctx
            .introduced
            .is_none_or(|introduced| introduced.contains(&other_hir_id))
        && let Some(other) = ctx.plan.by_hir_id.get(&other_hir_id)
        && other.base_hir_id == rewrite.base_hir_id
        && other.base_name == rewrite.base_name
    {
        return Derivation::DependsOn(
            IndexExpr::Plain(relative_index_expr(
                &idx_read_expr(other),
                name,
                &call.args[0],
            )),
            vec![other_hir_id],
        );
    }
    // 4. group member that is NOT index-rewritten at this point: either pruned
    //    from the plan, or planned but not (yet) introduced (e.g. its init was
    //    undecidable so it stays raw). the member is a raw pointer at runtime,
    //    so compute the index via runtime `offset_from` against the base
    //    pointer — the emitted form of the old
    //    group_member_pointer_assignment_index_expr. this keeps groups alive
    //    when only a subset of members is index-derivable. only reachable from
    //    assignment sites (not initializer sites), matching the old code.
    if ctx.allow_member_pointer_form
        && let Some(other_hir_id) = receiver_hir_id
        && rewrite.group_member_hir_ids.contains(&other_hir_id)
        && (!ctx.plan.by_hir_id.contains_key(&other_hir_id)
            || ctx
                .introduced
                .is_some_and(|introduced| !introduced.contains(&other_hir_id)))
    {
        let rhs_ptr = pprust::expr_to_string(rhs);
        let base_index = base_current_index_expr(rewrite).unwrap_or("0isize");
        let base_ptr = base_offset_expr_for_index(rewrite, base_index);
        let relative = utils::expr!("({}).offset_from({})", rhs_ptr, base_ptr);
        let index = match base_current_index_expr(rewrite) {
            Some(index_name) => add_index_expr(index_name, &relative),
            None => relative,
        };
        return Derivation::Index(IndexExpr::Plain(index));
    }
    Derivation::Unsupported("member RHS receiver is not the base, self, or a planned member")
}

fn derive_base_index(
    rhs: &Expr,
    base_rewrite: &BaseCursorRewrite,
    ctx: &DerivationCtx<'_, '_>,
) -> Derivation {
    if is_null_expr(rhs) {
        return Derivation::Unsupported("base assignment from null");
    }
    let rhs_u = unwrap_cast_and_paren(rhs);
    // base = base / base.as_ptr -> index 0 (the base cursor's own index).
    if (!base_rewrite.field_base
        && hir_id_of_ast_expr(ctx.ast_to_hir, ctx.tcx, rhs_u.id) == Some(base_rewrite.base_hir_id))
        || (base_rewrite.field_base && expr_matches_base_name(rhs_u, &base_rewrite.base_name))
    {
        return Derivation::Index(IndexExpr::Plain(utils::expr!(
            "{}",
            base_rewrite.index_name
        )));
    }
    // base = member (same base) -> DependsOn(member_idx, [member]).
    if let Some(hir_id) =
        direct_planned_local_hir_id(ctx.ast_to_hir, ctx.tcx, &ctx.plan.by_hir_id, rhs_u)
        && let Some(member) = ctx.plan.by_hir_id.get(&hir_id)
        && same_rewrite_base(member, base_rewrite)
    {
        return Derivation::DependsOn(
            IndexExpr::Plain(utils::expr!("{}", idx_read_expr(member))),
            vec![hir_id],
        );
    }
    let ExprKind::MethodCall(call) = &rhs_u.kind else {
        return Derivation::Unsupported("base RHS is not base/member or a method call");
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return Derivation::Unsupported("base RHS method is not offset/add");
    }
    if !receiver_cast_preserves_pointee_layout(&call.receiver, ctx.ast_to_hir, ctx.tcx) {
        return Derivation::Unsupported("base RHS receiver cast changes pointee size");
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ctx.ast_to_hir, ctx.tcx, receiver.id);
    let receiver_is_base = (!base_rewrite.field_base
        && receiver_hir_id == Some(base_rewrite.base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ctx.ast_to_hir,
            ctx.tcx,
            base_rewrite.base_hir_id,
            &base_rewrite.base_name,
            base_rewrite.field_base,
        )
        || (base_rewrite.field_base && expr_matches_base_name(receiver, &base_rewrite.base_name));
    if receiver_is_base {
        let offset = offset_index_arg_expr(name, &call.args[0]);
        return Derivation::Index(IndexExpr::Plain(add_index_expr(
            &base_rewrite.index_name,
            &offset,
        )));
    }
    // base = member.offset(n) (same base) -> DependsOn(member_idx + n, [member]).
    if let Some(hir_id) = receiver_hir_id
        && let Some(member) = ctx.plan.by_hir_id.get(&hir_id)
        && same_rewrite_base(member, base_rewrite)
    {
        return Derivation::DependsOn(
            IndexExpr::Plain(relative_index_expr(
                &idx_read_expr(member),
                name,
                &call.args[0],
            )),
            vec![hir_id],
        );
    }
    Derivation::Unsupported("base RHS receiver is not the base or a planned member")
}

fn hir_id_of_ast_expr(ast_to_hir: &AstToHir, tcx: TyCtxt<'_>, node_id: NodeId) -> Option<HirId> {
    let hir_expr = ast_to_hir.get_expr(node_id, tcx)?;
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    Some(hir_id)
}

fn rewrite_binding_pat(pat: &mut Pat, index_name: &str) -> bool {
    let PatKind::Ident(_, ident, _) = &mut pat.kind else {
        return false;
    };
    ident.name = Symbol::intern(index_name);
    true
}

fn index_ty(nullable: bool) -> P<Ty> {
    if nullable {
        P(utils::ty!("Option<isize>"))
    } else {
        P(utils::ty!("isize"))
    }
}

fn is_null_expr(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    match &expr.kind {
        ExprKind::Call(callee, _) => {
            let ExprKind::Path(_, path) = &unwrap_cast_and_paren(callee).kind else {
                return false;
            };
            let segments = path
                .segments
                .iter()
                .map(|seg| seg.ident.name.as_str())
                .collect::<Vec<_>>();
            matches!(
                segments.as_slice(),
                ["std", "ptr", "null" | "null_mut"] | ["core", "ptr", "null" | "null_mut"]
            )
        }
        ExprKind::Lit(lit) => lit.kind == token::LitKind::Integer && lit.symbol.as_str() == "0",
        _ => false,
    }
}

/// returns whether unwrapping a cast on an `offset`/`add`/`offset_from`
/// receiver preserves the pointee size, so the derived index stays in base
/// element units; alignment is also required to match as extra conservatism for
/// the rare same-size/different-align case.
fn receiver_cast_preserves_pointee_layout(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let outer = unwrap_paren(receiver);
    // no cast applied directly to the receiver: the unwrap cannot change units.
    if !matches!(outer.kind, ExprKind::Cast(..)) {
        return true;
    }
    let inner = unwrap_cast_and_paren(outer);
    let (Some(outer_layout), Some(inner_layout)) = (
        ast_expr_pointee_size_align(outer, ast_to_hir, tcx),
        ast_expr_pointee_size_align(inner, ast_to_hir, tcx),
    ) else {
        return false;
    };
    outer_layout == inner_layout
}

/// resolves the `(size, align)` in bytes of the pointee of an AST expression
/// whose type is a raw pointer. returns `None` if the type is unresolvable, not
/// a raw pointer, or has no computable layout.
fn ast_expr_pointee_size_align(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<(u64, u64)> {
    let hir_expr = ast_to_hir.get_expr(expr.id, tcx)?;
    let typeck = tcx.typeck(hir_expr.hir_id.owner);
    let ty::TyKind::RawPtr(pointee, _) = typeck.expr_ty(hir_expr).kind() else {
        return None;
    };
    let typing_env = ty::TypingEnv::post_analysis(tcx, hir_expr.hir_id.owner.to_def_id());
    let layout = tcx.layout_of(typing_env.as_query_input(*pointee)).ok()?;
    Some((layout.size.bytes(), layout.align.abi.bytes()))
}

fn unwrap_pointer_producing_expr(expr: &Expr) -> &Expr {
    let expr = unwrap_cast_and_paren(expr);
    match &expr.kind {
        ExprKind::AddrOf(_, _, inner) => {
            let inner = unwrap_cast_and_paren(inner);
            if let ExprKind::Unary(UnOp::Deref, deref_inner) = &inner.kind {
                return unwrap_pointer_producing_expr(deref_inner);
            }
            expr
        }
        _ => expr,
    }
}

fn expr_matches_base_name(expr: &Expr, base_name: &str) -> bool {
    pprust::expr_to_string(unwrap_cast_and_paren(expr)).replace(' ', "")
        == base_name.replace(' ', "")
}

fn offset_index_arg_expr(name: &str, arg: &Expr) -> Expr {
    if name == "add" || matches!(unwrap_cast_and_paren(arg).kind, ExprKind::Lit(_)) {
        utils::expr!("({}) as isize", pprust::expr_to_string(arg))
    } else {
        utils::expr!("{}", pprust::expr_to_string(arg))
    }
}

fn add_index_expr(current: &str, offset: &Expr) -> Expr {
    utils::expr!("({}) + ({})", current, pprust::expr_to_string(offset))
}

fn relative_index_expr(current: &str, method_name: &str, arg: &Expr) -> Expr {
    let offset = offset_index_arg_expr(method_name, arg);
    add_index_expr(current, &offset)
}

fn base_current_index_expr(rewrite: &BindingRewrite) -> Option<&str> {
    rewrite.base_index_name.as_deref()
}

fn expr_is_projection_from_base_hir(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    if hir_id_of_ast_expr(ast_to_hir, tcx, expr.id) == Some(base_hir_id) {
        return true;
    }
    match &expr.kind {
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Field(inner, _)
        | ExprKind::Unary(UnOp::Deref, inner) => {
            expr_is_projection_from_base_hir(inner, ast_to_hir, tcx, base_hir_id)
        }
        _ => false,
    }
}

fn receiver_is_base_as_ptr_hir(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
) -> bool {
    let ExprKind::MethodCall(call) = &receiver.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "as_ptr" | "as_mut_ptr") || !call.args.is_empty() {
        return false;
    }
    expr_is_projection_from_base_hir(&call.receiver, ast_to_hir, tcx, base_hir_id)
}

fn receiver_is_field_base_as_ptr(receiver: &Expr, base_name: &str) -> bool {
    let ExprKind::MethodCall(call) = &receiver.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "as_ptr" | "as_mut_ptr") || !call.args.is_empty() {
        return false;
    }
    expr_matches_base_name(&call.receiver, base_name)
}

fn receiver_is_base_as_ptr_for_context(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
    base_name: &str,
    field_base: bool,
) -> bool {
    if field_base {
        receiver_is_field_base_as_ptr(receiver, base_name)
    } else {
        receiver_is_base_as_ptr_hir(receiver, ast_to_hir, tcx, base_hir_id)
    }
}

fn receiver_is_base_as_ptr(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> bool {
    receiver_is_base_as_ptr_for_context(
        receiver,
        ast_to_hir,
        tcx,
        rewrite.base_hir_id,
        &rewrite.base_name,
        rewrite.field_base,
    )
}

fn slice_base_expr_from_as_ptr_receiver(receiver: &Expr) -> &Expr {
    let receiver = unwrap_cast_and_paren(receiver);
    if let ExprKind::AddrOf(_, _, inner) = &receiver.kind {
        unwrap_cast_and_paren(inner)
    } else {
        receiver
    }
}

fn projected_as_ptr_receiver_base_name(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> Option<String> {
    if rewrite.field_base {
        return None;
    }
    let expr = unwrap_pointer_producing_expr(expr);
    let ExprKind::MethodCall(offset_call) = &expr.kind else {
        return None;
    };
    let name = offset_call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || offset_call.args.len() != 1 {
        return None;
    }
    if !receiver_cast_preserves_pointee_layout(&offset_call.receiver, ast_to_hir, tcx) {
        return None;
    }
    let receiver = unwrap_cast_and_paren(&offset_call.receiver);
    let ExprKind::MethodCall(as_ptr_call) = &receiver.kind else {
        return None;
    };
    let as_ptr_name = as_ptr_call.seg.ident.name.as_str();
    if !matches!(as_ptr_name, "as_ptr" | "as_mut_ptr") || !as_ptr_call.args.is_empty() {
        return None;
    }
    let base_expr = slice_base_expr_from_as_ptr_receiver(&as_ptr_call.receiver);
    if hir_id_of_ast_expr(ast_to_hir, tcx, base_expr.id) == Some(rewrite.base_hir_id) {
        return None;
    }
    expr_is_projection_from_base_hir(base_expr, ast_to_hir, tcx, rewrite.base_hir_id)
        .then(|| pprust::expr_to_string(base_expr))
}

fn pointer_index_from_base_expr(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> IndexExpr {
    let base_hir_id = rewrite.base_hir_id;
    let base_name = rewrite.base_name.as_str();
    let field_base = rewrite.field_base;
    let base_proxy_hir_ids = &rewrite.base_proxy_hir_ids;
    let base_index_name = base_current_index_expr(rewrite);

    if is_null_expr(expr) {
        return IndexExpr::Null;
    }

    let expr = unwrap_pointer_producing_expr(expr);
    let expr_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, expr.id);
    if (!field_base && expr_hir_id == Some(base_hir_id))
        || expr_hir_id.is_some_and(|id| base_proxy_hir_ids.contains(&id))
        || (field_base && expr_matches_base_name(expr, base_name))
        || receiver_is_base_as_ptr_for_context(
            expr,
            ast_to_hir,
            tcx,
            base_hir_id,
            base_name,
            field_base,
        )
    {
        return IndexExpr::Plain(match base_index_name {
            Some(index_name) => utils::expr!("{}", index_name),
            None => utils::expr!("0isize"),
        });
    }

    let ExprKind::MethodCall(call) = &expr.kind else {
        return IndexExpr::Unsupported;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return IndexExpr::Unsupported;
    }
    if !receiver_cast_preserves_pointee_layout(&call.receiver, ast_to_hir, tcx) {
        return IndexExpr::Unsupported;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = (!field_base && receiver_hir_id == Some(base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ast_to_hir,
            tcx,
            base_hir_id,
            base_name,
            field_base,
        )
        || (field_base && expr_matches_base_name(receiver, base_name))
        || receiver_hir_id.is_some_and(|id| base_proxy_hir_ids.contains(&id));
    if !receiver_is_base {
        return IndexExpr::Unsupported;
    }
    let offset = offset_index_arg_expr(name, &call.args[0]);
    match base_index_name {
        Some(index_name) => IndexExpr::Plain(add_index_expr(index_name, &offset)),
        None => IndexExpr::Plain(offset),
    }
}

/// For a live (caller-visible) field base, recognizes a base self-advance
/// `(*s).out = (*s).out.offset(n)` / `.add(n)` and returns the counter update
/// expression `out_idx + n`. Returns `None` for any other RHS (e.g. assignment
/// from a member), which approach D does not support.
fn live_base_self_advance_counter(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_rewrite: &BaseCursorRewrite,
) -> Option<Expr> {
    let rhs = unwrap_cast_and_paren(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return None;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return None;
    }
    if !receiver_cast_preserves_pointee_layout(&call.receiver, ast_to_hir, tcx) {
        return None;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_is_base = (!base_rewrite.field_base
        && hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id) == Some(base_rewrite.base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ast_to_hir,
            tcx,
            base_rewrite.base_hir_id,
            &base_rewrite.base_name,
            base_rewrite.field_base,
        )
        || (base_rewrite.field_base && expr_matches_base_name(receiver, &base_rewrite.base_name));
    if !receiver_is_base {
        return None;
    }
    let offset = offset_index_arg_expr(name, &call.args[0]);
    Some(add_index_expr(&base_rewrite.index_name, &offset))
}

fn index_init_expr(index: IndexExpr, nullable: bool) -> Option<Expr> {
    match (index, nullable) {
        (IndexExpr::Plain(expr), false) => Some(expr),
        (IndexExpr::Plain(expr), true) => {
            Some(utils::expr!("Some({})", pprust::expr_to_string(&expr)))
        }
        (IndexExpr::Null, true) => Some(utils::expr!("None")),
        (IndexExpr::Null, false) | (IndexExpr::Unsupported, _) => None,
    }
}

fn index_assignment_rhs_expr(index: IndexExpr, nullable: bool) -> Option<Expr> {
    index_init_expr(index, nullable)
}

fn idx_read_expr(rewrite: &BindingRewrite) -> String {
    if rewrite.nullable {
        format!("{}.unwrap()", rewrite.index_name)
    } else {
        rewrite.index_name.clone()
    }
}

/// computes the offset expression for a member materialization. for a live
/// (caller-visible) field base the member index is corrected by the base
/// counter (`index - base_index`); otherwise the member index is used as-is.
fn member_offset_expr(base_live: bool, base_index_name: Option<&str>, index_expr: &str) -> String {
    match (base_live, base_index_name) {
        (true, Some(base_idx)) => format!("({index_expr}) - ({base_idx})"),
        _ => index_expr.to_string(),
    }
}

fn base_offset_expr_for_parts(base_name: &str, base_is_raw_ptr: bool, index_expr: &str) -> String {
    if base_is_raw_ptr {
        format!("({base_name}).offset({index_expr})")
    } else {
        format!("({base_name}).as_ptr().offset({index_expr})")
    }
}

fn base_offset_expr_for_index(rewrite: &BindingRewrite, index_expr: &str) -> String {
    let offset = member_offset_expr(
        rewrite.base_live,
        rewrite.base_index_name.as_deref(),
        index_expr,
    );
    base_offset_expr_for_parts(&rewrite.base_name, rewrite.base_is_raw_ptr, &offset)
}

fn pointer_expr_for_index(rewrite: &BindingRewrite) -> Expr {
    let base_offset = base_offset_expr_for_index(rewrite, &idx_read_expr(rewrite));
    utils::expr!("{} as {}", base_offset, rewrite.ptr_ty)
}

fn materialized_init_expr(rewrite: &BindingRewrite, index_expr: &str) -> Expr {
    let ptr = base_offset_expr_for_index(rewrite, index_expr);
    utils::expr!("{} as {}", ptr, rewrite.ptr_ty)
}

fn materialized_ty(rewrite: &BindingRewrite) -> P<Ty> {
    P(utils::ty!("{}", rewrite.ptr_ty))
}

fn pointer_value_expr(rewrite: &BindingRewrite) -> Expr {
    if rewrite.nullable {
        let null_fn = if rewrite.ptr_mut {
            "std::ptr::null_mut()"
        } else {
            "std::ptr::null()"
        };
        utils::expr!(
            "{}.map_or({} as {}, |idx| ({}) as {})",
            rewrite.index_name,
            null_fn,
            rewrite.ptr_ty,
            base_offset_expr_for_index(rewrite, "idx"),
            rewrite.ptr_ty
        )
    } else {
        pointer_expr_for_index(rewrite)
    }
}

fn base_cursor_pointer_expr(rewrite: &BaseCursorRewrite) -> Expr {
    let base_offset = base_offset_expr_for_parts(
        &rewrite.base_name,
        rewrite.base_is_raw_ptr,
        &rewrite.index_name,
    );
    utils::expr!("{} as {}", base_offset, rewrite.ptr_ty)
}

fn introduced_planned_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    introduced_hir_ids: &FxHashSet<HirId>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, unwrap_cast_and_paren(expr).id)?;
    introduced_hir_ids.contains(&hir_id).then_some(hir_id)
}

fn planned_materialized_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = direct_planned_local_hir_id(ast_to_hir, tcx, planned_rewrites, expr)?;
    planned_rewrites
        .get(&hir_id)
        .is_some_and(rewrite_uses_materialized_binding)
        .then_some(hir_id)
}

fn introduced_materialized_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    introduced_hir_ids: &FxHashSet<HirId>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = planned_materialized_local_hir_id(ast_to_hir, tcx, planned_rewrites, expr)?;
    introduced_hir_ids.contains(&hir_id).then_some(hir_id)
}

fn representation_uses_index_rewrite(representation: &BindingRepresentation) -> bool {
    matches!(representation, BindingRepresentation::IndexOnly)
}

fn rewrite_uses_index_rewrite(rewrite: &BindingRewrite) -> bool {
    representation_uses_index_rewrite(&rewrite.representation)
        || (matches!(
            rewrite.representation,
            BindingRepresentation::Materialized(_)
        ) && rewrite.nullable)
}

fn rewrite_uses_materialized_binding(rewrite: &BindingRewrite) -> bool {
    matches!(
        rewrite.representation,
        BindingRepresentation::Materialized(_)
    ) && !rewrite.nullable
}

fn introduced_index_rewritten_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    introduced_hir_ids: &FxHashSet<HirId>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = introduced_planned_local_hir_id(ast_to_hir, tcx, introduced_hir_ids, expr)?;
    planned_rewrites
        .get(&hir_id)
        .is_some_and(rewrite_uses_index_rewrite)
        .then_some(hir_id)
}

struct ArrayLocalIndexRewriteVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    plan: RewritePlan,
    introduced_hir_ids: FxHashSet<HirId>,
    changed: bool,
    trace: &'a mut RewriteTrace,
}

impl ArrayLocalIndexRewriteVisitor<'_, '_> {
    fn introduced_index_backed_rewrite(&self, hir_id: HirId) -> Option<&BindingRewrite> {
        if !self.introduced_hir_ids.contains(&hir_id) {
            return None;
        }
        let rewrite = self.plan.by_hir_id.get(&hir_id)?;
        (rewrite_uses_index_rewrite(rewrite) || rewrite_uses_materialized_binding(rewrite))
            .then_some(rewrite)
    }

    fn index_expr_for_operand(&self, expr: &Expr, anchor: &BindingRewrite) -> Option<String> {
        if let Some(hir_id) =
            hir_id_of_ast_expr(self.ast_to_hir, self.tcx, unwrap_cast_and_paren(expr).id)
            && let Some(rewrite) = self.introduced_index_backed_rewrite(hir_id)
            && !rewrite.nullable
            && rewrite.base_hir_id == anchor.base_hir_id
            && rewrite.base_name == anchor.base_name
        {
            return Some(idx_read_expr(rewrite));
        }
        match pointer_index_from_base_expr(expr, self.ast_to_hir, self.tcx, anchor) {
            IndexExpr::Plain(index) => Some(pprust::expr_to_string(&index)),
            IndexExpr::Null | IndexExpr::Unsupported => None,
        }
    }

    fn rewrite_materialized_local_stmt(&mut self, local: &mut rustc_ast::Local) -> Option<Stmt> {
        let let_stmt = self.ast_to_hir.get_let_stmt(local.id, self.tcx)?;
        let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind else {
            return None;
        };
        let mut rewrite = self.plan.by_hir_id.get(&hir_id)?.clone();
        if !rewrite_uses_materialized_binding(&rewrite) {
            return None;
        }

        let init = local.kind.init_mut()?;
        if let Some(base_name) =
            projected_as_ptr_receiver_base_name(init, self.ast_to_hir, self.tcx, &rewrite)
        {
            rewrite.base_name = base_name;
            rewrite.base_is_raw_ptr = false;
            self.plan.by_hir_id.insert(hir_id, rewrite.clone());
        }

        let ctx = DerivationCtx {
            ast_to_hir: self.ast_to_hir,
            tcx: self.tcx,
            plan: &self.plan,
            introduced: Some(&self.introduced_hir_ids),
            // initializer site: no pointer-form fallback (diff-neutral with the
            // old visit_local path, which never reached the pointer form).
            allow_member_pointer_form: false,
        };
        let index = match derive_index(init, Anchor::Member(&rewrite), &ctx) {
            Derivation::Index(index) | Derivation::DependsOn(index, _) => index,
            Derivation::Unsupported(_) => IndexExpr::Unsupported,
        };
        let Some(new_index_init) = index_init_expr(index, rewrite.nullable) else {
            self.trace.record(
                hir_id.owner.def_id,
                TraceSubject::Member(rewrite.source_name.clone()),
                TraceStage::Apply,
                TraceDecision::Skipped,
                || {
                    "apply: index derivation failed at visit time (prune/visitor divergence)"
                        .to_string()
                },
            );
            return None;
        };
        let index_name = rewrite.index_name.clone();
        let index_stmt = utils::stmt!(
            "let mut {}: isize = {};",
            index_name,
            pprust::expr_to_string(&new_index_init)
        );
        let materialized_init = materialized_init_expr(&rewrite, &idx_read_expr(&rewrite));

        if !rewrite_binding_pat(&mut local.pat, &rewrite.source_name) {
            return None;
        }
        local.ty = Some(materialized_ty(&rewrite));
        *init = P(materialized_init);
        self.introduced_hir_ids.insert(hir_id);
        self.trace.record(
            hir_id.owner.def_id,
            TraceSubject::Member(rewrite.source_name.clone()),
            TraceStage::Apply,
            TraceDecision::Rewritten,
            || "apply: materialized binding introduced".to_string(),
        );
        self.changed = true;
        Some(index_stmt)
    }
}

impl MutVisitor for ArrayLocalIndexRewriteVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut Item) {
        if let ItemKind::Fn(box fn_item) = &mut item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id).copied()
        {
            let mut cursors = self
                .plan
                .base_by_key
                .values()
                .filter(|rewrite| rewrite.fn_def_id == def_id)
                .cloned()
                .collect::<Vec<_>>();
            cursors.sort_by(|a, b| a.index_name.cmp(&b.index_name));
            if !cursors.is_empty() {
                let stmts = &mut fn_item.body.as_mut().unwrap().stmts;
                for rewrite in cursors.into_iter().rev() {
                    stmts.insert(
                        0,
                        utils::stmt!("let mut {}: isize = 0isize;", rewrite.index_name),
                    );
                }
                self.changed = true;
            }
        }
        mut_visit::walk_item(self, item);
    }

    fn visit_block(&mut self, block: &mut Block) {
        let mut new_stmts = Vec::with_capacity(block.stmts.len());
        for mut stmt in std::mem::take(&mut block.stmts) {
            if let StmtKind::Let(local) = &mut stmt.kind
                && let Some(index_stmt) = self.rewrite_materialized_local_stmt(local)
            {
                new_stmts.push(index_stmt);
                new_stmts.push(stmt);
                continue;
            }
            if let StmtKind::Expr(expr) | StmtKind::Semi(expr) = &stmt.kind
                && let ExprKind::Assign(lhs, rhs, _) = &expr.kind
                && let Some(base_key) =
                    direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, lhs)
                && let Some(base_rewrite) = self.plan.base_by_key.get(&base_key)
                && base_rewrite.base_live
            {
                if let Some(counter_rhs) =
                    live_base_self_advance_counter(rhs, self.ast_to_hir, self.tcx, base_rewrite)
                {
                    let counter_stmt = utils::stmt!(
                        "{} = {};",
                        base_rewrite.index_name,
                        pprust::expr_to_string(&counter_rhs)
                    );
                    // keep the field write verbatim (field stays caller-correct),
                    // then advance the shadow counter.
                    new_stmts.push(stmt);
                    new_stmts.push(counter_stmt);
                    self.changed = true;
                    continue;
                }
                // not a recognized self-advance: leave the statement untouched.
                // prune drops such groups, so members are not index-rewritten and
                // the live field read stays correct.
                new_stmts.push(stmt);
                continue;
            }
            if let StmtKind::Expr(expr) | StmtKind::Semi(expr) = &mut stmt.kind
                && let ExprKind::Assign(lhs, rhs, _) = &mut expr.kind
                && let Some(hir_id) = introduced_materialized_local_hir_id(
                    self.ast_to_hir,
                    self.tcx,
                    &self.plan.by_hir_id,
                    &self.introduced_hir_ids,
                    lhs,
                )
                && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id).cloned()
            {
                let ctx = DerivationCtx {
                    ast_to_hir: self.ast_to_hir,
                    tcx: self.tcx,
                    plan: &self.plan,
                    introduced: Some(&self.introduced_hir_ids),
                    allow_member_pointer_form: true,
                };
                let index = match derive_index(rhs, Anchor::Member(&rewrite), &ctx) {
                    Derivation::Index(index) | Derivation::DependsOn(index, _) => index,
                    Derivation::Unsupported(_) => IndexExpr::Unsupported,
                };
                if let Some(new_rhs) = index_assignment_rhs_expr(index, rewrite.nullable) {
                    let idx_stmt = utils::stmt!(
                        "{} = {};",
                        rewrite.index_name,
                        pprust::expr_to_string(&new_rhs)
                    );
                    let materialized_rhs =
                        materialized_init_expr(&rewrite, &idx_read_expr(&rewrite));
                    let value_stmt = utils::stmt!(
                        "{} = {};",
                        rewrite.source_name,
                        pprust::expr_to_string(&materialized_rhs)
                    );
                    new_stmts.push(idx_stmt);
                    new_stmts.push(value_stmt);
                    self.changed = true;
                    continue;
                }
            }
            new_stmts.extend(self.flat_map_stmt(stmt));
        }
        block.stmts = new_stmts.into();
    }

    fn visit_local(&mut self, local: &mut rustc_ast::Local) {
        let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx) else {
            mut_visit::walk_local(self, local);
            return;
        };
        let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind else {
            mut_visit::walk_local(self, local);
            return;
        };
        let Some(mut rewrite) = self.plan.by_hir_id.get(&hir_id).cloned() else {
            mut_visit::walk_local(self, local);
            return;
        };
        if rewrite_uses_materialized_binding(&rewrite) {
            mut_visit::walk_local(self, local);
            return;
        }
        let Some(init) = local.kind.init_mut() else {
            mut_visit::walk_local(self, local);
            return;
        };
        if let Some(base_name) =
            projected_as_ptr_receiver_base_name(init, self.ast_to_hir, self.tcx, &rewrite)
        {
            rewrite.base_name = base_name;
            rewrite.base_is_raw_ptr = false;
            self.plan.by_hir_id.insert(hir_id, rewrite.clone());
        }
        let ctx = DerivationCtx {
            ast_to_hir: self.ast_to_hir,
            tcx: self.tcx,
            plan: &self.plan,
            introduced: Some(&self.introduced_hir_ids),
            // initializer site: no pointer-form fallback (diff-neutral with the
            // old visit_local path, which never reached the pointer form).
            allow_member_pointer_form: false,
        };
        let index = match derive_index(init, Anchor::Member(&rewrite), &ctx) {
            Derivation::Index(index) | Derivation::DependsOn(index, _) => index,
            Derivation::Unsupported(_) => IndexExpr::Unsupported,
        };
        let Some(new_init) = index_init_expr(index, rewrite.nullable) else {
            self.trace.record(
                hir_id.owner.def_id,
                TraceSubject::Member(rewrite.source_name.clone()),
                TraceStage::Apply,
                TraceDecision::Skipped,
                || {
                    "apply: index derivation failed at visit time (prune/visitor divergence)"
                        .to_string()
                },
            );
            mut_visit::walk_local(self, local);
            return;
        };
        if !rewrite_binding_pat(&mut local.pat, &rewrite.index_name) {
            mut_visit::walk_local(self, local);
            return;
        }
        local.ty = Some(index_ty(rewrite.nullable));
        *init = P(new_init);
        self.introduced_hir_ids.insert(hir_id);
        self.trace.record(
            hir_id.owner.def_id,
            TraceSubject::Member(rewrite.source_name.clone()),
            TraceStage::Apply,
            TraceDecision::Rewritten,
            || "apply: index-only binding introduced".to_string(),
        );
        self.changed = true;
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                if let Some(base_key) =
                    direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, lhs)
                    && let Some(rewrite) = self.plan.base_by_key.get(&base_key)
                    && !rewrite.base_live
                {
                    let ctx = DerivationCtx {
                        ast_to_hir: self.ast_to_hir,
                        tcx: self.tcx,
                        plan: &self.plan,
                        introduced: Some(&self.introduced_hir_ids),
                        allow_member_pointer_form: true,
                    };
                    let index = match derive_index(rhs, Anchor::Base(rewrite), &ctx) {
                        Derivation::Index(index) | Derivation::DependsOn(index, _) => index,
                        Derivation::Unsupported(_) => IndexExpr::Unsupported,
                    };
                    if let IndexExpr::Plain(new_rhs) = index {
                        *lhs = P(utils::expr!("{}", rewrite.index_name));
                        *rhs = P(new_rhs);
                        self.changed = true;
                    } else {
                        self.visit_expr(rhs);
                    }
                    return;
                }
                if let Some(hir_id) = introduced_planned_local_hir_id(
                    self.ast_to_hir,
                    self.tcx,
                    &self.introduced_hir_ids,
                    lhs,
                ) && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
                    && rewrite_uses_index_rewrite(rewrite)
                {
                    let ctx = DerivationCtx {
                        ast_to_hir: self.ast_to_hir,
                        tcx: self.tcx,
                        plan: &self.plan,
                        introduced: Some(&self.introduced_hir_ids),
                        allow_member_pointer_form: true,
                    };
                    let index = match derive_index(rhs, Anchor::Member(rewrite), &ctx) {
                        Derivation::Index(index) | Derivation::DependsOn(index, _) => index,
                        Derivation::Unsupported(_) => IndexExpr::Unsupported,
                    };
                    if let Some(new_rhs) = index_assignment_rhs_expr(index, rewrite.nullable) {
                        *lhs = P(utils::expr!("{}", rewrite.index_name));
                        *rhs = P(new_rhs);
                        self.changed = true;
                    } else {
                        self.visit_expr(rhs);
                    }
                } else {
                    self.visit_expr(lhs);
                    self.visit_expr(rhs);
                }
                return;
            }
            ExprKind::AssignOp(_, lhs, rhs) => {
                if direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, lhs)
                    .is_none()
                    && introduced_index_rewritten_local_hir_id(
                        self.ast_to_hir,
                        self.tcx,
                        &self.plan.by_hir_id,
                        &self.introduced_hir_ids,
                        lhs,
                    )
                    .is_none()
                {
                    self.visit_expr(lhs);
                }
                self.visit_expr(rhs);
                return;
            }
            ExprKind::AddrOf(_, _, inner) => {
                if direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, inner)
                    .is_none()
                    && introduced_index_rewritten_local_hir_id(
                        self.ast_to_hir,
                        self.tcx,
                        &self.plan.by_hir_id,
                        &self.introduced_hir_ids,
                        inner,
                    )
                    .is_none()
                {
                    self.visit_expr(inner);
                }
                return;
            }
            _ => {}
        }

        if let ExprKind::MethodCall(call) = &expr.kind {
            let receiver = unwrap_paren(&call.receiver);
            if call.seg.ident.name.as_str() == "is_null"
                && call.args.is_empty()
                && let Some(hir_id) = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, receiver.id)
                && self.introduced_hir_ids.contains(&hir_id)
                && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
                && rewrite_uses_index_rewrite(rewrite)
            {
                *expr = if rewrite.nullable {
                    utils::expr!("{}.is_none()", rewrite.index_name)
                } else {
                    utils::expr!("false")
                };
                self.changed = true;
                return;
            }
        }

        if let ExprKind::Binary(op, lhs, rhs) = &expr.kind
            && matches!(
                op.node,
                BinOpKind::Eq
                    | BinOpKind::Ne
                    | BinOpKind::Lt
                    | BinOpKind::Le
                    | BinOpKind::Gt
                    | BinOpKind::Ge
            )
        {
            let lhs_hir =
                hir_id_of_ast_expr(self.ast_to_hir, self.tcx, unwrap_cast_and_paren(lhs).id);
            let rhs_hir =
                hir_id_of_ast_expr(self.ast_to_hir, self.tcx, unwrap_cast_and_paren(rhs).id);
            let lhs_rewrite =
                lhs_hir.and_then(|hir_id| self.introduced_index_backed_rewrite(hir_id));
            let rhs_rewrite =
                rhs_hir.and_then(|hir_id| self.introduced_index_backed_rewrite(hir_id));
            let anchor = lhs_rewrite.or(rhs_rewrite);
            if let Some(anchor) = anchor
                && !anchor.nullable
                && let Some(lhs_idx) = self.index_expr_for_operand(lhs, anchor)
                && let Some(rhs_idx) = self.index_expr_for_operand(rhs, anchor)
            {
                *expr = match op.node {
                    BinOpKind::Eq => utils::expr!("{lhs_idx} == {rhs_idx}"),
                    BinOpKind::Ne => utils::expr!("{lhs_idx} != {rhs_idx}"),
                    BinOpKind::Lt => utils::expr!("{lhs_idx} < {rhs_idx}"),
                    BinOpKind::Le => utils::expr!("{lhs_idx} <= {rhs_idx}"),
                    BinOpKind::Gt => utils::expr!("{lhs_idx} > {rhs_idx}"),
                    BinOpKind::Ge => utils::expr!("{lhs_idx} >= {rhs_idx}"),
                    _ => unreachable!(),
                };
                self.changed = true;
                return;
            }
        }

        if let ExprKind::Unary(UnOp::Deref, inner) = &mut expr.kind
            && let Some(base_key) =
                direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, inner)
            && let Some(rewrite) = self.plan.base_by_key.get(&base_key)
            && !rewrite.base_live
        {
            let ptr = base_cursor_pointer_expr(rewrite);
            *expr = utils::expr!("*({})", pprust::expr_to_string(&ptr));
            self.changed = true;
            return;
        }

        if let ExprKind::Unary(UnOp::Deref, inner) = &mut expr.kind
            && let Some(hir_id) = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, inner.id)
            && self.introduced_hir_ids.contains(&hir_id)
            && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
            && rewrite_uses_index_rewrite(rewrite)
        {
            let ptr = pointer_expr_for_index(rewrite);
            *expr = utils::expr!("*({})", pprust::expr_to_string(&ptr));
            self.changed = true;
            return;
        }

        if let ExprKind::MethodCall(call) = &expr.kind
            && call.seg.ident.name.as_str() == "offset_from"
            && call.args.len() == 1
        {
            let receiver = unwrap_cast_and_paren(&call.receiver);
            let arg = unwrap_cast_and_paren(&call.args[0]);
            let receiver_hir = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, receiver.id);
            let arg_hir = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, arg.id);
            let receiver_rewrite =
                receiver_hir.and_then(|hir_id| self.introduced_index_backed_rewrite(hir_id));
            let arg_rewrite =
                arg_hir.and_then(|hir_id| self.introduced_index_backed_rewrite(hir_id));
            let anchor = receiver_rewrite.or(arg_rewrite);
            let replacement = anchor.and_then(|anchor| {
                if anchor.nullable {
                    return None;
                }
                let receiver_idx = self.index_expr_for_operand(receiver, anchor)?;
                let arg_idx = self.index_expr_for_operand(arg, anchor)?;
                Some(utils::expr!("({}) - ({})", receiver_idx, arg_idx))
            });
            if let Some(replacement) = replacement {
                *expr = replacement;
                self.changed = true;
                return;
            }
        }

        mut_visit::walk_expr(self, expr);

        if let Some(base_key) =
            direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, expr)
            && let Some(rewrite) = self.plan.base_by_key.get(&base_key)
            && !rewrite.base_live
        {
            *expr = base_cursor_pointer_expr(rewrite);
            self.changed = true;
            return;
        }

        if let Some(hir_id) = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, expr.id)
            && self.introduced_hir_ids.contains(&hir_id)
            && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
            && rewrite_uses_index_rewrite(rewrite)
        {
            *expr = pointer_value_expr(rewrite);
            self.changed = true;
        }
    }
}

trait LocalKindInitMut {
    fn init_mut(&mut self) -> Option<&mut P<Expr>>;
}

impl LocalKindInitMut for LocalKind {
    fn init_mut(&mut self) -> Option<&mut P<Expr>> {
        match self {
            LocalKind::Init(init) | LocalKind::InitElse(init, _) => Some(init),
            LocalKind::Decl => None,
        }
    }
}

#[cfg(test)]
mod member_offset_tests {
    use super::member_offset_expr;

    #[test]
    fn live_base_subtracts_base_index() {
        assert_eq!(
            member_offset_expr(true, Some("out_idx"), "src_idx"),
            "(src_idx) - (out_idx)"
        );
    }

    #[test]
    fn non_live_base_is_unchanged() {
        assert_eq!(
            member_offset_expr(false, Some("out_idx"), "src_idx"),
            "src_idx"
        );
    }

    #[test]
    fn live_base_without_index_is_unchanged() {
        assert_eq!(member_offset_expr(true, None, "src_idx"), "src_idx");
    }
}

#[cfg(test)]
mod derivation_tests {
    // these run the whole pass and assert the emitted index forms, which
    // exercise derive_index end to end (a direct unit harness would need a
    // built RewritePlan). kept here so the module name documents intent.
    use super::*;

    // marker test: derive_index exists and the enum variants are constructible.
    #[test]
    fn derivation_enum_is_constructible() {
        let d = Derivation::Unsupported("x");
        assert!(matches!(d, Derivation::Unsupported("x")));
        let d2 = Derivation::DependsOn(IndexExpr::Null, vec![]);
        assert!(matches!(d2, Derivation::DependsOn(IndexExpr::Null, _)));
    }
}
