use rustc_hash::FxHashSet;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::Local;

use super::{
    PointerFlowResult,
    collector::analyze_body_with_summaries,
    field_access::{FieldAccess, FieldAccessKind, FieldAccessReject, FieldAccessRejectKind},
    graph::BaseId,
    pointer_flow_analysis,
};
use crate::utils::rustc::RustProgram;

// local copy of the array_local_provenance test helper; test modules cannot
// import each other's private items
fn build_rust_program(tcx: rustc_middle::ty::TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    let mut structs = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn analyze_single(code: &str, fn_name: &str) -> PointerFlowResult {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let did = program
            .functions
            .iter()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == fn_name)
            .unwrap_or_else(|| panic!("missing function {fn_name}"));
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        analyze_body_with_summaries(tcx, did, &body, &FxHashSet::default(), None)
    })
    .unwrap()
}

fn analyze_interprocedural(code: &str, fn_name: &str) -> PointerFlowResult {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let results = pointer_flow_analysis(&program, &FxHashSet::default());
        let did = program
            .functions
            .iter()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == fn_name)
            .unwrap_or_else(|| panic!("missing function {fn_name}"));
        results.get(&did).cloned().expect("missing analysis result")
    })
    .unwrap()
}

fn param_base(result: &PointerFlowResult, param_index: usize) -> BaseId {
    let local = Local::from_usize(param_index + 1);
    let slot = result
        .slot_table
        .local_head_slot(local)
        .expect("param has no pointer slot");
    BaseId::Param { local, slot }
}

fn accesses_reaching_param(result: &PointerFlowResult, param_index: usize) -> Vec<FieldAccess> {
    let base = param_base(result, param_index);
    result
        .field_accesses
        .iter()
        .filter(|access| {
            result
                .provenance
                .reachable_bases
                .get(&access.node)
                .is_some_and(|bases| bases.contains(&base))
        })
        .cloned()
        .collect()
}

fn rejects_reaching_param(
    result: &PointerFlowResult,
    param_index: usize,
) -> Vec<FieldAccessReject> {
    let base = param_base(result, param_index);
    result
        .field_rejects
        .iter()
        .filter(|reject| {
            result
                .provenance
                .reachable_bases
                .get(&reject.node)
                .is_some_and(|bases| bases.contains(&base))
        })
        .cloned()
        .collect()
}

#[test]
fn no_events_without_field_uses() {
    let result = analyze_single(
        r#"
pub unsafe fn passthrough(p: *mut i32) -> *mut i32 {
    p
}
"#,
        "passthrough",
    );
    assert!(result.field_accesses.is_empty());
    // returning the pointer records a Returned reject on the return slot;
    // the pointee is not a struct, so nothing else appears
    assert!(
        result
            .field_rejects
            .iter()
            .all(|r| r.kind == FieldAccessRejectKind::Returned)
    );
}

#[test]
fn direct_field_read() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
    pub b: i32,
}
pub unsafe fn read_a(ctx: *mut Ctx) -> i32 {
    (*ctx).a
}
"#,
        "read_a",
    );
    let accesses = accesses_reaching_param(&result, 0);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].field.index(), 0);
    assert_eq!(accesses[0].kind, FieldAccessKind::Read);
    assert!(rejects_reaching_param(&result, 0).is_empty());
}

#[test]
fn direct_field_write() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn write_a(ctx: *mut Ctx) {
    (*ctx).a = 1;
}
"#,
        "write_a",
    );
    let accesses = accesses_reaching_param(&result, 0);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].kind, FieldAccessKind::Write);
}

#[test]
fn field_address_is_address_kind() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn addr_a(ctx: *mut Ctx) -> *mut i32 {
    &raw mut (*ctx).a
}
"#,
        "addr_a",
    );
    let accesses = accesses_reaching_param(&result, 0);
    assert!(
        accesses
            .iter()
            .any(|a| a.kind == FieldAccessKind::Address && a.field.index() == 0)
    );
}

#[test]
fn access_through_local_alias() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn via_alias(ctx: *mut Ctx) -> i32 {
    let q = ctx;
    (*q).a
}
"#,
        "via_alias",
    );
    let accesses = accesses_reaching_param(&result, 0);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].field.index(), 0);
}

#[test]
fn two_fields_both_reported() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
    pub b: i32,
}
pub unsafe fn both(ctx: *mut Ctx) -> i32 {
    (*ctx).b = 2;
    (*ctx).a
}
"#,
        "both",
    );
    let fields: rustc_hash::FxHashSet<usize> = accesses_reaching_param(&result, 0)
        .iter()
        .map(|a| a.field.index())
        .collect();
    assert_eq!(fields.len(), 2);
}

#[test]
fn integer_array_field_is_reported() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub tweaked: [u64; 8],
}
pub unsafe fn read_elem(ctx: *mut Ctx, i: usize) -> u64 {
    (*ctx).tweaked[i]
}
"#,
        "read_elem",
    );
    let accesses = accesses_reaching_param(&result, 0);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].field.index(), 0);
}

#[test]
fn nested_deref_attributes_inner_access_to_inner_pointer() {
    let result = analyze_single(
        r#"
pub struct Node {
    pub val: i32,
    pub next: *mut Node,
}
pub unsafe fn chase(n: *mut Node) -> i32 {
    (*(*n).next).val
}
"#,
        "chase",
    );
    // only the `next` read is attributed to the parameter; the inner `val`
    // access belongs to the loaded pointer's own (unknown) provenance
    let accesses = accesses_reaching_param(&result, 0);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].field.index(), 1);
    assert_eq!(accesses[0].kind, FieldAccessKind::Read);
}

#[test]
fn non_pointer_struct_local_produces_no_events() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub fn on_stack() -> i32 {
    let s = Ctx { a: 3 };
    s.a
}
"#,
        "on_stack",
    );
    assert!(result.field_accesses.is_empty());
    assert!(result.field_rejects.is_empty());
}

#[test]
fn whole_struct_copy_is_rejected() {
    let result = analyze_single(
        r#"
#[derive(Clone, Copy)]
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn copy_out(ctx: *mut Ctx) -> i32 {
    let s = *ctx;
    s.a
}
"#,
        "copy_out",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::WholeStructUse)
    );
}

#[test]
fn whole_struct_store_is_rejected() {
    let result = analyze_single(
        r#"
#[derive(Clone, Copy)]
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn overwrite(ctx: *mut Ctx, v: Ctx) {
    *ctx = v;
}
"#,
        "overwrite",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::WholeStructUse)
    );
}

#[test]
fn plain_reborrow_is_not_rejected_and_attributes_to_param() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn reborrow(ctx: *mut Ctx) -> i32 {
    let r = &mut *ctx;
    (*r).a
}
"#,
        "reborrow",
    );
    assert!(rejects_reaching_param(&result, 0).is_empty());
    let accesses = accesses_reaching_param(&result, 0);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].field.index(), 0);
}

#[test]
fn union_field_access_is_rejected() {
    let result = analyze_single(
        r#"
#[derive(Clone, Copy)]
pub union Val {
    pub i: i32,
    pub f: f32,
}
pub unsafe fn read_union(v: *mut Val) -> i32 {
    (*v).i
}
"#,
        "read_union",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::UnionFieldAccess)
    );
}

#[test]
fn returning_the_param_is_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn id(ctx: *mut Ctx) -> *mut Ctx {
    ctx
}
"#,
        "id",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::Returned)
    );
}

#[test]
fn storing_param_into_memory_is_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub struct Holder {
    pub p: *mut Ctx,
}
pub unsafe fn stash(h: *mut Holder, ctx: *mut Ctx) {
    (*h).p = ctx;
}
"#,
        "stash",
    );
    // ctx escapes into (*h).p
    let ctx_rejects = rejects_reaching_param(&result, 1);
    assert!(
        ctx_rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::EscapesToMemory)
    );
    // h itself only gets a field write, no reject
    let h_accesses = accesses_reaching_param(&result, 0);
    assert!(
        h_accesses
            .iter()
            .any(|a| a.field.index() == 0 && a.kind == FieldAccessKind::Write)
    );
    assert!(rejects_reaching_param(&result, 0).is_empty());
}

#[test]
fn incompatible_cast_is_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn as_bytes(ctx: *mut Ctx) -> u8 {
    let p = ctx as *mut u8;
    *p
}
"#,
        "as_bytes",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::IncompatibleCast)
    );
}

#[test]
fn mut_to_const_cast_is_not_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn constify(ctx: *mut Ctx) -> i32 {
    let p = ctx as *const Ctx;
    (*p).a
}
"#,
        "constify",
    );
    assert!(rejects_reaching_param(&result, 0).is_empty());
    assert_eq!(accesses_reaching_param(&result, 0).len(), 1);
}

#[test]
fn repeat_of_param_into_array_is_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn spread(ctx: *mut Ctx) -> [*mut Ctx; 4] {
    [ctx; 4]
}
"#,
        "spread",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::EscapesToMemory)
    );
}

#[test]
fn extern_call_is_unknown_callee_reject() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
extern "C" {
    fn consume(ctx: *mut Ctx);
}
pub unsafe fn call_extern(ctx: *mut Ctx) {
    consume(ctx);
}
"#,
        "call_extern",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::UnknownCallee)
    );
}

#[test]
fn pointer_arithmetic_call_is_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn advance(ctx: *mut Ctx) -> *mut Ctx {
    ctx.offset(1)
}
"#,
        "advance",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::PointerArithmetic)
    );
}

#[test]
fn local_callee_without_summary_is_incomplete_reject() {
    // analyze_single passes callee_summaries: None, so the local callee has
    // no summary at the call site
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn callee(ctx: *mut Ctx) -> i32 {
    (*ctx).a
}
pub unsafe fn caller(ctx: *mut Ctx) {
    callee(ctx);
}
"#,
        "caller",
    );
    let rejects = rejects_reaching_param(&result, 0);
    assert!(
        rejects
            .iter()
            .any(|r| r.kind == FieldAccessRejectKind::IncompleteCalleeSummary)
    );
}

#[test]
fn null_check_is_not_rejected() {
    let result = analyze_single(
        r#"
pub struct Ctx {
    pub a: i32,
}
pub unsafe fn checked(ctx: *mut Ctx) -> i32 {
    if ctx.is_null() {
        return 0;
    }
    (*ctx).a
}
"#,
        "checked",
    );
    assert!(rejects_reaching_param(&result, 0).is_empty());
    assert_eq!(accesses_reaching_param(&result, 0).len(), 1);
}
