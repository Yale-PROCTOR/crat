use super::*;

fn emitted(input: &str) -> String {
    crate::bo_rewriter::emit_tests::ast_emitted_source_of(input).unwrap()
}

#[test]
fn native_admission_binds_real_model_to_compiler_identity() {
    utils::compilation::run_compiler_on_str("pub unsafe fn witness() -> i32 { let a = [1_i32; 4]; let p: *const i32 = a.as_ptr(); *p.offset(1) }", |tcx| {
        // Production collection/solve on this small fixture supplies the
        // accepted model; no all-Ref test map substitutes for it.
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let subject = &table.entries.iter().find(|(s, _)| s.param_name.as_deref() == Some("p")).unwrap().0;
        let row = inspect_subject(tcx, &ctx.slots, &ctx.model, subject);
        assert_eq!(row.owner, subject.fn_did);
        assert_eq!(row.local, subject.local);
        assert_eq!(row.shape, admission::Shape::LocalArray);
        let kinds = model_kinds(subject.fn_did, tcx.mir_drops_elaborated_and_const_checked(subject.fn_did).borrow().local_decls.indices(), &ctx.slots, &ctx.model);
        println!("native component model: {kinds:?}; outcome: {row:?}");
        // Measured at L01 double-prime: at least one native component member
        // lacks Ref authority. The synthetic all-Ref premise must not leak in.
        assert_eq!(row.status, admission::Status::NeedsFact, "{row:#?}");
        assert_eq!(row.findings[0].outcome, admission::Outcome::Missing(admission::Need::RefAdmission));
        let without_model = inspect_subject(tcx, &ctx.slots, &FxHashMap::default(), subject);
        assert_eq!(without_model.status, admission::Status::NeedsFact);
    }).unwrap();
}

// These are requested production-emission RED witnesses. Keep their observed
// failure explicit until shared Cursor form/renderer support is authorized.
#[test]
fn requested_negative_offset_emits_cursor_index() {
    let source = emitted(
        "pub unsafe fn witness() -> i32 { let a = [1_i32; 4]; let p: *const i32 = a.as_ptr().add(2); *p.offset(-1) }",
    );
    assert!(
        source.contains("checked_add_signed"),
        "cursor index absent: {source}"
    );
}

#[test]
fn requested_unknown_offset_emits_cursor_index() {
    let source = emitted(
        "pub unsafe fn witness(delta: isize) -> i32 { let a = [1_i32; 4]; let p: *const i32 = a.as_ptr().add(2); *p.offset(delta) }",
    );
    assert!(
        source.contains("checked_add_signed"),
        "cursor index absent: {source}"
    );
}

#[test]
fn requested_raw_callee_emits_current_cursor_view() {
    let source = emitted(
        "unsafe extern \"C\" { fn memchr(p: *const core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; } pub unsafe fn witness(delta: isize) -> bool { let a = [1_u8; 4]; let p: *const u8 = a.as_ptr().add(2); memchr(p.offset(delta) as *const core::ffi::c_void, 0, 1).is_null() }",
    );
    assert!(
        source.contains("checked_add_signed") && source.contains("as_ptr"),
        "current cursor view absent: {source}"
    );
}

#[test]
fn requested_return_keeps_typed_cursor_hold() {
    let input =
        "pub unsafe fn witness(p: *const i32, delta: isize) -> *const i32 { p.offset(delta) }";
    assert_typed_hold(input, "p");
    let source = emitted(input);
    assert!(
        source.contains("*const i32"),
        "unsupported cursor return must hold: {source}"
    );
}

#[test]
fn requested_storage_keeps_typed_cursor_hold() {
    let input = "pub struct Store { p: *const i32 } pub unsafe fn witness(s: *mut Store, p: *const i32, delta: isize) { (*s).p = p.offset(delta); }";
    assert_typed_hold(input, "p");
    let source = emitted(input);
    assert!(
        source.contains("*const i32"),
        "unsupported cursor storage must hold: {source}"
    );
}

fn assert_typed_hold(input: &str, name: &str) {
    utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some(name))
            .unwrap();
        let Decision::Degraded(reason) = decision else {
            panic!("unsupported cursor boundary escaped typed hold: {decision:?}")
        };
        assert!(!reason.reason.key().is_empty());
        let row = inspect_subject(tcx, &ctx.slots, &ctx.model, subject);
        assert_ne!(row.status, admission::Status::DecisionOnly);
        println!(
            "boundary {name}: {:?}; admission {:?}",
            reason.reason, row.status
        );
    })
    .unwrap();
}
