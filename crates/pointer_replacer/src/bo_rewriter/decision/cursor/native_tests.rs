use super::*;

pub(super) fn emitted(input: &str) -> String {
    let source = utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = crate::bo_rewriter::ast_transform::capture_ast(tcx).unwrap();
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        println!(
            "CURSOR-FAMILY {:?}",
            ctx.raw_boundary_artifacts.additive_family_receipts
        );
        println!(
            "CURSOR-NATIVE plans {:?}; decisions {:?}",
            table.cursor_receipts,
            table
                .entries
                .iter()
                .map(|(s, d)| (&s.label, d))
                .collect::<Vec<_>>()
        );
        let emission = crate::bo_rewriter::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        let held = emission.plan.held_classes();
        if !held.is_empty() {
            println!("CURSOR-HELD {:#?}", emission.plan.class_finalization);
        }
        let reverts = crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &std::collections::BTreeSet::new(),
            &table,
        )
        .unwrap();
        let (files, _, _, _) = crate::bo_rewriter::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .unwrap();
        files.into_values().next().unwrap()
    })
    .unwrap();
    compile(&source, None);
    source
}

pub(super) fn compile(source: &str, main: Option<&str>) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "cursor-native-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("fixture.rs");
    std::fs::write(
        &path,
        format!(
            "#![allow(unsafe_op_in_unsafe_fn)]\n{source}\n{}",
            main.unwrap_or("")
        ),
    )
    .unwrap();
    let output = directory.join("fixture");
    let mut rustc = std::process::Command::new("rustc");
    rustc
        .arg("--edition=2024")
        .arg(&path)
        .arg("-o")
        .arg(&output);
    if main.is_none() {
        rustc.args(["--crate-type=lib", "--emit=metadata"]);
    }
    let result = rustc.output().unwrap();
    assert!(
        result.status.success(),
        "cursor output did not compile: {}\n{source}",
        String::from_utf8_lossy(&result.stderr)
    );
    if main.is_some() {
        assert!(
            std::process::Command::new(output)
                .status()
                .unwrap()
                .success(),
            "cursor runtime result mismatch"
        );
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn native_ref_fixture_probe() {
    for (name, input) in [
        (
            "raw-array",
            "pub unsafe fn witness() -> i32 { let a = [1_i32;4]; let p: *const i32 = ((&raw const a) as *const i32).add(2); *p.offset(-1) }",
        ),
        (
            "raw-array-mut",
            "pub unsafe fn witness() -> i32 { let mut a = [1_i32;4]; let p: *mut i32 = ((&raw mut a) as *mut i32).add(2); *p.offset(-1) = 3; *p }",
        ),
        (
            "slice-input",
            "pub unsafe fn witness(a: &[i32]) -> i32 { let p: *const i32 = a.as_ptr().add(2); *p.offset(-1) }",
        ),
        (
            "slice-input-mut",
            "pub unsafe fn witness(a: &mut [i32]) -> i32 { let p: *mut i32 = a.as_mut_ptr().add(2); *p.offset(-1) = 3; *p }",
        ),
    ] {
        utils::compilation::run_compiler_on_str(input, |tcx| {
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some("p"))
                .unwrap();
            let row = inspect_subject(tcx, &ctx.slots, &ctx.model, subject);
            let body = tcx
                .mir_drops_elaborated_and_const_checked(subject.fn_did)
                .borrow();
            let kinds = model_kinds(
                subject.fn_did,
                body.local_decls.indices(),
                &ctx.slots,
                &ctx.model,
            );
            println!("NATIVE-PROBE {name}: {kinds:?} DECISION {decision:?} ADMISSION {row:?}");
        })
        .unwrap();
    }
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

// R394 migrates these standing witnesses to the legacy-shaped wrapper.
#[test]
fn requested_negative_offset_emits_cursor_index() {
    let source = emitted(
        "pub unsafe fn witness(a: &[i32; 4]) -> i32 { let p: *const i32 = a.as_ptr().add(2); *p.offset(-1) }",
    );
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "cursor index absent: {source}"
    );
    compile(
        &source,
        Some("fn main() { assert_eq!(unsafe { witness(&[10,20,30,40]) },20); }"),
    );
}

#[test]
fn requested_unknown_offset_emits_cursor_index() {
    let source = emitted(
        "pub unsafe fn witness(a: &[i32; 4], flag: bool) -> i32 { let p: *const i32 = a.as_ptr().add(2); *p.offset(if flag { -1 } else { 1 }) }",
    );
    compile(
        &source,
        Some(
            "fn main() { assert_eq!(unsafe { witness(&[10,20,30,40],true) },20); assert_eq!(unsafe { witness(&[10,20,30,40],false) },40); }",
        ),
    );
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "cursor index absent: {source}"
    );
}

#[test]
fn requested_raw_callee_emits_current_cursor_view() {
    let source = emitted(
        "unsafe fn raw_read(p: *const i32) -> i32 { p.read() } pub unsafe fn witness(a: &[i32; 4], flag: bool) -> i32 { let p: *const i32 = a.as_ptr().offset(if flag { 1 } else { 2 }); *p.offset(-1) + raw_read(p) }",
    );
    assert!(
        source.contains("slice_cursor::SliceCursor") && source.contains("as_ptr"),
        "current cursor view absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { assert_eq!(unsafe { witness(&[10,20,30,40],true) },30); assert_eq!(unsafe { witness(&[10,20,30,40],false) },50); }",
        ),
    );
}

#[test]
fn cursor_unbounded_offsets_and_raw_aliases_remain_held() {
    for (index, input) in [
        "pub unsafe fn witness(a: &[i32;4], delta: isize) -> i32 { let p:*const i32=a.as_ptr().add(2); *p.offset(delta) }",
        "pub unsafe fn witness(a: &[i32;4], flag: bool) -> i32 { let p:*const i32=a.as_ptr().add(2); *p.offset(if flag { -1 } else { 2 }) }",
        "pub unsafe fn witness(a: &mut [i32;4]) -> i32 { let p:*mut i32=a.as_mut_ptr().add(2); let q:*mut i32=&raw mut *p; *p=7; *q=8; *p.offset(-1) }",
        "unsafe extern \"C\" { fn opaque(p:*const i32) -> i32; } pub unsafe fn witness(a:&[i32;4]) -> i32 { let p:*const i32=a.as_ptr().add(2); *p.offset(-1) + opaque(p) }",
    ].into_iter().enumerate() {
        let source = emitted(input);
        assert_eq!(
            source.contains("slice_cursor::SliceCursor"), index < 2,
            "R394 admits dynamic indices; raw aliases and unknown retention stay held: {source}"
        );
    }
}

#[test]
fn cursor_mutable_array_reference_keeps_writes_at_checked_index() {
    let source = emitted(
        "pub unsafe fn witness(a: &mut [i32;4]) -> i32 { let p:*mut i32=a.as_mut_ptr().add(2); *p.offset(-1)=9; *p }",
    );
    assert!(
        source.contains("slice_cursor::SliceCursorMut"),
        "mutable cursor missing: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut a=[1,2,3,4]; assert_eq!(unsafe{witness(&mut a)},3); assert_eq!(a,[1,9,3,4]); }",
        ),
    );
}

#[test]
fn cursor_mutable_t1_binding_supports_whole_tuple_reborrow() {
    let source = emitted(
        "unsafe fn raw_read(p:*const i32)->i32 { p.read() } pub unsafe fn witness(a: &mut [i32;4]) -> i32 { let p:*mut i32=a.as_mut_ptr().add(2); *p.offset(-1)=9; raw_read(p) }",
    );
    assert!(
        source.contains("let mut p:"),
        "mutable cursor needs a reborrowable binding: {source}"
    );
    compile(
        &source,
        Some(
            "fn main(){let mut a=[1,2,3,4];assert_eq!(unsafe{witness(&mut a)},3);assert_eq!(a,[1,9,3,4]);}",
        ),
    );
}

#[test]
fn cursor_checks_intermediate_positions_not_just_final_dereference() {
    let source = emitted(
        "pub unsafe fn witness(a:&[i32;4])->i32 { let p:*const i32=a.as_ptr().add(2); *p.offset(-3).offset(3) }",
    );
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "R394 does not require a static intermediate window: {source}"
    );
    let source = emitted(
        "pub unsafe fn witness(a:&[i32;4])->i32 { let p:*const i32=a.as_ptr().add(2); *p.offset(2).offset(-1) }",
    );
    assert!(
        source.contains("::core::primitive::usize"),
        "one-past then back is within the proved window: {source}"
    );
    compile(
        &source,
        Some("fn main(){assert_eq!(unsafe{witness(&[10,20,30,40])},40);}"),
    );
}

#[test]
fn cursor_preserves_raw_identifier_bindings() {
    let source = emitted(
        "pub unsafe fn witness(a:&[i32;4])->i32 { let r#type:*const i32=a.as_ptr().add(2); *r#type.offset(-1) }",
    );
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "raw identifier cursor did not survive: {source}"
    );
    compile(
        &source,
        Some("fn main(){assert_eq!(unsafe{witness(&[10,20,30,40])},20);}"),
    );
}

#[test]
fn requested_return_takes_raw_return_bridge() {
    // Expectation migrated (relay 005): a derived pointer returned from a
    // wrapper cursor takes the tail address under the raw-boundary T2 receipt.
    let input =
        "pub unsafe fn witness(p: *const i32, delta: isize) -> *const i32 { p.offset(delta) }";
    utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("p"))
            .unwrap();
        let Decision::Cursor { plan, .. } = decision else {
            panic!("returned cursor tail not bridged: {decision:?}")
        };
        assert!(
            plan.uses
                .iter()
                .any(|edit| edit.bridge_kind == "raw-op-cursor-return"),
            "{plan:?}"
        );
    })
    .unwrap();
    let source = emitted(input);
    assert!(
        source.contains(".as_ptr()") && source.contains("-> *const i32"),
        "raw return bridge absent: {source}"
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
