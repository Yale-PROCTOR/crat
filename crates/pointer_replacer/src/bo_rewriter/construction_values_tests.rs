//! Copy initializer reductions from the frozen brotli corpus.

fn emitted(input: &str, binding: &str) -> String {
    emitted_reverting(input, binding, false)
}

fn emitted_reverting(input: &str, binding: &str, withdraw: bool) -> String {
    let source = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("emission plan");
        let mut held = emission.plan.held_classes();
        if withdraw {
            let owner = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some(binding))
                .unwrap()
                .0
                .fn_did;
            held.insert(super::bridge_receipt::SignatureClassId::of(owner));
        }
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &Default::default(),
            &table,
        )
        .expect("held classes");
        let source = super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("AST emission")
        .0
        .into_values()
        .next()
        .expect("one source");
        println!("EMITTED\n{source}");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some(binding))
            .expect("copy subject");
        assert!(
            matches!(decision, super::decision::Decision::Ref { .. }),
            "{} owes a copy value: {decision:?}",
            subject.label
        );
        assert!(
            withdraw
                || !held.contains(&super::bridge_receipt::SignatureClassId::of(subject.fn_did)),
            "copy must be placed"
        );
        source
    })
    .expect("input compiles");
    assert!(super::verify::type_checks_str(&source), "{source}");
    source
}

#[test]
fn wave6k_brotli_metablock_start_copy() {
    let source = emitted(
        r#"
        pub unsafe fn BrotliCompressFragmentFastImpl(input: *const u8) -> u8 {
            let mut metablock_start = input;
            *metablock_start
        }
    "#,
        "metablock_start",
    );
    assert!(source.contains("metablock_start: &u8"), "{source}");
    assert!(source.contains("&*input"), "{source}");
}

#[test]
fn wave6k_brotli_base_ip_copy() {
    let source = emitted(
        r#"
        pub unsafe fn BrotliCompressFragmentTwoPassImpl(input: *const u8) -> u8 {
            let mut base_ip = input;
            *base_ip + *input
        }
    "#,
        "base_ip",
    );
    assert!(source.contains("base_ip: &u8"), "{source}");
    assert!(source.contains("&*input"), "{source}");
}

#[test]
fn wave6k_lodepng_strlen_original_pointer_copy() {
    let source = emitted(
        r#"
        pub unsafe fn lodepng_strlen(mut a: *const i8) -> usize {
            let mut orig = a;
            while *a != 0 { a = a.offset(1); }
            a.offset_from(orig) as usize
        }
    "#,
        "orig",
    );
    assert!(source.contains("orig: &i8"), "{source}");
}

#[test]
fn wave6k_mutable_copy_allows_later_parent_use() {
    let source = emitted(
        r#"
        pub unsafe fn increment(p: *mut u8) -> u8 {
            let q = p;
            *q += 1;
            *p += 2;
            *p
        }
    "#,
        "q",
    );
    assert!(source.contains("q: &mut u8 = &mut *p"), "{source}");
}

#[test]
fn wave6k_function_withdrawal_restores_both_copy_sites() {
    let source = emitted_reverting(
        r#"
        pub unsafe fn copy(p: *const u8) -> u8 { let q = p; *q }
    "#,
        "q",
        true,
    );
    assert!(source.contains("p: *const u8"), "{source}");
    assert!(source.contains("let q = p"), "{source}");
    assert!(!source.contains("q: &u8"), "{source}");
    assert!(!source.contains("&*p"), "{source}");
}
