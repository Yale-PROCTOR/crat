//! Corpus-shaped witnesses for the wave-5r revert partition.

const STRUCT_SLICE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
#[derive(Clone, Copy)]
pub struct Info { pub outputs: i32 }
pub unsafe fn inspect(info: *const Info) -> i32 {
    if info.is_null() { return 0; }
    (*info.offset(1)).outputs + (*info).outputs
}
"#;

/// A cast repair cannot supply the multi-byte extent of fwrite's source; the
/// contract can. Since wave-4 #1b's `fwrite` row (R386-3) the position is a
/// counted contract, so the counted buffer takes the SLICE form with the
/// exact count `buffersize` — never the one-byte reference this witness was
/// written against — and the raw function is no longer retained.
#[test]
fn wave5r_e0606_counted_foreign_read_stays_raw_without_extent() {
    let input = r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe extern "C" {
            fn fwrite(buffer: *const core::ffi::c_void, size: usize,
                count: usize, file: *mut core::ffi::c_void) -> usize;
        }
        pub unsafe fn save(buffer: *const u8, buffersize: usize, file: *mut core::ffi::c_void) {
            fwrite(buffer as *const core::ffi::c_void, 1, buffersize, file);
        }
    "#;
    let attempted = ast_source_reverting(input, None);
    assert!(
        !attempted.contains("buffer: &u8"),
        "the unlicensed one-byte form is never attempted: {attempted}"
    );
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        true,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let (source, reverted_count) = match outcome {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        }
        | super::RewriteOutcome::Degraded {
            source,
            reverted_count,
            ..
        } => (source, reverted_count),
    };
    println!("R5-HELD {source}");
    assert!(super::verify::type_checks_str(&source));
    assert!(
        source.contains("buffer: &[u8]")
            && source.contains(
                "fwrite(buffer.as_ptr().cast::<core::ffi::c_void>(), 1, buffersize, file)"
            ),
        "the counted buffer takes the slice form with its exact count: {source}"
    );
    assert!(
        !source.contains("buffer: &u8"),
        "one-byte reference must not replace the counted buffer: {source}"
    );
    assert_eq!(reverted_count, 0, "nothing is retained raw: {source}");
}

#[test]
fn wave5r_e0596_shared_field_borrow_into_readonly_callee() {
    let source = emitted(
        r#"
        #![allow(dead_code, unused_unsafe)]
        pub struct Part { value: i32 }
        pub struct Whole { a: Part, b: Part }
        unsafe fn child(p: *mut Part) {}
        pub unsafe fn wrapper(p: *mut Whole) {
            child(&mut (*p).a);
            child(&mut (*p).b);
        }
    "#,
    );
    assert!(
        source.contains("p: &Whole"),
        "readonly root stays shared: {source}"
    );
    assert!(
        !source.contains("&mut (*p)"),
        "field borrow has shared permission: {source}"
    );
}

#[test]
fn wave5r_e0596_written_field_keeps_mutable_permission() {
    let source = emitted(
        r#"
        #![allow(dead_code, unused_unsafe)]
        pub struct Part { value: i32 }
        pub struct Whole { a: Part }
        unsafe fn child(p: *mut Part) { (*p).value += 1; }
        pub unsafe fn wrapper(p: *mut Whole) { child(&mut (*p).a); }
    "#,
    );
    assert!(
        source.contains("p: &mut Whole"),
        "written root needs mutable permission: {source}"
    );
}

fn emitted(input: &str) -> String {
    emitted_reverting(input, None)
}

fn emitted_reverting(input: &str, reverted_function: Option<&str>) -> String {
    let source = ast_source_reverting(input, reverted_function);
    println!("EMITTED\n{source}");
    assert!(
        super::verify::type_checks_str(&source),
        "emitted source must type-check:\n{source}"
    );
    source
}

fn ast_source_reverting(input: &str, reverted_function: Option<&str>) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("capture original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native corpus-mode decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("native emission plan");
        let mut held = emission.plan.held_classes();
        if let Some(name) = reverted_function {
            let owner = tcx
                .hir_body_owners()
                .find(|owner| tcx.def_path_str(owner.to_def_id()) == name)
                .expect("the reverted fixture function exists");
            held.insert(super::bridge_receipt::SignatureClassId::of(owner));
        }
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &Default::default(),
            &table,
        )
        .expect("planned held classes");
        super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("native AST emission")
        .0
        .into_values()
        .next()
        .expect("one source file")
    })
    .expect("input type-checks")
}

const FIELD_CALL: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub struct Part { value: i32 }
    pub struct Whole { a: Part }
    unsafe fn child(p: *mut Part) {}
    pub unsafe fn wrapper(p: *mut Whole) { child(&mut (*p).a); }
"#;

#[test]
fn wave5r_e0596_reverted_caller_retains_valid_original_borrow() {
    let source = emitted_reverting(FIELD_CALL, Some("wrapper"));
    assert!(source.contains("p: *mut Whole"));
    assert!(source.contains("&mut (*p).a"));
}

/// Migrated by wave-6r (R217-2(a)): a withdrawn callee class keeps its raw
/// formal, and the shared root's field address now bridges read-only under
/// the callee's negative-write evidence instead of failing the compile gate.
#[test]
fn wave5r_e0596_reverted_callee_bridges_shared_root_read_only() {
    let source = emitted_reverting(FIELD_CALL, Some("child"));
    assert!(source.contains("child(p: *mut Part)"), "{source}");
    assert!(
        source.contains("child(core::ptr::from_ref(&(*p).a).cast_mut())"),
        "the raw callee receives a read-only view of the shared root: {source}"
    );
    assert!(!source.contains("&mut (*p).a"), "{source}");
}

#[test]
fn wave5r_e0382_indirect_growth_callback_has_no_lend_certificate() {
    use super::decision::ownership_fields_effects::{EffectsHold, NativeEffects};
    let source = r#"
        pub struct Parser { data: *mut u8, grow: unsafe fn(*mut u8, usize) -> *mut u8 }
        pub unsafe fn csv_increase_buffer(p: *mut Parser) {
            (*p).data = ((*p).grow)((*p).data, 16);
        }
    "#;
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = super::collect_program(tcx);
        let function = program
            .functions
            .iter()
            .copied()
            .find(|f| tcx.def_path_str(f.to_def_id()) == "csv_increase_buffer")
            .unwrap();
        let effects = NativeEffects::derive(&program);
        assert!(
            matches!(effects.certify(function, 0), Err(EffectsHold::Opaque(_))),
            "an indirect realloc callback cannot receive the landed no-consume certificate"
        );
    })
    .expect("native callback fixture compiles");
}

#[test]
fn wave5r_e0499_overlapping_mutable_arguments_require_a_hold() {
    let raw = "unsafe fn add(a: *mut i32, b: *mut i32) { *a += *b; } fn caller() { let mut diff = 1; unsafe { add(&mut diff, &mut diff); } }";
    assert!(super::verify::type_checks_str(raw));
    let references = raw.replace("*mut i32", "&mut i32");
    assert!(
        !super::verify::type_checks_str(&references),
        "compiler aliasing hold remains required"
    );
}

#[test]
fn wave5r_e0503_live_field_borrow_requires_a_hold() {
    let raw = "struct State { flags: i32 } fn caller() { let mut state = State { flags: 1 }; let p: *mut i32 = &mut state.flags; state.flags += 1; unsafe { *p += 1; } }";
    assert!(super::verify::type_checks_str(raw));
    assert!(
        !super::verify::type_checks_str(&raw.replace("*mut i32", "&mut i32")),
        "use through the owner while a mutable field reference is live stays held"
    );
}

#[test]
fn wave5r_e0609_struct_slice_field() {
    let source = emitted(STRUCT_SLICE);
    assert!(source.contains("(info.unwrap())[0].outputs"));
    assert!(source.contains("info.unwrap()[1].outputs"));
    assert!(
        source.contains("[Info]"),
        "witness must exercise a slice: {source}"
    );
    assert!(
        !source.contains("(*info).outputs"),
        "slice receiver selects its element: {source}"
    );
}

#[test]
fn wave5r_e0609_mutable_slice_field() {
    let source = emitted(&STRUCT_SLICE.replace("*const Info", "*mut Info").replace(
        "(*info.offset(1)).outputs + (*info).outputs",
        "(*info).outputs += 1; (*info.offset(1)).outputs + (*info).outputs",
    ));
    assert!(
        source.contains("Option<&mut [Info]>"),
        "mutable optional slice survives: {source}"
    );
    assert!(
        source.contains("[0].outputs += 1"),
        "write selects the current element: {source}"
    );
}

#[test]
fn wave5r_e0609_thin_optional_field_control() {
    let source = emitted(&STRUCT_SLICE.replace(
        "(*info.offset(1)).outputs + (*info).outputs",
        "(*info).outputs",
    ));
    assert!(
        source.contains("Option<&Info>"),
        "thin optional stays thin: {source}"
    );
    assert!(
        !source.contains("[0]"),
        "thin field use needs no index: {source}"
    );
}

#[test]
fn wave5r_e0308_raw_cast_initializer_into_ref() {
    let source = emitted(
        r#"
        #![allow(dead_code, unused_unsafe)]
        pub struct Item { value: i32 }
        pub unsafe fn inspect(p: *const Item) -> i32 {
            let q: *const Item = &*p as *const Item;
            (*q).value
        }
    "#,
    );
    assert!(
        source.contains("q: &Item"),
        "the local must promote: {source}"
    );
}

#[test]
fn wave5r_e0308_raw_void_cast_into_optional_char() {
    let source = emitted(VOID_CAST_INPUT);
    assert!(
        source.contains("pvalue: *mut core::ffi::c_void"),
        "void input stays raw: {source}"
    );
    assert!(
        source.contains("s: Option<&i8>"),
        "callee optional character remains: {source}"
    );
    assert!(
        source.contains("(pvalue as *mut i8).as_ref()"),
        "cast target precedes reference construction: {source}"
    );
}

const VOID_CAST_INPUT: &str = r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe fn strlen2(s: *mut i8) -> i32 {
            if s.is_null() { 0 } else { *s as i32 }
        }
        pub unsafe fn add_value(pvalue: *mut core::ffi::c_void) -> i32 {
            strlen2(pvalue as *mut i8)
        }
    "#;

#[test]
fn wave5r_e0308_cast_input_survives_caller_reversion() {
    let source = emitted_reverting(VOID_CAST_INPUT, Some("add_value"));
    assert!(source.contains("(pvalue as *mut i8).as_ref()"));
}

#[test]
fn wave5r_e0308_cast_input_survives_callee_reversion() {
    let source = emitted_reverting(VOID_CAST_INPUT, Some("strlen2"));
    assert!(source.contains("strlen2(pvalue as *mut i8)"));
    assert!(!source.contains(".as_ref()"));
}

#[test]
fn wave5r_e0308_mutable_address_into_shared_reference() {
    let source = emitted(
        r#"
        #![allow(dead_code, unused_unsafe)]
        pub struct Item { value: i32 }
        pub unsafe fn inspect(p: *mut Item) -> i32 {
            let q: *mut Item = &mut *p.offset(1) as *mut Item;
            (*q).value
        }
    "#,
    );
    assert!(
        source.contains("q: &Item"),
        "read-only local remains shared: {source}"
    );
    assert!(
        !source.contains("as *mut Item"),
        "only the raw cast is erased: {source}"
    );
}

#[test]
fn wave5r_e0308_raw_destination_keeps_its_initializer() {
    let source = emitted(
        r#"
        #![allow(dead_code, unused_unsafe)]
        pub struct Item { value: i32 }
        pub unsafe fn inspect(p: *mut Item) -> i32 {
            let q: *mut Item = &mut *p.offset(1) as *mut Item;
            (*q).value += 1;
            (*q).value
        }
    "#,
    );
    assert!(
        source.contains("q: *mut Item"),
        "a model-Raw local remains raw: {source}"
    );
    // wave-6s (report 005): the base `p` now delivers as a slice and the raw
    // destination receives the suffix's pointer under the existing body raw
    // alias receipt; the identity-cast peel still does not fire on a raw
    // destination.
    assert!(
        source.contains("let q: *mut Item = (&mut (p)[1..]).as_mut_ptr();"),
        "{source}"
    );
}

#[path = "wave6r_option_tests.rs"]
mod wave6r_option_tests;

#[path = "wave6r_shared_root_tests.rs"]
mod wave6r_shared_root_tests;

#[path = "wave6r_child_access_tests.rs"]
mod wave6r_child_access_tests;

#[path = "wave6r_url_tests.rs"]
mod wave6r_url_tests;

#[path = "wave6r_returned_alias_tests.rs"]
mod wave6r_returned_alias_tests;

#[path = "wave6r_static_dict_tests.rs"]
mod wave6r_static_dict_tests;

#[path = "wave6r_iterator_tests.rs"]
mod wave6r_iterator_tests;

#[path = "wave6r_address_alias_tests.rs"]
mod wave6r_address_alias_tests;

#[path = "wave6r_consumed_result_tests.rs"]
mod wave6r_consumed_result_tests;

#[path = "wave6r_output_storage_seam_tests.rs"]
mod wave6r_output_storage_seam_tests;
