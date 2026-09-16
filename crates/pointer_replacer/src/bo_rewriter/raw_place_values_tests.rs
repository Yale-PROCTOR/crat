//! Raw-place reborrow values from the frozen ht / urlparser corpus: a raw
//! struct-field read and a static byte-string conditional.

use super::decision::Decision;

fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

fn emitted(input: &str, binding: &str) -> (String, Decision) {
    emitted_reverting(input, binding, false)
}

fn emitted_reverting(input: &str, binding: &str, withdraw: bool) -> (String, Decision) {
    let (source, decision) = ::utils::compilation::run_compiler_on_str(input, move |tcx| {
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
            .expect("subject");
        assert!(
            withdraw
                || !held.contains(&super::bridge_receipt::SignatureClassId::of(subject.fn_did)),
            "the owner must be placed: {:?}",
            emission
                .plan
                .class_finalization
                .classes
                .get(&super::bridge_receipt::SignatureClassId::of(subject.fn_did))
        );
        (source, decision.clone())
    })
    .expect("input compiles");
    assert!(super::verify::type_checks_str(&source), "{source}");
    (source, decision)
}

/// ht `ht_next`: the iterator's raw `_table` field holds the table pointer.
const HT_NEXT: &str = r#"
    #[repr(C)]
    pub struct ht { pub capacity: usize, pub length: usize }
    #[repr(C)]
    pub struct hti { pub _table: *mut ht, pub _index: usize }
    pub unsafe fn ht_next(it: *mut hti) -> bool {
        let mut table = (*it)._table;
        while (*it)._index < (*table).capacity {
            (*it)._index = (*it)._index.wrapping_add(1);
            if (*table).length > 0 {
                return true;
            }
        }
        false
    }
"#;

/// urlparser `url_get_path`: a format string chosen between two literals.
const URL_FMT: &str = r#"
    extern "C" {
        fn sprintf(s: *mut i8, format: *const i8, _: ...) -> i32;
    }
    pub unsafe fn url_get_path(path: *mut i8, tmp_path: *mut i8, is_ssh: bool) {
        let mut fmt = (if is_ssh { b"%s\0" as *const u8 as *const i8 } else { b"/%s\0" as *const u8 as *const i8 }) as *mut i8;
        sprintf(path, fmt, tmp_path);
    }
"#;

#[test]
fn wave6k_ht_next_raw_field_read_is_a_declared_reborrow() {
    let (source, decision) = emitted(HT_NEXT, "table");
    assert!(matches!(decision, Decision::Ref { .. }), "{decision:?}");
    let compact_source = compact(&source);
    assert!(compact_source.contains("table:&"), "{source}");
    assert!(compact_source.contains("*(*it)._table"), "{source}");
}

/// A static literal is not a raw-place value. Its consumer reads to the NUL,
/// so the thin reference is held (R272-1) — and wave-4 R410-9 (b) (report
/// 025; ratified R217-2(a), addendum 411) then delivers it as the
/// counted-literal slice: `&[i8]` with each literal's own byte length,
/// `.as_ptr()` at `sprintf`.
#[test]
fn wave6k_urlparser_static_literal_format_keeps_its_thin_extent_hold() {
    ::utils::compilation::run_compiler_on_str(URL_FMT, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("fmt"))
            .expect("subject");
        assert!(
            matches!(decision, Decision::Slice { mutable: false, .. }),
            "{} takes the counted-literal slice, never a thin reference: {decision:?}",
            subject.label
        );
        assert!(
            super::decision::raw_place_values::value(tcx, subject).is_none(),
            "a literal is not a raw-place value"
        );
    })
    .expect("input compiles");
    let (source, _) = emitted(URL_FMT, "fmt");
    let compact_source = compact(&source);
    assert!(compact_source.contains("fmt:&[i8]="), "{source}");
    assert!(
        compact_source
            .contains(r#"core::slice::from_raw_parts(b"%s\0"as*constu8as*consti8,3usize)"#),
        "{source}"
    );
    assert!(
        compact_source.contains("sprintf(path,fmt.as_ptr(),"),
        "{source}"
    );
}

/// Owner withdrawal restores the untyped raw read.
#[test]
fn wave6k_withdrawn_owner_restores_the_raw_place_read() {
    let (source, _) = emitted_reverting(HT_NEXT, "table", true);
    assert!(source.contains("let mut table = (*it)._table;"), "{source}");
    assert!(!source.contains("table: &"), "{source}");
}
