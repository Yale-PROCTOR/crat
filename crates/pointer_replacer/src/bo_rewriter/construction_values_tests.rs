//! Copy initializer reductions from the frozen brotli corpus.

use super::decision::Decision;

/// Every subject's settled decision, keyed by binding name.
fn decisions(input: &str) -> Vec<(String, Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        table
            .entries
            .iter()
            .map(|(subject, decision)| {
                println!("DECISION {} {decision:?}", subject.label);
                (
                    subject.param_name.clone().unwrap_or_default(),
                    decision.clone(),
                )
            })
            .collect()
    })
    .expect("input compiles")
}

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

/// heman `heman_ops_sobel::fresh13#271` (A12, relay 031): the copy's source is
/// a LOCAL already decided a safe form, and the rule refused it because only a
/// parameter source was admitted — `copy-source-coupled` with nothing wrong.
const LOCAL_SOURCE: &str = r#"
    pub unsafe fn pick(p: *mut i32) -> *mut i32 { p }
    pub unsafe fn walk(p: *mut i32) -> i32 {
        let got = pick(p);
        let peer = got;
        *peer
    }
"#;

/// The acyclicity guard: a copy of a copy is refused, so the walk is one hop.
const COPY_OF_A_COPY: &str = r#"
    pub unsafe fn chain(p: *mut i32) -> i32 {
        let first = p;
        let second = first;
        *second
    }
"#;

#[test]
fn wave6k_a_copy_of_a_delivered_local_is_typed() {
    let decided = decisions(LOCAL_SOURCE);
    for (name, decision) in &decided {
        println!("PROBE {name} {decision:?}");
    }
    let peer = decided
        .iter()
        .find(|(name, _)| name == "peer")
        .map(|(_, d)| d.clone())
        .expect("the copy");
    assert!(
        !matches!(
            peer,
            Decision::Degraded(ref degraded) if degraded.reason.key() == "copy-source-coupled"
        ),
        "a copy of a delivered LOCAL is this rule's shape: {peer:?}"
    );
}

#[test]
fn wave6k_a_copy_of_a_copy_keeps_the_refusal() {
    let decided = decisions(COPY_OF_A_COPY);
    let second = decided
        .iter()
        .find(|(name, _)| name == "second")
        .map(|(_, d)| d.clone())
        .expect("the second copy");
    assert!(
        matches!(second, Decision::Degraded(_)),
        "the walk stops at one hop, so a copy of a copy is not typed: {second:?}"
    );
}

/// libcsv `csv_write2::csrc#9` (relay 035; wave-6v 028 route (a)): a counted
/// `*const c_void` parameter reinterpreted as bytes. The contract rewrites the
/// initializer and every use, so the local needs no declaration of its own; the
/// receiver-form refusal degraded it `copy-source-coupled` for lacking one.
const COUNTED_READ_ALIAS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
static mut SINK: u64 = 0;
unsafe fn sink(c: i32) -> i32 { SINK = SINK.wrapping_mul(31).wrapping_add(c as u64); 0 }
unsafe fn csv_fwrite2(mut src: *const core::ffi::c_void, mut src_size: u64, mut quote: u8) -> i32 {
    let mut csrc = src as *const u8;
    if src.is_null() { return 0 as i32; }
    if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }
    while src_size != 0 {
        if *csrc as i32 == quote as i32 {
            if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }
        }
        if sink(*csrc as i32) == -(1 as i32) { return -(1 as i32); }
        src_size = src_size.wrapping_sub(1);
        csrc = csrc.offset(1);
    }
    if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }
    return 0 as i32;
}
unsafe fn csv_fwrite(mut src: *const core::ffi::c_void, mut src_size: u64) -> i32 {
    return csv_fwrite2(src, src_size, 0x22 as i32 as u8);
}
"#;

/// The control: the same copy shape over a source that is NOT a counted
/// contract keeps the refusal — the exemption is the contract's, not the cast's.
const PLAIN_CAST_COPY: &str = r#"
    pub unsafe fn scan(mut src: *const i8, mut n: usize) -> usize {
        let mut us = src as *const u8;
        let mut chars = 0usize;
        while n > 0 {
            if *us == b'"' { chars += 1; }
            us = us.offset(1);
            n -= 1;
        }
        chars
    }
"#;

/// **The hook is in and the predicate now reads it (relay 036); this witness
/// still cannot fire in a REDUCTION.** `alias_contract` answers from the
/// contract that rewrote the local, and in this fixture no contract is proved
/// for `csv_fwrite2::src` at all — the family contracts the outer wrapper
/// (`csv_fwrite::src`, decided `Opt { slice: true }`) and the alias lives in the
/// inner function. The corpus is the other way round (`csv_write2::src#3` is a
/// subject decided `optional` in the same function as `csrc`), so the live check
/// for these three rows is the census, not a reduction — fixture ≠ corpus,
/// R452-2 (i). Un-ignore when a reduction contracts the aliasing parameter.
#[test]
#[ignore = "the reduction contracts the outer wrapper, not the aliasing parameter (report 036)"]
fn wave6k_a_counted_read_alias_is_not_asked_for_a_declaration() {
    let decided = decisions(COUNTED_READ_ALIAS);
    let csrc = decided
        .iter()
        .find(|(name, _)| name == "csrc")
        .map(|(_, d)| d.clone())
        .expect("the alias");
    assert!(
        !matches!(
            csrc,
            Decision::Degraded(ref degraded) if degraded.reason.key() == "copy-source-coupled"
        ),
        "the counted alias needs no declaration and must not be degraded for lacking one: {csrc:?}"
    );
}

#[test]
fn wave6k_a_plain_cast_copy_keeps_the_refusal() {
    let decided = decisions(PLAIN_CAST_COPY);
    let us = decided
        .iter()
        .find(|(name, _)| name == "us")
        .map(|(_, d)| d.clone())
        .expect("the copy");
    assert!(
        matches!(us, Decision::Degraded(_)),
        "a cast copy with no counted contract behind it keeps the veto: {us:?}"
    );
}
