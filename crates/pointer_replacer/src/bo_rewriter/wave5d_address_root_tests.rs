//! R473-2 — the address of a value local is a trivially safe raw-boundary
//! source.
//!
//! The cascade's dominant seed (44 of 59 at `batch1315`; 221 subjects behind
//! the 59) is one shape: `&mut x` / `&x` over a LOCAL binding whose type is not
//! a raw pointer, refused because `decisions` carries no entry for the root.
//! It never can: a non-pointer local is not a pointer subject, so the gate asks
//! for a fact the root cannot have. A `Degraded` subject IS in that map and
//! takes its own path, so absence means "not a pointer subject", not "unsafe".
//!
//! Nothing here synthesizes retention: the callee's retention of the address is
//! the existing tier's question. The controls below prove exactly that.

use std::collections::BTreeSet;

/// One real pipeline run. Returns (dispositions TSV, emitted root file).
fn run(input: &str) -> (String, String) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx)?;
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        )))?;
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)?;
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(), &BTreeSet::new(), &table,
        )?;
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
            tcx, &capture, &reverts, emission.plan.root_file.as_ref(), &table,
            Some(&emission.plan.terminal_call_plans),
        )?;
        Ok::<_, String>((
            ctx.raw_boundary_artifacts.dispositions.clone(),
            files.into_values().next().expect("address-root fixture root"),
        ))
    })
    .expect("address-root fixture compiles")
    .expect("attested address-root emission")
}

/// The disposition rows whose `callee` column is exactly `callee`.
fn rows<'a>(dispositions: &'a str, callee: &str) -> Vec<&'a str> {
    dispositions
        .lines()
        .skip(1)
        .filter(|line| line.split('\t').nth(3) == Some(callee))
        .collect()
}

/// binn's shape, reduced: `binn_list_read` passes `&mut binn_struct` into
/// `binn_list_get_value`'s `*mut` parameter. 8 seeds, 34 members behind them.
const VALUE_LOCAL: &str = "#![allow(dead_code, unused_unsafe)]\n\
    #[derive(Copy, Clone)]\n\
    pub struct Rec { pub a: i32, pub b: i32 }\n\
    unsafe fn fill(out: *mut Rec) { (*out).a = 1; (*out).b = 2; }\n\
    pub unsafe fn entry() -> i32 {\n\
        let mut rec = Rec { a: 0, b: 0 };\n\
        fill(&mut rec);\n\
        rec.a + rec.b\n\
    }\n";

#[test]
fn r473_2_the_address_of_a_value_local_is_a_trivially_safe_source() {
    let (dispositions, emitted) = run(VALUE_LOCAL);
    let fill = rows(&dispositions, "fill");
    println!("R473-2 value-local dispositions:\n{}", fill.join("\n"));
    assert!(
        !fill.is_empty(),
        "AUTHORING PREMISE: the `&mut rec` argument reaches a raw-boundary site"
    );
    // The site's PUBLIC disposition stays refused on purpose: the admission
    // unlocks the callee's parameter input and nothing else, so no other arm's
    // reading of this site moves. The receipt says the input was admitted, and
    // the delivery below is the proof that it was.
    assert!(
        fill.iter()
            .any(|row| row.contains("address-of-value-local-input")),
        "the admitted input must carry its receipt:\n{}",
        fill.join("\n")
    );
    assert!(
        emitted.contains("fn fill(out: &mut Rec)"),
        "the callee's parameter must be delivered native:\n{emitted}"
    );
    assert!(
        emitted.contains("fill(&mut rec)"),
        "the caller's argument is already the delivered form — zero syntax:\n{emitted}"
    );
}

/// Control 1 — a pointee that IS a raw pointer is not this shape. That root is
/// a pointer local and keeps its decision path; admitting it here would answer
/// a decision question with a syntactic one.
#[test]
fn r473_2_a_raw_pointer_pointee_is_not_a_value_local() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        unsafe fn take(pp: *mut *mut i32) { let _ = *pp; }\n\
        pub unsafe fn entry(seed: *mut i32) {\n\
            let mut inner: *mut i32 = seed;\n\
            take(&mut inner);\n\
        }\n";
    let (dispositions, _) = run(input);
    let take = rows(&dispositions, "take");
    println!(
        "R473-2 raw-pointer-pointee dispositions:\n{}",
        take.join("\n")
    );
    assert!(
        take.iter()
            .all(|row| !row.contains("address-of-value-local-input")),
        "a raw-pointer pointee must not be admitted as a value local:\n{}",
        take.join("\n")
    );
}

/// Control 2 — the address of a PROJECTION is not the address of a local. The
/// rule is deliberately narrow: `&mut rec.a` is sound too, but it is not what
/// was measured or priced, so it stays refused until it is.
#[test]
fn r473_2_a_projection_is_not_a_local_root() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        #[derive(Copy, Clone)]\n\
        pub struct Rec { pub a: i32, pub b: i32 }\n\
        unsafe fn bump(out: *mut i32) { *out += 1; }\n\
        pub unsafe fn entry() -> i32 {\n\
            let mut rec = Rec { a: 0, b: 0 };\n\
            bump(&mut rec.a);\n\
            rec.a + rec.b\n\
        }\n";
    let (dispositions, _) = run(input);
    let bump = rows(&dispositions, "bump");
    println!("R473-2 projection dispositions:\n{}", bump.join("\n"));
    assert!(
        bump.iter()
            .all(|row| !row.contains("address-of-value-local-input")),
        "a field projection must not be admitted as a local root:\n{}",
        bump.join("\n")
    );
}

/// Control 3 — retention is the TIER's question, not this rule's. The callee
/// stores the address into a static; the site must still be refused, and by
/// positive retention rather than by a missing subject decision.
#[test]
fn r473_2_a_retained_address_is_refused_by_the_tier_not_by_this_rule() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        #[derive(Copy, Clone)]\n\
        pub struct Rec { pub a: i32, pub b: i32 }\n\
        static mut SAVED: *mut Rec = 0 as *mut Rec;\n\
        unsafe fn keep(out: *mut Rec) { SAVED = out; }\n\
        pub unsafe fn entry() -> i32 {\n\
            let mut rec = Rec { a: 0, b: 0 };\n\
            keep(&mut rec);\n\
            rec.a\n\
        }\n";
    let (dispositions, _) = run(input);
    let keep = rows(&dispositions, "keep");
    println!("R473-2 retained-address dispositions:\n{}", keep.join("\n"));
    assert!(
        keep.iter()
            .any(|row| row.contains("raw-boundary-positive-retention")),
        "a retained address must be refused by positive retention, not by a \
         missing subject decision:\n{}",
        keep.join("\n")
    );
    assert!(
        keep.iter()
            .all(|row| !row.contains("address-of-value-local-input")),
        "a retained address is never admitted as an input:\n{}",
        keep.join("\n")
    );
}

/// binn's actual shape: the struct the address points at has RAW POINTER
/// FIELDS. That is still a value local — the rule reads the LOCAL's own type,
/// not its contents, because the claim is about the address's validity, not
/// about what the callee may do through it. 8 corpus seeds, 34 members.
#[test]
fn r473_2_a_struct_with_pointer_fields_is_still_a_value_local() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        #[derive(Copy, Clone)]\n\
        pub struct Iter { pub pbuf: *mut i8, pub count: i32 }\n\
        unsafe fn next(it: *mut Iter) -> i32 { (*it).count += 1; (*it).count }\n\
        pub unsafe fn entry(buf: *mut i8) -> i32 {\n\
            let mut it = Iter { pbuf: buf, count: 0 };\n\
            next(&mut it)\n\
        }\n";
    let (dispositions, emitted) = run(input);
    let next = rows(&dispositions, "next");
    println!(
        "R473-2 pointer-field struct dispositions:\n{}",
        next.join("\n")
    );
    assert!(
        next.iter()
            .any(|row| row.contains("address-of-value-local")),
        "a struct with pointer fields is a value local:\n{}",
        next.join("\n")
    );
    assert!(
        emitted.contains("fn next(it: &mut Iter)"),
        "the callee's parameter must be delivered native:\n{emitted}"
    );
}

/// Clause 1 — the shape gate. A `-cast` variant is a different source
/// expression; a bare local or a raw expression is not an address at all.
#[test]
fn r473_2_only_a_bare_address_shape_is_admitted() {
    use super::decision::raw_boundary::address_of_value_local_source;
    assert_eq!(
        address_of_value_local_source("addr-of-mut", true, false),
        Some(super::decision::Decision::Ref { mutable: true })
    );
    assert_eq!(
        address_of_value_local_source("addr-of", true, false),
        Some(super::decision::Decision::Ref { mutable: false })
    );
    for shape in [
        "addr-of-mut-cast",
        "addr-of-cast",
        "bare-local",
        "raw-expr",
        "cast-of-local",
    ] {
        assert_eq!(
            address_of_value_local_source(shape, true, false),
            None,
            "{shape} is not a bare address of a local"
        );
    }
}

/// Clause 2 — the root must be a LOCAL binding path.
#[test]
fn r473_2_a_non_local_root_is_refused() {
    use super::decision::raw_boundary::address_of_value_local_source;
    assert_eq!(
        address_of_value_local_source("addr-of-mut", false, false),
        None
    );
}

/// Clause 3 — a raw-pointer local IS a pointer subject and keeps its decision
/// path. A syntactic admission must not answer its decision question.
#[test]
fn r473_2_a_raw_pointer_local_keeps_its_decision_path() {
    use super::decision::raw_boundary::address_of_value_local_source;
    assert_eq!(
        address_of_value_local_source("addr-of-mut", true, true),
        None
    );
    assert_eq!(address_of_value_local_source("addr-of", true, true), None);
}
