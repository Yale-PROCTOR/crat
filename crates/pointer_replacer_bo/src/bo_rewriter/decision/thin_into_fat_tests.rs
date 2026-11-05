//! **R758-1 (2) / R763-1 (a), main 147 §2 — the thin-into-fat hand-on.** A
//! subject whose own uses carry no arithmetic, handed bare to a callee
//! parameter the program uses as an array, is itself used as an array. Before
//! the rule it took the thin form and reached the callee as a one-element
//! `core::slice::from_ref` / `from_mut` (shape (i), R416-5's defect: the callee
//! indexes past it and panics on a UB-free input).
use super::slice_input_tests::{decision, decisions};

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

fn emitted(input: &str) -> String {
    match crate::bo_rewriter::rewrite_m1(input) {
        crate::bo_rewriter::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must emit: {other:#?}"),
    }
}

/// The census world (the frozen benchmark graph): every function with a
/// converting parameter has an exposure surface plan there. The witnesses of
/// corpus forwarders that are entries (`#[no_mangle]`, `pub`) emit here; in the
/// open world narrowing 2 (b) keeps such an entry's signature (main 170).
fn emitted_census(input: &str) -> String {
    match crate::bo_rewriter::rewrite_m1_census_world(input) {
        crate::bo_rewriter::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must emit: {other:#?}"),
    }
}

fn is_slice(decision: &super::Decision) -> bool {
    matches!(
        decision,
        super::Decision::Slice { .. } | super::Decision::Opt { slice: true, .. }
    )
}

/// brotli `BrotliFindAllStaticDictionaryMatches::matches` (54′: 81 one-element
/// views into `AddMatch`): an exported forwarder whose one caller hands it the
/// first element of a local array.
const MATCHES: &str = r#"
unsafe fn AddMatch(distance: usize, len: usize, len_code: usize, matches: *mut u32) {
    let match_0 = (distance << 5).wrapping_add(len_code) as u32;
    if match_0 < *matches.offset(len as isize) {
        *matches.offset(len as isize) = match_0;
    }
}
#[no_mangle]
pub unsafe extern "C" fn FindAll(data: *const u8, n: usize, matches: *mut u32) -> i32 {
    let mut found = 0;
    if n > 2 && *data.offset(0) as i32 == 1 {
        AddMatch(1, 2, 2, matches);
        found = 1;
    }
    if n > 3 {
        AddMatch(3, 3, 3, matches);
        found = 1;
    }
    found
}
pub unsafe fn caller(data: *const u8, n: usize) -> u32 {
    let mut dict_matches: [u32; 38] = [0xfffffff; 38];
    if FindAll(data, n, &mut *dict_matches.as_mut_ptr().offset(0)) != 0 {
        dict_matches[3]
    } else {
        0
    }
}
"#;

#[test]
fn r758_1_a_parameter_handed_bare_to_an_array_formal_is_a_slice() {
    let input = format!("{ALLOW}{MATCHES}");
    let table = decisions(&input);
    assert!(
        is_slice(decision(&table, "FindAll::matches")),
        "{:?}",
        decision(&table, "FindAll::matches")
    );
    let source = emitted_census(&input);
    assert!(
        !source.contains("from_mut(matches)"),
        "no one-element view of the forwarder:\n{source}"
    );
}

/// **Narrowing 2 (b), read on the settled table (main 170, restated main 173a).**
/// In the open world nothing owns an unseen entry's surface. Where the formal
/// it hands on to stays RAW, a slice buys no view and only changes the
/// signature external callers call, so the entry keeps its thin form: wave-6v's
/// two `slerp` witnesses pin that half. Where the formal is a SLICE (`FindAll`
/// → `AddMatch`), the thin form would be the one-element view, and the rule
/// gives the entry the fat twin: this witness.
#[test]
fn r808_5_the_open_world_keeps_an_unseen_entrys_signature() {
    let source = emitted(&format!("{ALLOW}{MATCHES}"));
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("matches:&mut[u32])->i32") && !source.contains("from_mut(matches)"),
        "an entry handing on to a slice formal takes the fat twin:\n{source}"
    );
}

/// brotli `ReadSymbol::table` → `DecodeSymbol(.., from_ref(table), ..)`: the
/// LOCAL form of the same shape.
const TABLE: &str = r#"
unsafe fn DecodeSymbol(bits: u32, table: *const u16) -> u16 {
    *table.offset((bits & 0xff) as isize)
}
pub unsafe fn ReadSymbol(tables: *const u16, bits: u32) -> u16 {
    let mut table: *const u16 = tables;
    DecodeSymbol(bits, table)
}
pub unsafe fn entry(bits: u32) -> u16 {
    let t: [u16; 256] = [1; 256];
    ReadSymbol(t.as_ptr(), bits)
}
"#;

#[test]
fn r758_1_a_local_handed_bare_to_an_array_formal_is_a_slice() {
    let input = format!("{ALLOW}{TABLE}");
    let table = decisions(&input);
    assert!(
        is_slice(decision(&table, "ReadSymbol::table")),
        "{:?}",
        decision(&table, "ReadSymbol::table")
    );
    let source = emitted(&input);
    assert!(
        !source.contains("from_ref(table)"),
        "no one-element view of the local:\n{source}"
    );
}

/// wave-6a 135 F3 / F4 (`agents/artifacts/2026-10-02-wave-6a-135/f3_f4_indent_newline.rs`):
/// json.h `json_write_pretty_value::{indent, newline}`, whose callers replace a
/// NULL before the call and whose callee walks them to the NUL.
const JSON_H: &str = r#"
pub unsafe extern "C" fn json_write_pretty_array(
    mut depth: usize,
    mut indent: *const i8,
    mut newline: *const i8,
    mut data: *mut i8,
) -> *mut i8 {
    let mut m = 0 as usize;
    while '\0' as i32 != *indent.offset(m as isize) as i32 {
        *data = *indent.offset(m as isize);
        data = data.offset(1);
        m = m.wrapping_add(1);
    }
    m = 0 as usize;
    while '\0' as i32 != *newline.offset(m as isize) as i32 {
        *data = *newline.offset(m as isize);
        data = data.offset(1);
        m = m.wrapping_add(1);
    }
    if depth > 0 as usize {
        data = json_write_pretty_value(depth.wrapping_sub(1), indent, newline, data);
    }
    return data;
}
pub unsafe extern "C" fn json_write_pretty_value(
    mut depth: usize,
    mut indent: *const i8,
    mut newline: *const i8,
    mut data: *mut i8,
) -> *mut i8 {
    return json_write_pretty_array(depth, indent, newline, data);
}
#[no_mangle]
pub unsafe extern "C" fn json_write_pretty(mut indent: *const i8, mut newline: *const i8, mut data: *mut i8) -> *mut i8 {
    if indent.is_null() {
        indent = b"  \0" as *const u8 as *const i8;
    }
    if newline.is_null() {
        newline = b"\n\0" as *const u8 as *const i8;
    }
    let mut indent_size = 0 as usize;
    while '\0' as i32 != *indent.offset(indent_size as isize) as i32 {
        indent_size = indent_size.wrapping_add(1);
    }
    return json_write_pretty_value(1 as usize, indent, newline, data);
}
"#;

#[test]
fn r758_1_json_h_indent_and_newline_are_not_one_element_views() {
    let input = format!("{ALLOW}{JSON_H}");
    let table = decisions(&input);
    for label in [
        "json_write_pretty_value::indent",
        "json_write_pretty_value::newline",
    ] {
        let decided = decision(&table, label);
        assert!(
            is_slice(decided) || matches!(decided, super::Decision::Degraded(_)),
            "{label}: {decided:?}"
        );
    }
    let source = emitted_census(&input);
    assert!(
        !source.contains("from_ref(indent)") && !source.contains("from_ref(newline)"),
        "no one-element view:\n{source}"
    );
}

/// The control: a thin formal handed to a THIN formal (one element read) stays
/// thin.
#[test]
fn r758_1_a_thin_formal_handed_to_a_thin_formal_stays_thin() {
    let input = format!(
        "{ALLOW}
unsafe fn read1(p: *const u32) -> u32 {{ *p }}
pub unsafe fn fwd(q: *const u32) -> u32 {{ read1(q) }}
pub unsafe fn top() -> u32 {{ let x = 5u32; fwd(&x) }}
"
    );
    let table = decisions(&input);
    assert!(
        matches!(decision(&table, "fwd::q"), super::Decision::Ref { .. }),
        "{:?}",
        decision(&table, "fwd::q")
    );
}

/// R805-7 (relay 272 item 3, the review of wave-5d's `7e95b112f`): the rule
/// asks the same gate as the hold that complements it — the subject's own
/// (`enabled_for`), not its owner's. A subject whose slice stage alone is
/// withdrawn (an exclusion re-derivation's subject-scoped transaction) is not
/// made fat by the rule; the hold takes it.
#[test]
fn r805_7_the_rule_respects_a_subject_scoped_withdrawal_of_the_slice_stage() {
    use crate::bo_rewriter::additive::{FamilyPolicy, FamilyStage};
    let input = format!("{ALLOW}{MATCHES}");
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).unwrap();
        let functions = tcx
            .hir_body_owners()
            .filter(|d| matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let program = crate::bo_rewriter::collect_program(tcx);
        let fat = crate::bo_rewriter::fat_facts::FatFacts::from_program(&program);
        let (subject, _) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == "FindAll::matches")
            .expect("FindAll::matches");
        let open = FamilyPolicy::at(FamilyStage::SliceUse);
        assert!(super::slice_input::hands_on_to_fat(
            subject, &facts, &fat, &open
        ));
        let mut withdrawn = FamilyPolicy::at(FamilyStage::SliceUse);
        withdrawn.withdrawn_subjects.insert((
            FamilyStage::SliceUse,
            crate::bo_rewriter::bridge_receipt::SignatureClassId::of(subject.fn_did),
            subject.hir_id.local_id.as_u32(),
        ));
        assert!(!super::slice_input::hands_on_to_fat(
            subject, &facts, &fat, &withdrawn
        ));
    })
    .unwrap();
}

/// **R802-6's restore hold, narrowed (relay 273 R807-1, relay 275; main 170a).**
/// The hold is in scope only where the hand-on renders a one-element view: the
/// callee formal is delivered fat. p55b measured three subjects it moved into
/// formals that stay raw (binn `binn_map_get_pair::value`,
/// `binn_object_get_pair::value`, lodepng `auto_choose_color::mode_out`).
const MID: &str = r#"
unsafe fn reads(p: *const i32) -> i32 { *p.offset(1) }
unsafe fn mid(x: *const i32) -> i32 { reads(x) }
pub unsafe fn top() -> i32 { let a: [i32; 2] = [1, 2]; mid(a.as_ptr()) }
"#;

#[test]
fn r808_6_the_restore_hold_releases_a_subject_whose_formal_is_not_fat() {
    use super::local_callee_extent::{AccessReason, LocalCalleeAccess};
    let input = format!("{ALLOW}{MID}");
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).unwrap();
        let mut entries = table.entries.clone();
        let at = |label: &str| {
            entries
                .iter()
                .position(|(subject, _)| subject.label == label)
                .unwrap_or_else(|| panic!("{label}"))
        };
        let (mid, reads) = (at("mid::x"), at("reads::p"));
        let held =
            |entries: &[(super::Subject, super::Decision)], subject: usize, formal: usize| {
                super::degrade(
                    &entries[subject].0,
                    "test".into(),
                    super::DegradeReason::LocalCalleeAccessExtent {
                        access: Box::new(LocalCalleeAccess {
                            callee_id: entries[formal].0.fn_did,
                            parameter_index: 0,
                            callee: "reads".into(),
                            parameter: "p".into(),
                            access: "read",
                            reason: AccessReason::PointerArithmetic {
                                op: super::RESTORE_HOLD_OP.into(),
                            },
                            footprint_bytes: None,
                        }),
                        count: None,
                    },
                )
            };
        entries[mid].1 = held(&entries, mid, reads);
        let key = (entries[mid].0.fn_did, entries[mid].0.hir_id);
        assert!(
            is_slice(&entries[reads].1),
            "the formal is delivered fat: {:?}",
            entries[reads].1
        );
        assert!(
            super::restore_holds_to_release(&entries).is_empty(),
            "a fat formal keeps the hold"
        );
        entries[reads].1 = super::degrade(
            &entries[reads].0,
            "test".into(),
            super::DegradeReason::KindRaw,
        );
        assert!(
            super::restore_holds_to_release(&entries).contains(&key),
            "a raw formal releases it"
        );
        entries[reads].1 = super::Decision::Ref { mutable: false };
        assert!(
            super::restore_holds_to_release(&entries).contains(&key),
            "a thin formal releases it"
        );
    })
    .unwrap();
}
