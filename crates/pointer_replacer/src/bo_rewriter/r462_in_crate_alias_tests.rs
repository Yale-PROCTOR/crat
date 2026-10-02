//! Wave-6o (relay 112, R672 / R462-1 (2)): the exported-entry waiver covers
//! the EXTERNAL caller only. An in-crate call that passes the same pointer at
//! both positions of an exported entry's pair is evidence, and refuses the
//! `&mut` / `&mut` pair. The shape is libzahl's `zcmp(a, a)` from its own
//! provided test (`test.c:119`), which R672 joins to the crate as `main_0`:
//! `zcmp` writes through both operands (`zcmpmag` trims `used`), so a shared
//! pair is not available either.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

fn decisions(input: &str, function: &str) -> Vec<(String, Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let mut out: Vec<(String, Decision)> = table
            .entries
            .iter()
            .filter(|(subject, _)| tcx.item_name(subject.fn_did.to_def_id()).as_str() == function)
            .filter_map(|(subject, decision)| Some((subject.param_name.clone()?, decision.clone())))
            .collect();
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
    })
    .expect("fixture compiler context")
}

const INPUT: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, non_camel_case_types)]
#[repr(C)] pub struct Z { pub sign: i32, pub used: usize }
#[no_mangle]
pub unsafe extern "C" fn zcmpmag(mut a: *mut Z, mut b: *mut Z) -> i32 {
    while (*a).used > (*b).used { (*a).used = (*a).used.wrapping_sub(1); }
    while (*b).used > (*a).used { (*b).used = (*b).used.wrapping_sub(1); }
    return 0 as i32;
}
#[no_mangle]
pub unsafe extern "C" fn zcmp(mut a: *mut Z, mut b: *mut Z) -> i32 {
    if (*a).sign != (*b).sign { return (*a).sign - (*b).sign; }
    return (*a).sign * zcmpmag(a, b);
}
pub unsafe fn main_0() -> i32 {
    let mut x: Z = Z { sign: 1, used: 2 };
    let mut y: Z = Z { sign: 1, used: 3 };
    let mut r: i32 = zcmp(&mut x, &mut y);
    r += zcmp(&mut x, &mut x);
    return r;
}
"#;

fn both_mut_refs(ds: &[(String, Decision)]) -> bool {
    ds.iter().filter(|(n, _)| n == "a" || n == "b").count() == 2
        && ds
            .iter()
            .filter(|(n, _)| n == "a" || n == "b")
            .all(|(_, d)| matches!(d, Decision::Ref { .. } | Decision::Opt { .. }))
}

/// `zcmp(&mut x, &mut x)` in-crate refuses the pair: the emitted entry is not
/// `&mut Z` / `&mut Z`, and the emitted program still type-checks.
#[test]
fn wave6o_in_crate_aliased_call_refuses_the_exported_pair() {
    assert!(verify::type_checks_str(INPUT));
    let ds = decisions(INPUT, "zcmp");
    assert!(
        !both_mut_refs(&ds),
        "an in-crate aliased call refuses the pair: {ds:?}"
    );
    let output = ast_emitted_source_of(INPUT).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(!flat.contains("fnzcmp(muta:&mutZ,mutb:&mutZ)"), "{output}");
    eprintln!("WAVE6O_R462_ALIAS_OUTPUT_BEGIN\n{output}\nWAVE6O_R462_ALIAS_OUTPUT_END");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: with distinct arguments only, the pair is certified under the
/// waiver (external callers) plus the in-crate evidence, and stays `&mut`.
#[test]
fn wave6o_in_crate_distinct_calls_keep_the_exported_pair() {
    let input = INPUT.replace("    r += zcmp(&mut x, &mut x);\n", "");
    assert!(verify::type_checks_str(&input));
    let ds = decisions(&input, "zcmp");
    assert!(
        both_mut_refs(&ds),
        "distinct in-crate arguments keep the pair: {ds:?}"
    );
}
