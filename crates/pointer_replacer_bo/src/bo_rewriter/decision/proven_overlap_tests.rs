//! R808-5 / R810-2 (F2) and R819-1 item 4: the proven-overlap formal pairs, read
//! from the call facts alone.

const SAME_POINTER: &str = include_str!("../testdata/r819_same_pointer_two_positions.rs");

/// The proven pairs as `(callee name, inner, outer)`.
fn pairs(input: &str) -> Vec<(String, usize, usize)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).expect("native decisions");
        let subjects = table
            .entries
            .iter()
            .map(|(subject, _)| subject.clone())
            .collect::<Vec<_>>();
        let functions = tcx
            .hir_body_owners()
            .filter(|owner| matches!(tcx.def_kind(*owner), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let (proven, callees) = super::co_conversion::proven_overlaps(&facts, &subjects);
        proven
            .into_iter()
            .map(|(callee, inner, outer)| {
                (
                    tcx.item_name(callees[&callee].to_def_id()).to_string(),
                    inner,
                    outer,
                )
            })
            .collect()
    })
    .expect("input type-checks")
}

/// `zmod(a, a, d)`: the same pointer at positions 0 and 1 is a proven overlap
/// of `zmod`'s first two formals (both ways); `zmodpow`'s three distinct
/// formals prove nothing.
#[test]
fn r819_4_the_same_pointer_at_two_positions_is_a_proven_overlap() {
    let proven = pairs(SAME_POINTER);
    assert!(proven.contains(&("zmod".to_owned(), 1, 0)), "{proven:?}");
    assert!(proven.contains(&("zmod".to_owned(), 0, 1)), "{proven:?}");
    assert!(
        !proven
            .iter()
            .any(|(callee, i, o)| callee == "zmod" && (*i == 2 || *o == 2)),
        "{proven:?}"
    );
}

/// `zcmp(b, b)` is a proven overlap too; whether it blocks is the written
/// condition's (a callee that only reads both keeps its shared references,
/// `r819_4_control_…` in the census-world tests).
#[test]
fn r819_4_the_same_pointer_read_twice_is_proven_and_left_to_the_written_condition() {
    let proven = pairs(SAME_POINTER);
    assert!(proven.contains(&("zcmp".to_owned(), 1, 0)), "{proven:?}");
}

const CONTAINMENT: &str = include_str!("../testdata/r866_containment.rs");

/// R866-1 (fan-out 083): `safe_read(&mut *s, &mut *br)` with `br = &mut
/// (*s).br`: the reborrow `&mut *s` is `s` itself, and `br` lies inside `s`'s
/// referent, so `br` (position 1) is a proven overlap of `s` (position 0).
#[test]
fn r866_1_a_field_inside_the_other_reborrowed_argument_is_a_proven_overlap() {
    let proven = pairs(CONTAINMENT);
    assert!(
        proven.contains(&("safe_read".to_owned(), 1, 0)),
        "{proven:?}"
    );
}

/// The direct spelling `safe_read2(&mut *s, &mut (*s).br)`.
#[test]
fn r866_1_the_fields_address_beside_the_objects_reborrow_is_a_proven_overlap() {
    let proven = pairs(CONTAINMENT);
    assert!(
        proven.contains(&("safe_read2".to_owned(), 1, 0)),
        "{proven:?}"
    );
}

/// The substrate's spelling `safe_read4(s, br)` was F2's already.
#[test]
fn r866_1_the_substrate_spelling_is_a_proven_overlap() {
    let proven = pairs(CONTAINMENT);
    assert!(
        proven.contains(&("safe_read4".to_owned(), 1, 0)),
        "{proven:?}"
    );
}

/// Control: two distinct locals' addresses prove nothing.
#[test]
fn r866_1_control_two_distinct_locals_prove_nothing() {
    let proven = pairs(CONTAINMENT);
    assert!(
        !proven.iter().any(|(callee, _, _)| callee == "safe_read3"),
        "{proven:?}"
    );
}
