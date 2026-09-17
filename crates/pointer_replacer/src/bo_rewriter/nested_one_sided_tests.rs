//! N1 (nested lane, R436-1) — the per-parameter inner-construction
//! substitution. A depth-2 table whose inner level is Ref is delivered on its
//! own when every use of it is an admitted leading row load; a sibling table
//! that does not qualify keeps exactly the form the frame already gives it.

use std::sync::OnceLock;

use super::{
    A5Mode, SlotKind, SlotRef, WholeProgramAttestation,
    decision::{Decision, nested_slice::Hold},
};

#[allow(dead_code, unused_assignments, unused_mut)]
#[path = "nested_one_sided_fixture.rs"]
mod original;

const SOURCE: &str = include_str!("nested_one_sided_fixture.rs");
const BOTH: &str = "indicators::ema::ti_ema";
const LATE: &str = "indicators::ema_late_out::ti_ema_late_out";
const EXTRA: &str = "indicators::ema_extra_use::ti_ema_extra_use";
/// wave-5d's pair fixture, read (never edited) as this lane's no-shadow control.
const PAIR_SOURCE: &str = include_str!("wave5d_ti_abs.rs");

fn emitted() -> &'static str {
    static SOURCE_AFTER: OnceLock<String> = OnceLock::new();
    SOURCE_AFTER.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("crat-nested-n1-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("lib.rs");
        std::fs::write(&root, SOURCE).unwrap();
        let outcome = super::rewrite_m1_path_a5_injected(
            &root,
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &|_| {},
        );
        std::fs::remove_dir_all(&dir).unwrap();
        let super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } = outcome
        else {
            panic!("N1 emission unavailable; compiler diagnostics precede this assertion");
        };
        assert_eq!(reverted_count, 0);
        println!("N1-EMITTED\n{source}\nN1-END");
        source
    })
}

fn decisions(name: &str) -> Vec<(String, Decision)> {
    let mut out = Vec::new();
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        for (s, decision) in &table.entries {
            if tcx.def_path_str(s.fn_did.to_def_id()) == name
                && let Some(parameter) = s.param_name.clone()
            {
                out.push((parameter, decision.clone()));
            }
        }
    })
    .unwrap();
    out
}

fn table_decision(name: &str, parameter: &str) -> Decision {
    decisions(name)
        .into_iter()
        .find(|(p, _)| p == parameter)
        .unwrap_or_else(|| panic!("{name}::{parameter} subject"))
        .1
}

/// **W-N1-FRAME** — every premise N1 consumes, pinned at the frame: both depth
/// levels are Ref, both tables are already delivered immutable flat slices,
/// both inner constructions are planned with a FABRICATED extent, and the pair
/// rule cannot reach this body. If any of these moves, N1's market moved.
#[test]
fn n1_frame_premises_are_exactly_what_the_rule_consumes() {
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut tables = 0;
        for (s, decision) in &table.entries {
            if tcx.def_path_str(s.fn_did.to_def_id()) != BOTH || s.ptr_depth != 2 {
                continue;
            }
            for depth in 0..2 {
                let slot = ctx.slots.fn_local_slots[&s.fn_did]
                    .slot_for_local_depth(s.local, depth)
                    .unwrap();
                assert_eq!(
                    ctx.model.get(&SlotRef::Local(s.fn_did, slot)),
                    Some(&SlotKind::Ref),
                    "{:?} depth={depth}: no injected model kinds",
                    s.param_name
                );
            }
            assert!(
                matches!(
                    decision,
                    Decision::Slice { mutable: false, .. } | Decision::NestedSlice { .. }
                ),
                "{decision:?}"
            );
            tables += 1;
        }
        assert_eq!(tables, 2);
        let constructions = table
            .slice_constructions
            .iter()
            .filter(|c| tcx.def_path_str(c.node.0.to_def_id()) == BOTH)
            .collect::<Vec<_>>();
        assert_eq!(constructions.len(), 2, "one inner row per table");
        for c in constructions {
            assert!(c.hold_reason.is_none() && c.replacement.is_some() && !c.nullable);
            assert!(
                c.length.is_fallback(),
                "the relocated extent is the fabricated one: {:?}",
                c.length
            );
        }
    })
    .unwrap();
}

/// **W-N1-DELIVERS** — the pair rule holds this body (it is a lookback
/// indicator, not the elementwise pattern) and N1 still delivers both tables'
/// inner levels.
#[test]
fn n1_delivers_every_qualifying_table_where_the_pair_rule_holds() {
    for parameter in ["inputs", "outputs"] {
        let decision = table_decision(BOTH, parameter);
        assert!(
            matches!(decision, Decision::NestedSlice { .. }),
            "{parameter} must deliver its inner level: {decision:?}"
        );
    }
}

/// **W-N1-LEADING** — clause (d). The output table's row load sits after an
/// early return, so relocating it would move a read across a branch: that
/// table keeps its frame form while the input table still delivers.
#[test]
fn n1_skips_a_table_whose_row_load_is_not_leading() {
    assert!(
        matches!(table_decision(LATE, "inputs"), Decision::NestedSlice { .. }),
        "the qualifying sibling still delivers"
    );
    let outputs = table_decision(LATE, "outputs");
    assert!(
        matches!(outputs, Decision::Slice { .. }),
        "a non-leading load keeps its frame form, unchanged: {outputs:?}"
    );
}

/// **W-N1-ALL-USES** — clause (b). The output table is read a second time
/// after the loop; that use is not an admitted row load, so the table is not
/// re-typed and its second read still sees the original pointer storage.
#[test]
fn n1_skips_a_table_with_a_use_that_is_not_a_row_load() {
    assert!(
        matches!(
            table_decision(EXTRA, "inputs"),
            Decision::NestedSlice { .. }
        ),
        "the qualifying sibling still delivers"
    );
    let outputs = table_decision(EXTRA, "outputs");
    assert!(
        matches!(outputs, Decision::Slice { .. }),
        "a table with a further use keeps its frame form: {outputs:?}"
    );
}

/// **W-N1-EMISSION** — the wrapper builds an exact descriptor array from the
/// raw table and the safe helper takes the nested form; the inner
/// constructions become reborrows of the elements, the mutable one explicitly.
#[test]
fn n1_emits_the_descriptor_array_and_the_nested_helper_signature() {
    let source = emitted();
    assert!(
        source.contains("inputs: &[&[std::os::raw::c_double]]"),
        "shared nested input table"
    );
    assert!(
        source.contains("outputs: &mut [&mut [std::os::raw::c_double]]"),
        "mutable nested output table"
    );
    assert!(
        source.contains("let __crat_nested_33_raw = *inputs.add(0);"),
        "the table cell is loaded in the wrapper"
    );
    assert!(
        source.contains(
            "let __crat_nested_33_view =\n        ::core::slice::from_raw_parts(__crat_nested_33_raw,\n            crate::FALLBACK_SLICE_EXTENT);"
        ) || source.contains("::core::slice::from_raw_parts(__crat_nested_33_raw,"),
        "the row view is built in the wrapper"
    );
    assert!(
        source.contains("let __crat_nested_4_rows = [__crat_nested_33_view];"),
        "an exact one-element descriptor array, not a fabricated table extent"
    );
    assert!(
        source.contains("__crat_safe_ti_ema(size, &__crat_nested_4_rows,")
            && source.contains("&mut __crat_nested_8_rows)"),
        "the wrapper passes borrows of the descriptor arrays"
    );
    assert!(
        source.contains("let mut input: &[std::os::raw::c_double] = inputs[0];"),
        "the shared row is a plain reborrow of the element"
    );
    assert!(
        source.contains("&mut *outputs[0]"),
        "the mutable row is an EXPLICIT reborrow, never a move out of borrowed storage"
    );
}

/// **W-N1-NO-GUARD** — N1 must not emit the pair rule's non-positive-count
/// early return: the helper it leaves behind still has its own early returns
/// and a `size <= 0` call must still reach them.
#[test]
fn n1_does_not_emit_a_count_guard() {
    let source = emitted();
    let wrapper = source
        .split("pub unsafe extern \"C\" fn ti_ema(")
        .nth(1)
        .expect("ti_ema wrapper")
        .split("pub unsafe extern \"C\" fn __crat_safe_ti_ema(")
        .next()
        .expect("wrapper body");
    assert!(
        !wrapper.contains("if size <= 0"),
        "no count guard belongs in an N1 wrapper:\n{wrapper}"
    );
    assert!(
        !wrapper.contains("__crat_nested_count"),
        "no shared count binding belongs in an N1 wrapper:\n{wrapper}"
    );
    assert!(
        source.contains("if period < 1 as std::os::raw::c_int"),
        "the helper keeps its own early return"
    );
}

/// **W-N1-EXTENT** — the fabricated extent is RELOCATED, not removed and not
/// duplicated: one fabricated inner length per row, still receipted, and the
/// wrapper's own table extent is now an exact array.
#[test]
fn n1_relocates_the_fabricated_extent_without_adding_one() {
    let source = emitted();
    let region = source
        .split("pub unsafe extern \"C\" fn ti_ema(")
        .nth(1)
        .expect("ti_ema")
        .split("pub mod ema_late_out")
        .next()
        .expect("ti_ema region");
    // The two inner rows keep their fabricated extent, relocated; the third is
    // the `options` table, a depth-1 subject this arm does not touch.
    assert_eq!(
        region.matches("crate::FALLBACK_SLICE_EXTENT").count(),
        3,
        "{region}"
    );
    assert_eq!(
        region.matches("__crat_nested_").filter(|_| true).count(),
        12,
        "two rows: raw, view, array, and the two argument sites:\n{region}"
    );
    // The OUTER fabricated table extents are gone: the wrapper now builds an
    // exact descriptor array instead of a 1024-element view of the C table.
    assert!(
        !region.contains("from_raw_parts(inputs,") && !region.contains("from_raw_parts(outputs,"),
        "no fabricated outer table extent may survive:\n{region}"
    );
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        for c in &table.slice_constructions {
            if tcx.def_path_str(c.node.0.to_def_id()) != BOTH {
                continue;
            }
            assert_eq!(
                c.initializer_kind, "nested-reborrow-relocated-fallback",
                "the relocated arm is named in the receipt"
            );
            assert!(
                c.length.is_fallback(),
                "N1 does not re-source a length it only moved: {:?}",
                c.length
            );
        }
        let plan = table
            .nested_receipts
            .iter()
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == BOTH)
            .and_then(|r| r.result.as_ref().ok())
            .expect("an admitted N1 plan");
        assert!(!plan.count_guard);
        assert!(plan.rows.iter().all(|r| r.was_fallback));
        assert!(
            plan.rows
                .iter()
                .all(|r| r.length == "crate::FALLBACK_SLICE_EXTENT")
        );
    })
    .unwrap();
}

/// **W-N1-PAIR-UNMOVED** — the pair rule still leads. Where it admits, its
/// plan is the one that ships (guarded, count-bound); N1 never shadows it.
#[test]
fn n1_never_shadows_an_admitted_pair_plan() {
    ::utils::compilation::run_compiler_on_str(PAIR_SOURCE, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let plan = table
            .nested_receipts
            .iter()
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == "indicators::abs::ti_abs")
            .and_then(|r| r.result.as_ref().ok())
            .expect("the pair rule still admits ti_abs");
        assert!(plan.count_guard, "the pair plan keeps its count guard");
        assert!(
            plan.rows.iter().all(|r| r.length == "__crat_nested_count"),
            "the pair plan keeps its evidence-backed count"
        );
    })
    .unwrap();
}

/// The typed hold vocabulary this arm may report is the pair rule's; N1 adds
/// no new one, so a held owner's census row cannot move because of this lane.
#[test]
fn n1_reports_no_new_hold_vocabulary() {
    let holds = [
        Hold::OuterNotDelivered,
        Hold::InnerNotRef,
        Hold::StorageUnproved,
        Hold::PairRequired,
        Hold::IntervalChanged,
        Hold::CountRelationUnproved,
        Hold::NullableLevelUnbuilt,
        Hold::RawBoundaryUnbuilt,
        Hold::DirectCallerUnbuilt,
        Hold::DeclarationUnbuilt,
    ];
    assert_eq!(holds.len(), 10);
}
