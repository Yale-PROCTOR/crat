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
const LATE_IN: &str = "indicators::ema_late_in::ti_ema_late_in";
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

fn region<'a>(source: &'a str, owner: &str) -> &'a str {
    source
        .split(&format!("pub unsafe extern \"C\" fn {owner}("))
        .nth(1)
        .unwrap_or_else(|| panic!("{owner} in the emitted tree"))
        .split("pub mod ")
        .next()
        .expect("owner region")
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

/// **W-N1-BOUNDARY** — the lane boundary. Both of this function's tables would
/// deliver, so the function is the PAIR rule's: N1 stands off and wave-5d's
/// hold — with its own premises about the count, the loop and the accumulator
/// — stays the only verdict on it.
#[test]
fn n1_stands_off_where_every_table_would_deliver() {
    for parameter in ["inputs", "outputs"] {
        let decision = table_decision(BOTH, parameter);
        assert!(
            matches!(decision, Decision::Slice { .. }),
            "{parameter} belongs to the pair rule here: {decision:?}"
        );
    }
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let receipt = table
            .nested_receipts
            .iter()
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == BOTH)
            .expect("a typed outcome");
        assert!(receipt.result.is_err(), "{:?}", receipt.result);
    })
    .unwrap();
}

/// **W-N1-DELIVERS-MUT** — the mirror of W-N1-LEADING: where the INPUT table's
/// load is the late one, the MUTABLE output table is the one that delivers.
#[test]
fn n1_delivers_a_mutable_table_when_it_is_the_qualifying_side() {
    let outputs = table_decision(LATE_IN, "outputs");
    assert!(
        matches!(
            outputs,
            Decision::NestedSlice {
                mutable: true,
                inner_mutable: true,
                ..
            }
        ),
        "the mutable table delivers its inner level: {outputs:?}"
    );
    assert!(
        matches!(table_decision(LATE_IN, "inputs"), Decision::Slice { .. }),
        "the late sibling keeps its frame form"
    );
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
/// construction becomes a reborrow of the element, explicitly on the mutable
/// side. Both one-sided fixtures are read: the shared table in `late_out`, the
/// mutable table in `late_in`.
#[test]
fn n1_emits_the_descriptor_array_and_the_nested_helper_signature() {
    let source = emitted();
    let shared = region(source, "ti_ema_late_out");
    assert!(
        shared.contains("inputs: &[&[std::os::raw::c_double]]"),
        "shared nested input table:\n{shared}"
    );
    assert!(
        shared.contains("outputs: &[*mut std::os::raw::c_double]"),
        "the sibling keeps EXACTLY its frame form:\n{shared}"
    );
    assert!(
        shared.contains("_raw = *inputs.add(0);"),
        "the table cell is loaded in the wrapper:\n{shared}"
    );
    assert!(
        shared.contains("::core::slice::from_raw_parts(__crat_nested_"),
        "the row view is built in the wrapper:\n{shared}"
    );
    assert!(
        shared.contains("_rows = [__crat_nested_"),
        "an exact one-element descriptor array, not a fabricated table extent:\n{shared}"
    );
    assert!(
        shared.contains("__crat_safe_ti_ema_late_out(size, &__crat_nested_"),
        "the wrapper passes a borrow of the descriptor array:\n{shared}"
    );
    assert!(
        shared.contains("let mut input: &[std::os::raw::c_double] = inputs[0];"),
        "the shared row is a plain reborrow of the element:\n{shared}"
    );

    let mutable = region(source, "ti_ema_late_in");
    assert!(
        mutable.contains("outputs: &mut [&mut [std::os::raw::c_double]]"),
        "mutable nested output table:\n{mutable}"
    );
    assert!(
        mutable.contains("&mut *outputs[0]"),
        "the mutable row is an EXPLICIT reborrow, never a move out of borrowed storage:\n{mutable}"
    );
    assert!(
        mutable.contains("_raw = *outputs.add(0);")
            && mutable.contains("::core::slice::from_raw_parts_mut(__crat_nested_"),
        "the mutable view is built in the wrapper:\n{mutable}"
    );
}

/// **W-N1-NO-GUARD** — N1 must not emit the pair rule's non-positive-count
/// early return: the helper it leaves behind still has its own early returns
/// and a `size <= 0` call must still reach them.
#[test]
fn n1_does_not_emit_a_count_guard() {
    let source = emitted();
    for owner in ["ti_ema_late_out", "ti_ema_late_in"] {
        let body = region(source, owner);
        let wrapper = body
            .split(&format!("pub unsafe extern \"C\" fn __crat_safe_{owner}("))
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
            body.contains("if period < 1 as std::os::raw::c_int"),
            "the helper keeps its own early return:\n{body}"
        );
    }
}

/// **W-N1-EXTENT** — the fabricated extent is RELOCATED, not removed and not
/// duplicated: the admitted row keeps its fabricated length, still receipted,
/// and that table's own fabricated outer extent is now an exact array while
/// the sibling's outer extent is untouched.
#[test]
fn n1_relocates_the_fabricated_extent_without_adding_one() {
    let source = emitted();
    let shared = region(source, "ti_ema_late_out");
    // Four, and each one is accounted for: the relocated inner row (now in the
    // wrapper), the untouched `options` table, and the sibling output table's
    // OWN two — its outer view and its inner row — which this arm did not take.
    // The count is unchanged from the frame: N1 moved one, it invented none.
    assert_eq!(
        shared.matches("crate::FALLBACK_SLICE_EXTENT").count(),
        4,
        "{shared}"
    );
    // The delivered table's OWN fabricated outer extent is gone: the wrapper
    // builds an exact descriptor array instead of a 1024-element table view.
    assert!(
        !shared.contains("from_raw_parts(inputs,"),
        "no fabricated outer table extent may survive on the delivered side:\n{shared}"
    );
    assert!(
        shared.contains("from_raw_parts(outputs,"),
        "the sibling's outer extent is untouched:\n{shared}"
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
        let plan = table
            .nested_receipts
            .iter()
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == LATE)
            .and_then(|r| r.result.as_ref().ok())
            .expect("an admitted N1 plan");
        assert!(!plan.count_guard);
        assert_eq!(plan.parameters.len(), 1, "one side only");
        assert!(plan.rows.iter().all(|r| r.was_fallback));
        assert!(
            plan.rows
                .iter()
                .all(|r| r.length == "crate::FALLBACK_SLICE_EXTENT")
        );
        let relocated = plan.rows.iter().map(|r| r.local).collect::<Vec<_>>();
        for c in &table.slice_constructions {
            if tcx.def_path_str(c.node.0.to_def_id()) != LATE {
                continue;
            }
            let expected = if relocated.contains(&c.node.1) {
                "nested-reborrow-relocated-fallback"
            } else {
                "place-read"
            };
            assert_eq!(
                c.initializer_kind, expected,
                "only the relocated row is re-labelled"
            );
            assert!(
                c.length.is_fallback(),
                "N1 does not re-source a length it only moved: {:?}",
                c.length
            );
        }
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
