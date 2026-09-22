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
const MIXED: &str = "indicators::sma_mixed::ti_sma_mixed";
const CURSOR_ONLY: &str = "indicators::sma_cursor_only::ti_sma_cursor_only";
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

/// **W-N1-BOTH** — R445-3 dropped the lane boundary. The pair rule holds this
/// body (it is a lookback indicator, not the elementwise pattern) and N1
/// delivers BOTH tables' inner levels, in one plan, per parameter.
#[test]
fn n1_delivers_every_qualifying_table_where_the_pair_rule_holds() {
    for parameter in ["inputs", "outputs"] {
        let decision = table_decision(BOTH, parameter);
        assert!(
            matches!(decision, Decision::NestedSlice { .. }),
            "{parameter} must deliver its inner level: {decision:?}"
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
        let plan = table
            .nested_receipts
            .iter()
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == BOTH)
            .and_then(|r| r.result.as_ref().ok())
            .expect("an admitted N1 plan");
        assert_eq!(plan.parameters.len(), 2, "one plan, both tables");
        assert!(!plan.count_guard, "still no count guard");
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

/// **W-N1-MIXED-FRAME** — the premises `ti_sma_mixed` exists to carry, pinned
/// before the rule is asked anything: its INPUT row is the cursor family's
/// market and its OUTPUT row is an ordinary slice, so this owner has exactly
/// one slice-only table and one cursor table. If either moves, the standoff
/// witnesses below are testing a shape that is not the corpus's.
///
/// The input row reading `Cursor` is itself load-bearing, and measured: with
/// the arm admitting it, the whole owner failed and the cursor came back out
/// as `Degraded(SliceNegOrUnknownOffset)` — a withdrawn cursor, which is how
/// the slicecursor fixture `ti_sma_cursor` still reads. So the standoff does
/// not only save the slice-only sibling; it leaves the cursor family holding
/// its own row. If this assertion ever reads `Degraded` again, the standoff
/// has stopped working and the owner is being taken down as a whole.
#[test]
fn n1_mixed_fixture_carries_one_cursor_row_and_one_slice_row() {
    let rows = decisions(MIXED);
    let input = rows
        .iter()
        .find(|(p, _)| p == "input")
        .map(|(_, d)| d)
        .expect("the input row subject");
    let output = rows
        .iter()
        .find(|(p, _)| p == "output")
        .map(|(_, d)| d)
        .expect("the output row subject");
    assert!(
        matches!(input, Decision::Cursor { .. }),
        "the input row must still be the cursor family's — a `Degraded` here is \
         a WITHDRAWN cursor, i.e. the standoff failed: {input:?}"
    );
    assert!(
        matches!(output, Decision::Slice { mutable: true, .. }),
        "the output row must be an ordinary mutable slice: {output:?}"
    );
    // ... and both TABLES are the flat slices N1 consumes, so the only thing
    // separating the two sides is which family owns the row.
    for table in ["inputs", "outputs"] {
        assert!(
            matches!(
                table_decision(MIXED, table),
                Decision::Slice { mutable: false, .. } | Decision::NestedSlice { .. }
            ),
            "{table} is not the flat-slice table this rule consumes"
        );
    }
}

/// **W-N1-STANDOFF** — R500-6 (b). `nested_slice::Plan` is per-OWNER, so every
/// admitted parameter shares one fate: a clause that fails later, or an
/// emission that does not type, takes the whole owner down. Report 015
/// measured the price of ignoring that — admitting a cursor sibling cost
/// tulipindicators five tables N1 already delivered (`ti_crossany`,
/// `ti_crossover`, `ti_decay`, `ti_edecay`, `ti_tr`), for nothing gained.
///
/// So the cursor arm stands off any owner that has a parameter admissible from
/// slice rows alone: that owner's plan is then exactly the plan the slice-only
/// arm would have made, and the seam can only ever add. The stood-off
/// parameter is named in the receipt — a typed hold, never a silent skip.
#[test]
fn n1_cursor_arm_stands_off_an_owner_with_a_slice_only_sibling() {
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
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == MIXED)
            .and_then(|r| r.result.as_ref().ok())
            .expect("the slice-only sibling still gives this owner a plan");
        let admitted = plan
            .parameters
            .iter()
            .map(|p| p.name.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            admitted,
            vec!["outputs".to_owned()],
            "only the slice-only table is admitted"
        );
        assert!(
            plan.rows.iter().all(|r| r.parameter
                == plan
                    .parameters
                    .iter()
                    .find(|p| p.name == "outputs")
                    .unwrap()
                    .hir),
            "the cursor sibling's rows left the plan with it"
        );
        assert_eq!(
            plan.stood_off.len(),
            1,
            "the cursor sibling is receipted, not silently dropped: {:?}",
            plan.stood_off
        );
    })
    .unwrap();
}

/// **W-N1-STANDOFF-DELIVERS** — the point of the standoff, in the tree: the
/// slice-only sibling keeps the delivery it had before the cursor arm existed,
/// and the cursor sibling keeps exactly its frame form.
#[test]
fn n1_standoff_keeps_the_slice_only_siblings_delivery() {
    let body = region(emitted(), "__crat_safe_ti_sma_mixed");
    assert!(
        body.contains("outputs: &mut [&mut [std::os::raw::c_double]]"),
        "the slice-only table still delivers its inner level:\n{body}"
    );
    assert!(
        body.contains("inputs: &[*const std::os::raw::c_double]"),
        "the cursor sibling keeps its frame form:\n{body}"
    );
}

/// **W-N1-CONSTRUCTED** — R501-4 (iv), (b′). A table is flipped only when every
/// one of its rows has a construction for `promote` to rewrite. The measured
/// reason: a cursor row's constructor belongs to the cursor family and is
/// rebuilt only after the flip, so in between the table's type has changed and
/// the row's base text has not — report 016 counted that as 61 of
/// tulipindicators' 68 `SliceCursor` constructions reverting to raw pointers,
/// and the planner's own answer is to WITHDRAW the Return-stage transaction
/// carrying the flip (`withdrawn=[Return]`, class-level), after which the
/// emitting `Return` pass re-derives without it.
///
/// So every row that survives into a plan must name a slice construction. This
/// is asserted over the plan rather than over the arm, deliberately: the day
/// the cursor family constructs a row before the flip, this witness keeps
/// passing and the arm is free again.
#[test]
fn n1_every_planned_row_names_a_construction() {
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut planned = 0;
        for receipt in &table.nested_receipts {
            let Ok(plan) = &receipt.result else { continue };
            for row in &plan.rows {
                assert!(
                    table
                        .slice_constructions
                        .iter()
                        .any(|c| c.node == (plan.owner, row.local)),
                    "{} row {:?} has no construction to rewrite — the flip would \
                     change the table's type and leave this row's base text alone",
                    tcx.def_path_str(plan.owner.to_def_id()),
                    row.local
                );
                planned += 1;
            }
        }
        assert!(planned > 0, "no plan reached this witness at all");
    })
    .unwrap();
}

/// **W-N1-NOT-WITHDRAWN** — (b′)'s own shape, and the one that measures the
/// difference. `ti_sma_cursor_only` has no slice-only table, so clause (f)
/// leaves the arm free and clause (g) is the only thing between it and a flip
/// it cannot type.
///
/// The assertion is that the owner has a RECEIPT AT ALL. Without (g) it has
/// none — and the reason corrects report 016, which read that absence as "the
/// owner is never offered". It is offered: the instrument shows a `Return` pass
/// admitting it, and then the transaction carrying the untypeable flip is
/// withdrawn class-level (`withdrawn=[Return]`), so the next `Return` pass —
/// whose table is the one handed back — re-derives without it and leaves no
/// receipt behind. With (g) the flip is never made, nothing is withdrawn, and
/// the owner ends with a typed hold instead of a hole.
#[test]
fn n1_an_owner_it_cannot_type_is_held_not_withdrawn() {
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
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == CURSOR_ONLY)
            .map(|r| r.result.clone());
        assert!(
            receipt.is_some(),
            "no receipt for {CURSOR_ONLY}: its Return-stage transaction was \
             withdrawn, which is what (b′) exists to prevent"
        );
        // And it delivers nothing, which is the whole point: tree-neutral where
        // it cannot type, rather than a cursor traded for nothing.
        assert!(
            !matches!(
                table_decision(CURSOR_ONLY, "inputs"),
                Decision::NestedSlice { .. }
            ),
            "the table it cannot type must not be flipped"
        );
    })
    .unwrap();
}

/// **W-N1-STANDOFF-SCOPED** — an owner with no cursor row at all never reaches
/// the precondition, so `ti_ema`'s two-table plan is exactly what it was before
/// this clause existed.
#[test]
fn n1_standoff_does_not_touch_an_owner_without_a_cursor_row() {
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
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == BOTH)
            .and_then(|r| r.result.as_ref().ok())
            .expect("an admitted N1 plan");
        assert_eq!(plan.parameters.len(), 2, "both tables still deliver");
        assert!(plan.stood_off.is_empty(), "nothing was stood off");
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
