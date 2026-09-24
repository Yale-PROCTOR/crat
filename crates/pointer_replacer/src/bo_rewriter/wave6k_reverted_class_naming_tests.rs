//! **The final-reverts artifact names every reverted class (R477-6).**
//!
//! wave-6k report 027 measured 161 rows over eight programs — brotli 87, binn
//! 30, heman 29, lodepng 8, libtree 3, robotfindskitten 2, buffer 1, bzip2 1 —
//! whose identity column read `<unknown-local-class>`. They are one population:
//! classes reverted through a HOLD (`held:*` 84 of brotli's 87) rather than
//! through a subject-keyed path, so `class_paths` — filled from planned edits,
//! emitted sites and emitted subjects — never saw them. The cause was never
//! lost (class id and reason head are on every row); only the name was.

use std::collections::{BTreeMap, BTreeSet};

use super::bridge_receipt::SignatureClassId;

/// The identity column of the one rendered row.
fn rendered_identity(
    withheld: &BTreeSet<SignatureClassId>,
    class_paths: &BTreeMap<SignatureClassId, String>,
) -> String {
    let receipt = super::render_raw_boundary_final_reverts(
        withheld,
        &BTreeSet::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        class_paths,
        &BTreeMap::new(),
        &BTreeSet::new(),
        None,
    );
    let header = receipt.lines().next().expect("a header");
    let column = header
        .split('\t')
        .position(|name| name == "identity")
        .expect("an identity column");
    receipt
        .lines()
        .nth(1)
        .expect("one row")
        .split('\t')
        .nth(column)
        .expect("the identity cell")
        .to_owned()
}

#[test]
fn wave6k_a_class_held_before_any_edit_renders_its_own_path() {
    ::utils::compilation::run_compiler_on_str(
        "pub unsafe fn held(p: *mut i32) -> i32 { *p }",
        |tcx| {
            let did = tcx
                .hir_crate_items(())
                .free_items()
                .map(|id| id.owner_id.def_id)
                .find(|did| {
                    tcx.opt_item_name(did.to_def_id())
                        .is_some_and(|item| item.as_str() == "held")
                })
                .expect("the fixture's function");
            let class = SignatureClassId::of(did);
            let withheld = BTreeSet::from([class]);

            // The gap, pinned: a class no edit, site or emitted subject ever
            // named has no entry, and the artifact writes the literal.
            let unseeded = BTreeMap::new();
            assert_eq!(
                rendered_identity(&withheld, &unseeded),
                "<unknown-local-class>",
                "the fallback is what report 027 measured 161 times"
            );

            // The fix: the reverted set names itself from the run.
            let mut seeded = BTreeMap::new();
            super::name_reverted_classes(tcx, &withheld, &mut seeded);
            assert_eq!(
                rendered_identity(&withheld, &seeded),
                "held",
                "the class renders the path the run already knows"
            );

            // Control: a class the emitted artifacts already named keeps that
            // name — `or_insert_with`, so no named row of the 364 moves.
            let mut already = BTreeMap::from([(class, "src::p::already".to_owned())]);
            super::name_reverted_classes(tcx, &withheld, &mut already);
            assert_eq!(
                already.get(&class).map(String::as_str),
                Some("src::p::already"),
                "an existing display path wins"
            );
        },
    )
    .expect("the fixture compiles");
}

/// **R547-6 (wave-6l 051 STOP 1) — the floor's revert names the arm.** A class
/// the graft floor held is reverted by the hold loop exactly as the verify loop
/// would revert it, and it sits in the same `reverted` set. Its final-reverts row
/// read `verify-reverted` while `graft-held.tsv` named the C-9 arm (brotli's
/// `ProcessRepeatedCodeLength`, class 557, at `l01p7`). The row now reads
/// `graft-held:c9`; a class only the verify loop reverted keeps `verify-reverted`.
#[test]
fn r547_6_a_floor_revert_is_attributed_to_the_arm_that_yielded() {
    ::utils::compilation::run_compiler_on_str(
        "pub unsafe fn held(p: *mut i32) -> i32 { *p }\npub unsafe fn verified(p: *mut i32) -> i32 { *p }",
        |tcx| {
            let class_of = |name: &str| {
                SignatureClassId::of(
                    tcx.hir_crate_items(())
                        .free_items()
                        .map(|id| id.owner_id.def_id)
                        .find(|did| {
                            tcx.opt_item_name(did.to_def_id())
                                .is_some_and(|item| item.as_str() == name)
                        })
                        .expect("the fixture's function"),
                )
            };
            let (held, verified) = (class_of("held"), class_of("verified"));
            super::ast_transform::reset_graft_held();
            super::ast_transform::record_graft_held(
                super::ast_transform::GraftHeldReceipt {
                    visitor: super::ast_transform::GraftVisitor::C9,
                    caller: held.local_def_id().local_def_index.as_u32(),
                    class: held.order_key(),
                    reason: "counted-void-twin",
                    lo: 10,
                    hi: 20,
                },
                held,
            );
            let both = BTreeSet::from([held, verified]);
            let receipt = super::render_raw_boundary_final_reverts(
                &both,
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &both,
                None,
            );
            super::ast_transform::reset_graft_held();
            let header = receipt.lines().next().expect("a header").split('\t').collect::<Vec<_>>();
            let column = |name: &str| header.iter().position(|h| *h == name).expect(name);
            let attribution_of = |class: SignatureClassId| {
                receipt
                    .lines()
                    .skip(1)
                    .map(|line| line.split('\t').collect::<Vec<_>>())
                    .find(|cells| cells[column("class_id")] == format!("local-def-index:{}", class.order_key()))
                    .map(|cells| (cells[column("attribution")].to_owned(), cells[column("reason_head")].to_owned()))
                    .unwrap_or_else(|| panic!("no row for {class:?} in\n{receipt}"))
            };
            assert_eq!(
                attribution_of(held),
                ("graft-held:c9".to_owned(), "graft-held".to_owned()),
                "{receipt}"
            );
            assert_eq!(
                attribution_of(verified).0,
                "verify-reverted",
                "{receipt}"
            );
        },
    )
    .expect("fixture compiles");
}
