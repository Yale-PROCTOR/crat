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
