//! **wave-6a 158 (relay 158; main 207a item 4)** — the A5 raw view at a call
//! whose formal a 57 hold makes raw, over the caller's own subject-use edits in
//! arguments the view does not select. brotli's `EmitLiterals` →
//! `BrotliWriteBits(*depth.offset(lit), *bits.offset(lit), storage_ix, storage)`:
//! at 56 `storage` was a delivered slice and its seam adapter sat inside the
//! call, so the byte projection left the whole-call view to the AST pass
//! (`nested_c9_over_seam`), which composed `depth[lit]` / `bits[lit]` under it.
//! At 57 `storage` is held for the pair, no seam is left in the call, the view
//! stays in the projection, and the caller's inner edits roll back
//! (`apply-site-rollback: edit overlaps an earlier edit`), holding its class.
//! The AST pass composes the same edits either way (`A5RawGraftVisitor` walks
//! the call's children first): only the projection refuses.

use super::{
    bridge_receipt::SignatureClassId,
    plan::{Edit, Justification},
};

fn class(index: u32) -> SignatureClassId {
    SignatureClassId::of(rustc_hir::def_id::LocalDefId {
        local_def_index: rustc_span::def_id::DefIndex::from_u32(index),
    })
}

const CALLEE: u32 = 1;
const CALLER: u32 = 2;

/// The call as the input has it.
const CALL: &str = "BrotliWriteBits(*depth.offset(lit as isize) as usize, *bits.offset(lit as isize) as u64, storage_ix, storage)";

fn edit(
    lo: usize,
    hi: usize,
    replacement: &str,
    justification: Justification,
    owner: u32,
    edit_kind: &'static str,
) -> Edit {
    Edit {
        lo,
        hi,
        replacement: replacement.to_owned(),
        justification,
        owner_class: Some(class(owner)),
        owner_path: "-".to_owned(),
        bridge: None,
        atom_ids: Vec::new(),
        subject_id: "-".to_owned(),
        required_arms: "-".to_owned(),
        edit_kind,
    }
}

/// The A5 raw view over the whole call (the callee's class), selecting
/// `storage` only.
fn a5_view() -> Edit {
    edit(
        0,
        CALL.len(),
        "{ let __crat_a5_raw_0_3: *mut u8 = storage; BrotliWriteBits(*depth.offset(lit as isize) as usize, *bits.offset(lit as isize) as u64, storage_ix, __crat_a5_raw_0_3) }",
        Justification::A5RawView,
        CALLEE,
        "a5-proof-site-raw-view",
    )
}

/// A subject-use edit of `owner` at `text` inside the call.
fn subject_use(text: &str, replacement: &str, owner: u32) -> Edit {
    let lo = CALL.find(text).expect("inside the call");
    edit(
        lo,
        lo + text.len(),
        replacement,
        Justification::KindDecision { kind: "slice" },
        owner,
        "subject-use",
    )
}

/// The planner recorded the view's class depending on the caller's
/// (`a5_wrapper_composition`'s unselected-argument case).
fn composed(outer: SignatureClassId, inner: SignatureClassId) -> bool {
    outer == class(CALLEE) && inner == class(CALLER)
}

fn rollbacks(edits: &[Edit]) -> usize {
    super::apply::apply(CALL, &super::validation_projection(edits, &composed))
        .rollbacks
        .len()
}

#[test]
fn w6a_158_a5_view_over_the_callers_use_in_an_unselected_argument_does_not_roll_back() {
    let edits = [
        a5_view(),
        subject_use(
            "*depth.offset(lit as isize)",
            "depth[(lit) as usize]",
            CALLER,
        ),
        subject_use("*bits.offset(lit as isize)", "bits[(lit) as usize]", CALLER),
    ];
    assert_eq!(rollbacks(&edits), 0);
}

/// Control: a contained use of the view's OWN class is the intra-class overlap
/// the plan holds; it still rolls back.
#[test]
fn w6a_158_a5_view_over_its_own_class_use_still_rolls_back() {
    let edits = [
        a5_view(),
        subject_use(
            "*depth.offset(lit as isize)",
            "depth[(lit) as usize]",
            CALLEE,
        ),
    ];
    assert_eq!(rollbacks(&edits), 1);
}

/// Control: an edit that only OVERLAPS the view (not strictly inside it) is no
/// nesting the AST pass composes; it still rolls back.
#[test]
fn w6a_158_an_edit_straddling_the_view_still_rolls_back() {
    let straddle = edit(
        CALL.len() - 8,
        CALL.len() + 1,
        "x",
        Justification::KindDecision { kind: "slice" },
        CALLER,
        "subject-use",
    );
    let mut text = CALL.to_owned();
    text.push(';');
    let applied = super::apply::apply(
        &text,
        &super::validation_projection(&[a5_view(), straddle], &composed),
    );
    assert_eq!(applied.rollbacks.len(), 1);
}

/// Control (the stand-in review's F1): an edit ENCLOSING the call — a
/// construction over an initializer that contains it — still collides with
/// the view. The AST pass would re-parse the initializer before the A5 pass and
/// lose the call's span; the projection must keep holding that one class.
#[test]
fn w6a_158_an_edit_enclosing_the_view_still_rolls_back() {
    let text = format!("malloc({CALL} as u64)");
    let shift = "malloc(".len();
    let shifted = |mut e: Edit| {
        e.lo += shift;
        e.hi += shift;
        e
    };
    let enclosing = edit(
        0,
        text.len(),
        "x",
        Justification::SeamAdapter {
            family: "safe",
            fabricated: false,
        },
        CALLER,
        "slice-local-construction",
    );
    let edits = [
        enclosing,
        shifted(a5_view()),
        shifted(subject_use(
            "*depth.offset(lit as isize)",
            "depth[(lit) as usize]",
            CALLER,
        )),
    ];
    let applied = super::apply::apply(&text, &super::validation_projection(&edits, &composed));
    assert!(!applied.rollbacks.is_empty());
}

/// Control (the stand-in review's F2): without the planner's recorded
/// composition the contained use is not suppressed.
#[test]
fn w6a_158_an_uncomposed_use_inside_the_view_still_rolls_back() {
    let edits = [
        a5_view(),
        subject_use(
            "*depth.offset(lit as isize)",
            "depth[(lit) as usize]",
            CALLER,
        ),
    ];
    let none = |_: SignatureClassId, _: SignatureClassId| false;
    let applied = super::apply::apply(CALL, &super::validation_projection(&edits, &none));
    assert_eq!(applied.rollbacks.len(), 1);
}
