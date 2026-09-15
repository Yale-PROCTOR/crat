//! Wave-6o (relay 006, R402-8). The thin-extent holds at the THIN `Opt` form.
//!
//! [`super::thin_extent`] (R272-1, a foreign position whose pinned contract
//! consumes more than one element) and [`super::local_callee_extent`]
//! (R364-2, a local callee that accesses wider than one element) are facts
//! about the SUBJECT, not about its form: an `Option<&T>` / `Option<&mut T>`
//! bridged to such a position hands over the same one-element claim a thin
//! `&T` would, and the callee walks off it. Both holds sat only in the plain
//! arm; this module answers the same two questions for the thin optional, in
//! the same order, with the same reason keys, so the facts join keeps one
//! vocabulary. Optional SLICES carry their own extent and are not held here.

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{DegradeReason, Subject, local_callee_extent::LocalCalleeAccess};

pub(crate) fn hold(
    subject: &Subject,
    thin_extent: &FxHashSet<(LocalDefId, HirId)>,
    local_callee_extent: &rustc_hash::FxHashMap<(LocalDefId, HirId), LocalCalleeAccess>,
) -> Option<DegradeReason> {
    let node = (subject.fn_did, subject.hir_id);
    if thin_extent.contains(&node) {
        return Some(DegradeReason::ThinExtent);
    }
    local_callee_extent
        .get(&node)
        .map(|access| DegradeReason::LocalCalleeAccessExtent {
            access: Box::new(access.clone()),
        })
}
