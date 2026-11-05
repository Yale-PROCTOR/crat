//! Two rules.
//!
//! - The depth-0 copy relaxation: a bare copy `x := y` between two locals, at an eligible site,
//!   keeps `x_0 ≡ y_0` or takes `y_0 = Ref ∧ x_0 = Raw` (a raw view of a reference). Raw → Ref
//!   stays forbidden and an Owning source stays equal; depths ≥ 1 stay equal.
//! - Merged liveness: in the engine's replay (the CEGAR validation and its
//!   witnessed pass), a local the replay demoted keeps its group's live owners' provenances
//!   live wherever it is live. Under Tree Borrows a raw view carries its source's tag, so the
//!   loans the source's origin requires must stay live through the view's uses.
//!
//! **The call arm** (relay era-5c/269, `construction::copy_relax_escape`). A copy whose value
//! reaches a call only as arguments whose formals the callee provably never retains
//! (`index_ranges::never_retained`; `memcpy` / `memmove` / `memset`'s contract rows), and whose
//! closure's own storage is never addressed, does not leave the function: during the call the
//! callee's accesses through it are child accesses of the source's tag, and nothing of it
//! outlives the call. The edge between two such copies
//! lent to one call stays (it is real for references); only the source's drag to its copy goes.
//!
//! **The emission's two obligations** (the seat's condition, relay era-5c/269 §1.3, and the
//! second review). Both are the rewriter's; this module exports what they need.
//!
//! - **A relaxed view carries its source's tag.** A raw copy of a `Ref` source is sound only
//!   when the emission creates it without a retag (`&raw mut *y`, `y as *mut T`, the
//!   coercion), never through a reborrow (`ptr::from_mut(&mut *y)`, a slice's
//!   `as_mut_ptr()`) while `y` is accessed before the view's last use: under Tree Borrows a
//!   reborrowed view is a child that the next write through `y` disables. S39's in-function
//!   relaxation already rests on this; the call arm extends it to a call's arguments.
//! - **The views of one subject at one call are not siblings.** When two or more arguments
//!   of one call are views of one `Ref` subject (`f(out, out)`), the subject's `Ref` is sound
//!   only if the emission introduces no sibling reborrow among them: every view it creates
//!   for the call derives from ONE raw pointer (`let p = out.as_mut_ptr(); f(p, p, …)`; a
//!   reborrow the input already has, `&(*ctx).pub_seed`, stays as it is), and the callee's
//!   formals at those positions stay raw (R833's pair rule, which the rewriter already
//!   applies: two references into one object at one call are UB under the callee's
//!   protectors, whatever pointer they come from). Spelled as separate reborrows
//!   (`out.as_mut_ptr()` twice), the views are siblings: a callee that writes through one
//!   view and then reads through another reads a Disabled tag (030's
//!   `fma_array(out, out, out, out, n)`; `thash`, `haraka512_perm` and `memmove` read before
//!   they write). Every call an admitted copy reaches with two or more views of its subject
//!   (`construction::copy_relax_views`) is exported as a `multi-view` row (`MultiView`, the
//!   `multi-view` export family), one per admission, whatever the subject's kind settles to (a
//!   Raw subject owes nothing). A `NotRecorded` family means unknown, not none.

use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis,
    points::{DenseLocationMap, PointIndex},
};
use rustc_span::def_id::LocalDefId;

use super::guarded_repair::MirLocationKey;
use crate::analyses::{
    borrow::{Provenance, ProvenanceSet},
    liveness::MaybeLiveLocals,
};

thread_local! {
    /// The copies the relaxation may take, installed by the solve before any coherence is
    /// added (`construction::analyze_copy_relax_sites`). Nothing installed: nothing is relaxed.
    /// Per thread: the solve installs and reads it on the compiler's thread, and compiler
    /// sessions running side by side in one process do not see each other's sites.
    static ELIGIBLE: RefCell<Option<FxHashMap<LocalDefId, FxHashSet<MirLocationKey>>>> =
        const { RefCell::new(None) };
}

/// One `multi-view` row (relay era-5c/269 §1.3): at the call terminating `call`'s block in
/// `function`, the arguments `arguments` (two or more, by position) are views of the local
/// `subject`, one of them at least through a copy the call arm admits. The emission owes them
/// one raw pointer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MultiView {
    pub(crate) function: LocalDefId,
    pub(crate) subject: Local,
    pub(crate) call: Location,
    pub(crate) arguments: Vec<u32>,
}

pub(crate) fn install(eligible: FxHashMap<LocalDefId, FxHashSet<MirLocationKey>>) {
    ELIGIBLE.with_borrow_mut(|slot| *slot = Some(eligible));
}

pub(crate) fn eligible(fn_did: LocalDefId, block: BasicBlock, statement_index: usize) -> bool {
    ELIGIBLE.with_borrow(|slot| {
        slot.as_ref().is_some_and(|eligible| {
            eligible.get(&fn_did).is_some_and(|sites| {
                sites.contains(&MirLocationKey::new(block.as_u32(), statement_index))
            })
        })
    })
}

/// Marks, at every point where a demoted local is live, the provenances of the live owners of
/// its union group (the members whose provenance the replay has not disabled). Returns the
/// number of (point, provenance) insertions.
pub(crate) fn extend_merge_liveness<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    provenance_set: &ProvenanceSet,
    demoted: &FxHashSet<Local>,
    location_map: &DenseLocationMap,
    liveness: &mut SparseBitMatrix<PointIndex, Provenance>,
) -> usize {
    let mut owners: FxHashMap<Local, Vec<Provenance>> = FxHashMap::default();
    for &local in demoted {
        let group = provenance_set.tree_borrow_local.borrow_mut().group(local);
        let mut live: Vec<Provenance> = group
            .into_iter()
            .filter(|member| *member != local)
            .filter_map(|member| provenance_set.local_data[member])
            .collect();
        live.sort();
        if !live.is_empty() {
            owners.insert(local, live);
        }
    }
    if owners.is_empty() {
        return 0;
    }
    let mut inserted = 0;
    let mut local_liveness = MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        local_liveness.seek_to_block_end(bb);
        let bb_len = bb_data.statements.len() + bb_data.terminator.is_some() as usize;
        for position in (0..bb_len).rev() {
            let location = Location {
                block: bb,
                statement_index: position,
            };
            let point = location_map.point_from_location(location);
            local_liveness.seek_before_primary_effect(location);
            for local in local_liveness.get().iter() {
                if let Some(provenances) = owners.get(&local) {
                    for &provenance in provenances {
                        inserted += liveness.insert(point, provenance) as usize;
                    }
                }
            }
        }
    }
    inserted
}
