//! era-5c relay 208 (the paper session's S39, the user's proposal): two switches, both off in
//! the frame.
//!
//! - `CRAT_COPY_RELAX=off|depth0-borrow-to-raw`: a bare copy `x := y` between two locals
//!   keeps `x_0 ≡ y_0` or takes `y_0 = Ref ∧ x_0 = Raw` (a raw view of a reference). Raw → Ref
//!   stays forbidden and an Owning source stays equal; depths ≥ 1 stay equal.
//! - `CRAT_MERGE_LIVENESS=off|on`: in the engine's replay (the CEGAR validation and its
//!   witnessed pass), a local the replay demoted keeps its group's live owners' provenances
//!   live wherever it is live. Under Tree Borrows a raw view carries its source's tag, so the
//!   loans the source's origin requires must stay live through the view's uses.

use std::sync::Mutex;

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

/// The copies the relaxation may take (S39 (b)), installed by the solve before any coherence is
/// added (`construction::analyze_copy_relax_sites`). Nothing installed: nothing is relaxed.
static ELIGIBLE: Mutex<Option<FxHashMap<LocalDefId, FxHashSet<MirLocationKey>>>> = Mutex::new(None);

pub(crate) fn install(eligible: FxHashMap<LocalDefId, FxHashSet<MirLocationKey>>) {
    *ELIGIBLE.lock().unwrap() = Some(eligible);
}

pub(crate) fn eligible(fn_did: LocalDefId, block: BasicBlock, statement_index: usize) -> bool {
    ELIGIBLE.lock().unwrap().as_ref().is_some_and(|eligible| {
        eligible.get(&fn_did).is_some_and(|sites| {
            sites.contains(&MirLocationKey::new(block.as_u32(), statement_index))
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
