use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::{
    mir::{Body, Location},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis,
    points::{DenseLocationMap, PointIndex},
};

use super::{Provenance, ProvenanceData, ProvenanceSet, direct_raw_pointer_field_slots_in_ty};
use crate::analyses::{liveness::MaybeLiveLocals, mir::TerminatorExt};

/// The set of program points where a [`Provenance`] is live.
pub(crate) type ProvenanceLiveness = SparseBitMatrix<PointIndex, Provenance>;

pub fn compute_provenance_liveness<'tcx>(
    location_map: &DenseLocationMap,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    provenance_set: &ProvenanceSet,
) -> ProvenanceLiveness {
    let mut provenance_liveness = ProvenanceLiveness::new(provenance_set.provenance_data.len());
    let placeholder_provenances: Vec<_> = provenance_set
        .provenance_data
        .iter_enumerated()
        .filter_map(|(provenance, data)| {
            matches!(data, ProvenanceData::PlaceHolder(..)).then_some(provenance)
        })
        .collect();

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

            let point_index = location_map.point_from_location(location);
            for &provenance in &placeholder_provenances {
                provenance_liveness.insert(point_index, provenance);
            }

            local_liveness.seek_before_primary_effect(location);
            let liveness = local_liveness.get();
            for local in liveness.iter() {
                if let Some(provenance) = provenance_set.local_data[local] {
                    provenance_liveness.insert(point_index, provenance);
                }
                for field in direct_raw_pointer_field_slots_in_ty(tcx, body.local_decls[local].ty) {
                    if let Some(provenance) =
                        provenance_set.field_data.get(&field).copied().flatten()
                    {
                        provenance_liveness.insert(point_index, provenance);
                    }
                }
            }

            if position == bb_len - 1 {
                // This is a terminator
                if let Some(terminator) = &bb_data.terminator
                    && let Some(mir_call) = terminator.as_call(tcx)
                    && let Some(dest_local) = mir_call.destination.as_local()
                    && let Some(dest_provenance) = provenance_set.local_data[dest_local]
                {
                    // Make the destination provenance live at terminator location
                    let point_index = location_map.point_from_location(location);
                    provenance_liveness.insert(point_index, dest_provenance);
                }
            }
        }
    }

    provenance_liveness
}
