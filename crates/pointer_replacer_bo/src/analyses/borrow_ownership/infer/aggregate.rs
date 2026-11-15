//! Struct and tuple initialization transfer disjoint component windows.

use rustc_abi::FieldIdx;

use super::*;
use crate::analyses::borrow_ownership::{ownership_occurrence, source_events};

#[cfg(test)]
mod tests;

impl<'infercx, 'db, 'tcx, Analysis> InferCtxt<'infercx, 'db, 'tcx, Analysis>
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
{
    pub(super) fn aggregate(
        &mut self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        kind: &AggregateKind<'tcx>,
        destination: Option<Consume<LocalSig>>,
        operands: &[(&Operand<'tcx>, Option<Consume<LocalSig>>)],
    ) {
        if !self.transfer_aggregate(body, place, kind, destination.clone(), operands) {
            // Operand visitation already advanced SSA. A declined transfer must
            // preserve every represented responsibility instead of allowing an
            // unconstrained post-value to disappear at finalization.
            for (_, source) in operands {
                if let Some(source) = source {
                    <Analysis as InferMode>::lend(self, source.clone());
                }
            }
            if let Some(destination) = destination {
                <Analysis as InferMode>::borrow(self, destination);
            }
        }
    }

    fn transfer_aggregate(
        &mut self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        kind: &AggregateKind<'tcx>,
        destination: Option<Consume<LocalSig>>,
        operands: &[(&Operand<'tcx>, Option<Consume<LocalSig>>)],
    ) -> bool {
        let Some(destination) = destination else { return false };
        if operands.iter().any(|(operand, _)| {
            operand
                .place()
                .is_some_and(|source| source.local == place.local)
        }) {
            return false;
        }
        let ty = place.ty(body, self.tcx).ty;
        let fields: Vec<_> = match (kind, ty.kind()) {
            (AggregateKind::Adt(did, _, args, _, None), TyKind::Adt(adt, destination_args))
                if adt.did() == *did
                    && args == destination_args
                    && adt.is_struct()
                    && self.struct_ctxt.unrestricted.is_struct_of_concerned(did) =>
            {
                adt.non_enum_variant()
                    .fields
                    .iter_enumerated()
                    .map(|(index, field)| (index, field.ty(self.tcx, args)))
                    .collect()
            }
            (AggregateKind::Tuple, TyKind::Tuple(elements)) => elements
                .iter()
                .enumerate()
                .map(|(index, ty)| (FieldIdx::from_usize(index), ty))
                .collect(),
            _ => return false,
        };
        if fields.len() != operands.len() {
            return false;
        }
        let width = destination.r#use.end.as_u32() - destination.r#use.start.as_u32();
        if width == 0 || destination.def.end.as_u32() - destination.def.start.as_u32() != width {
            return false;
        }
        let topology = self.struct_ctxt.unrestricted;
        let precision = topology.absolute_precision(ty, width);
        let chased = (topology.max_ptr_chased() - precision) as u32;
        if topology.measure(ty, chased) != width {
            return false;
        }

        // Validate the full partition before applying any field's laws. Slicing
        // these existing ranges must never frame another initialized field.
        let mut slices = Vec::new();
        let mut source_windows: Vec<Range<Var>> = Vec::new();
        let mut covered = 0;
        for (index, field_ty) in fields {
            let start = topology.field_offset(ty, index.as_usize(), chased);
            let field_width = topology.measure(field_ty, chased);
            if start != covered || field_width > width - covered {
                return false;
            }
            covered += field_width;
            if field_width == 0 {
                if operands[index.as_usize()]
                    .1
                    .as_ref()
                    .is_some_and(|source| !source.r#use.is_empty() || !source.def.is_empty())
                {
                    return false;
                }
                continue;
            }
            let (operand, direct_source) = &operands[index.as_usize()];
            if operand.place().is_some() && direct_source.is_none() {
                return false;
            }
            let source = direct_source.clone();
            let by_move = operand.is_move();
            if let Some(source) = &source {
                if source.r#use.end.as_u32() - source.r#use.start.as_u32() != field_width
                    || source.def.end.as_u32() - source.def.start.as_u32() != field_width
                    || source_windows.iter().any(|previous| {
                        previous.start < source.r#use.end && source.r#use.start < previous.end
                    })
                {
                    return false;
                }
                source_windows.push(source.r#use.clone());
            }
            let slice = Consume {
                r#use: destination.r#use.start + start..destination.r#use.start + covered,
                def: destination.def.start + start..destination.def.start + covered,
            };
            slices.push((index, field_ty, slice, source, by_move));
        }
        if covered != width {
            return false;
        }

        for (index, field_ty, slice, source, by_move) in slices {
            let field_place = place.project_deeper(&[PlaceElem::Field(index, field_ty)], self.tcx);
            let field_record =
                ownership_occurrence::record_field_view(place, field_place, &destination, &slice);
            let _destination = ownership_occurrence::destination_hint(field_record);
            let operand = operands[index.as_usize()].0;
            if let Some(source) = source {
                if by_move {
                    <Analysis as InferMode>::transfer::<true>(self, field_ty, slice, source, None);
                } else {
                    <Analysis as InferMode>::transfer::<false>(self, field_ty, slice, source, None);
                }
            } else if (field_ty.is_raw_ptr() || field_ty.is_ref() || field_ty.is_box())
                && source_events::operand_is_null(operand, &[], self.tcx)
            {
                with_own_assume_site(OwnAssumeSite::AggregateNull, || {
                    <Analysis as InferMode>::assume(self, slice.r#use, false);
                    <Analysis as InferMode>::assume(self, slice.def, false);
                });
            } else {
                // A constant's syntax is retained, but no transfer or licence
                // is fabricated for its unrepresented origin.
                <Analysis as InferMode>::unknown_source(self, slice);
            }
        }
        true
    }
}
