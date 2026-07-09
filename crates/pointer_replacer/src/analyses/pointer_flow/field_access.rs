//! field access events and rejects recorded on pointer-flow nodes, plus the
//! per-parameter query layer. events are flat lists in MIR-walk order; per-node
//! lookup is a linear filter, acceptable at per-body event counts.

use rustc_abi::FieldIdx;
use rustc_middle::{
    mir::{
        Body, Location, Place, ProjectionElem,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::{self, TyCtxt},
};

use crate::analyses::pointer_flow::{graph::PfgNode, slots::SlotTable};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldAccess {
    pub node: PfgNode,
    pub field: FieldIdx,
    pub kind: FieldAccessKind,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldAccessKind {
    Read,
    Write,
    Address,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldAccessReject {
    pub node: PfgNode,
    pub kind: FieldAccessRejectKind,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldAccessRejectKind {
    WholeStructUse,
    UnknownCallee,
    IncompleteCalleeSummary,
    EscapesToMemory,
    Returned,
    PointerArithmetic,
    IncompatibleCast,
    UnionFieldAccess,
}

pub(crate) struct FieldEventScanner<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    slot_table: &'a SlotTable,
    field_accesses: Vec<FieldAccess>,
    field_rejects: Vec<FieldAccessReject>,
}

impl<'a, 'tcx> FieldEventScanner<'a, 'tcx> {
    pub(crate) fn scan(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        slot_table: &'a SlotTable,
    ) -> (Vec<FieldAccess>, Vec<FieldAccessReject>) {
        let mut scanner = Self {
            tcx,
            body,
            slot_table,
            field_accesses: vec![],
            field_rejects: vec![],
        };
        scanner.visit_body(body);
        (scanner.field_accesses, scanner.field_rejects)
    }

    // resolves the pointer being deref'd (the place prefix before projection
    // index `deref_index`) to its PFG slot node. prefixes that fall outside
    // the slot table (recursive-struct cut) cannot reach any tracked base, so
    // callers skip the event when this returns None.
    fn prefix_node(&self, place: Place<'tcx>, deref_index: usize) -> Option<PfgNode> {
        let prefix_place =
            Place::from(place.local).project_deeper(&place.projection[..deref_index], self.tcx);
        self.slot_table
            .place_slots(prefix_place, self.body, self.tcx)?
            .next()
            .map(PfgNode::Slot)
    }

    fn scan_place(&mut self, place: Place<'tcx>, context: PlaceContext, location: Location) {
        let use_kind = classify_place_context(context);
        let projection = place.projection.as_ref();

        for (i, elem) in projection.iter().enumerate() {
            if !matches!(elem, ProjectionElem::Deref) {
                continue;
            }
            let prefix_ty = Place::ty_from(place.local, &projection[..i], self.body, self.tcx).ty;
            let Some(pointee) = prefix_ty.builtin_deref(true) else {
                continue;
            };
            let ty::TyKind::Adt(adt_def, _) = pointee.kind() else {
                continue;
            };

            let next = projection.get(i + 1);
            if adt_def.is_union() {
                let Some(node) = self.prefix_node(place, i) else {
                    continue;
                };
                self.field_rejects.push(FieldAccessReject {
                    node,
                    kind: FieldAccessRejectKind::UnionFieldAccess,
                    location,
                });
            } else if adt_def.is_struct() {
                match next {
                    Some(ProjectionElem::Field(field, _)) => {
                        let Some(node) = self.prefix_node(place, i) else {
                            continue;
                        };
                        // a later deref means this field is only read to traverse
                        let terminal = projection[i + 2..]
                            .iter()
                            .all(|elem| !matches!(elem, ProjectionElem::Deref));
                        let kind = if terminal {
                            use_kind
                        } else {
                            FieldAccessKind::Read
                        };
                        self.field_accesses.push(FieldAccess {
                            node,
                            field: *field,
                            kind,
                            location,
                        });
                    }
                    _ => {
                        // whole-struct use of `*q`; the plain-reborrow exemption
                        // and the reject arrive in Task 3
                    }
                }
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for FieldEventScanner<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.scan_place(*place, context, location);
        self.super_place(place, context, location);
    }
}

fn classify_place_context(context: PlaceContext) -> FieldAccessKind {
    match context {
        PlaceContext::NonMutatingUse(
            NonMutatingUseContext::SharedBorrow
            | NonMutatingUseContext::FakeBorrow
            | NonMutatingUseContext::RawBorrow,
        )
        | PlaceContext::MutatingUse(MutatingUseContext::Borrow | MutatingUseContext::RawBorrow) => {
            FieldAccessKind::Address
        }
        PlaceContext::MutatingUse(_) => FieldAccessKind::Write,
        _ => FieldAccessKind::Read,
    }
}
