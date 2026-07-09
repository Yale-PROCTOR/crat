//! field access events and rejects recorded on pointer-flow nodes, plus the
//! per-parameter query layer. events are flat lists in MIR-walk order; per-node
//! lookup is a linear filter, acceptable at per-body event counts.

use rustc_abi::FieldIdx;
use rustc_middle::{
    mir::{
        self, Body, Location, Place, ProjectionElem, Rvalue,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::{self, TyCtxt},
};

use crate::analyses::pointer_flow::{collector::operand_place, graph::PfgNode, slots::SlotTable};

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
                match next {
                    Some(ProjectionElem::Field(..)) => {
                        let Some(node) = self.prefix_node(place, i) else {
                            continue;
                        };
                        self.field_rejects.push(FieldAccessReject {
                            node,
                            kind: FieldAccessRejectKind::UnionFieldAccess,
                            location,
                        });
                    }
                    _ => {
                        // plain reborrows `&*q` / `&raw mut *q` are modeled precisely by
                        // collect_raw_borrow_flow as a flow edge, not a struct use
                        let plain_reborrow =
                            projection.len() == 1 && matches!(use_kind, FieldAccessKind::Address);
                        if plain_reborrow {
                            continue;
                        }
                        let Some(node) = self.prefix_node(place, i) else {
                            continue;
                        };
                        self.field_rejects.push(FieldAccessReject {
                            node,
                            kind: FieldAccessRejectKind::WholeStructUse,
                            location,
                        });
                    }
                }
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
                        // plain reborrows `&*q` / `&raw mut *q` are modeled precisely by
                        // collect_raw_borrow_flow as a flow edge, not a struct use
                        let plain_reborrow =
                            projection.len() == 1 && matches!(use_kind, FieldAccessKind::Address);
                        if plain_reborrow {
                            continue;
                        }
                        let Some(node) = self.prefix_node(place, i) else {
                            continue;
                        };
                        self.field_rejects.push(FieldAccessReject {
                            node,
                            kind: FieldAccessRejectKind::WholeStructUse,
                            location,
                        });
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

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        // returning a pointer value: record on the return slot node; reachability
        // decides which parameters it concerns
        if place.local == mir::RETURN_PLACE
            && place.projection.is_empty()
            && let Some(slot) = self.slot_table.local_head_slot(place.local)
        {
            self.field_rejects.push(FieldAccessReject {
                node: PfgNode::Slot(slot),
                kind: FieldAccessRejectKind::Returned,
                location,
            });
        }

        // storing a struct-pointer value through a deref is tracked by the PFG,
        // but the use itself is not rewritable by param specialization (the
        // destination cell's declared type keeps the pointer alive) — see plan notes
        if let Some(src_place) = assigned_pointer_source(rvalue)
            && is_raw_ptr_to_adt(src_place.ty(self.body, self.tcx).ty)
            && (place
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref))
                || self
                    .slot_table
                    .place_slots(*place, self.body, self.tcx)
                    .is_none())
            && let Some(node) = self.head_node(src_place)
        {
            self.field_rejects.push(FieldAccessReject {
                node,
                kind: FieldAccessRejectKind::EscapesToMemory,
                location,
            });
        }

        self.super_assign(place, rvalue, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Cast(_, operand, target_ty) => {
                if let Some(place) = operand_place(operand)
                    && let src_ty = place.ty(self.body, self.tcx).ty
                    && is_raw_ptr_to_adt(src_ty)
                    && src_ty.builtin_deref(true) != target_ty.builtin_deref(true)
                    && let Some(node) = self.head_node(place)
                {
                    self.field_rejects.push(FieldAccessReject {
                        node,
                        kind: FieldAccessRejectKind::IncompatibleCast,
                        location,
                    });
                }
            }
            Rvalue::BinaryOp(mir::BinOp::Offset, box (lhs, _)) => {
                if let Some(place) = operand_place(lhs)
                    && is_raw_ptr_to_adt(place.ty(self.body, self.tcx).ty)
                    && let Some(node) = self.head_node(place)
                {
                    self.field_rejects.push(FieldAccessReject {
                        node,
                        kind: FieldAccessRejectKind::PointerArithmetic,
                        location,
                    });
                }
            }
            Rvalue::Aggregate(_, operands) => {
                // a pointer packed into a composite value is out of slot-tracking
                self.reject_escaping_operands(operands.iter(), location);
            }
            Rvalue::Repeat(operand, _) => {
                // a pointer repeated into an array is out of slot-tracking, same as Aggregate
                self.reject_escaping_operands(std::iter::once(operand), location);
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }
}

impl<'tcx> FieldEventScanner<'_, 'tcx> {
    fn head_node(&self, place: Place<'tcx>) -> Option<PfgNode> {
        self.slot_table
            .place_head_slot(place, self.body, self.tcx)
            .map(PfgNode::Slot)
    }

    // shared by Rvalue::Aggregate and Rvalue::Repeat: any struct-pointer operand
    // packed into a composite value escapes slot-tracking
    fn reject_escaping_operands<'a>(
        &mut self,
        operands: impl Iterator<Item = &'a mir::Operand<'tcx>>,
        location: Location,
    ) where
        'tcx: 'a,
    {
        for operand in operands {
            if let Some(place) = operand_place(operand)
                && is_raw_ptr_to_adt(place.ty(self.body, self.tcx).ty)
                && let Some(node) = self.head_node(place)
            {
                self.field_rejects.push(FieldAccessReject {
                    node,
                    kind: FieldAccessRejectKind::EscapesToMemory,
                    location,
                });
            }
        }
    }
}

// use/cast/copy-for-deref of a place — the shapes a pointer store takes in MIR
fn assigned_pointer_source<'tcx>(rvalue: &Rvalue<'tcx>) -> Option<Place<'tcx>> {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_place(operand),
        Rvalue::CopyForDeref(place) => Some(*place),
        _ => None,
    }
}

fn is_raw_ptr_to_adt(ty: ty::Ty<'_>) -> bool {
    ty.is_raw_ptr()
        && ty
            .builtin_deref(true)
            .is_some_and(|pointee| matches!(pointee.kind(), ty::TyKind::Adt(..)))
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
