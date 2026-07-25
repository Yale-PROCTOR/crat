//! Borrow inference

use std::{cell::RefCell, collections::VecDeque};

use errors::{Errors, compute_errors};
use invalidates::{Invalidates, compute_invalidates};
use itertools::Itertools as _;
use killed::{Killed, compute_killed};
use lifetime_flow::{LifetimeFlowResults, analyze_program_lifetime_flow};
use loan_liveness::{LoanLiveness, compute_loan_liveness};
use provenance_liveness::{ProvenanceLiveness, compute_provenance_liveness};
use requires::{ProvenanceRequiresLoan, compute_requires};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{
        Body, HasLocalDecls, Local, Location, Operand, PassWhere, Place, PlaceElem, RETURN_PLACE,
        Rvalue, Terminator,
        pretty::PrettyPrintMirOptions,
        visit::{PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{fmt::DebugWithContext, points::DenseLocationMap};
use rustc_span::def_id::LocalDefId;
use subset_closure::{SubSetClosure, compute_subset_closure};

use super::mir::{CallKind, TerminatorExt};
use crate::utils::{dsa::union_find::UnionFind, rustc::RustProgram};

macro_rules! disallow_interprocedural {
    () => {
        // panic!()
    };
}

mod errors;
mod invalidates;
mod killed;
pub mod lifetime_flow;
mod loan_liveness;
mod places_conflict;
mod provenance_liveness;
mod requires;
mod subset_closure;

rustc_index::newtype_index! {
    #[orderable]
    pub struct Provenance {
    }
}

pub type PromotedMutRefs = FxHashMap<LocalDefId, DenseBitSet<Local>>;
pub type PromotedFieldRefs = FxHashSet<StructFieldSlot>;

#[allow(dead_code)]
pub struct BorrowPromotionResults {
    pub mutable_locals: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    pub shared_locals: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    pub mutable_fields: PromotedFieldRefs,
    pub shared_fields: PromotedFieldRefs,
    pub lifetime_flows: LifetimeFlowResults,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StructFieldSlot {
    pub struct_did: LocalDefId,
    pub field_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProvenanceOwner {
    Local(Local),
    Field(StructFieldSlot),
}

pub enum ProvenanceData {
    PlaceHolder(Local, bool), // (Local, is_mutable)
    Local(Local, bool),       // (Local, is_mutable)
    Field(StructFieldSlot, bool),
}

impl ProvenanceData {
    pub fn owner(&self) -> ProvenanceOwner {
        match self {
            ProvenanceData::PlaceHolder(local, _) | ProvenanceData::Local(local, _) => {
                ProvenanceOwner::Local(*local)
            }
            ProvenanceData::Field(field, _) => ProvenanceOwner::Field(*field),
        }
    }

    pub fn is_mutable(&self) -> bool {
        match self {
            ProvenanceData::PlaceHolder(_, is_mutable) => *is_mutable,
            ProvenanceData::Local(_, is_mutable) => *is_mutable,
            ProvenanceData::Field(_, is_mutable) => *is_mutable,
        }
    }
}

fn is_direct_raw_ptr_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..))
}

fn direct_raw_pointer_field_slot<'tcx, D: HasLocalDecls<'tcx>>(
    local_decls: &D,
    place: Place<'tcx>,
) -> Option<(StructFieldSlot, u8, bool)> {
    let mut base_ty = local_decls.local_decls()[place.local].ty;
    let mut deref_depth = 0u8;

    for (index, projection_elem) in place.projection.iter().enumerate() {
        match projection_elem {
            PlaceElem::Deref => {
                deref_depth = deref_depth.checked_add(1)?;
                base_ty = base_ty.builtin_deref(true)?;
            }
            PlaceElem::Field(field, field_ty) if index + 1 == place.projection.len() => {
                let TyKind::Adt(adt_def, _) = base_ty.kind() else {
                    return None;
                };
                if !adt_def.did().is_local() || !adt_def.is_struct() || adt_def.is_union() {
                    return None;
                }
                let TyKind::RawPtr(_, mutability) = field_ty.kind() else {
                    return None;
                };
                return Some((
                    StructFieldSlot {
                        struct_did: adt_def.did().expect_local(),
                        field_index: field.index(),
                    },
                    deref_depth,
                    mutability.is_mut(),
                ));
            }
            PlaceElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }

    None
}

impl std::fmt::Debug for ProvenanceData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let owner = self.owner();
        let is_mutable = self.is_mutable();
        f.write_fmt(format_args!("'{owner:?} (mutable: {is_mutable})"))
    }
}

/// This formulation is definitely wrong as we don't create [`Origin`]
/// for nested pointers. But I guess it could be fine?
pub struct ProvenanceSet {
    pub(crate) local_data: IndexVec<Local, Option<Provenance>>,
    field_data: FxHashMap<StructFieldSlot, Option<Provenance>>,
    pub(crate) provenance_data: IndexVec<Provenance, ProvenanceData>,
    pub(crate) tree_borrow_local: RefCell<UnionFind<Local>>,
}

impl ProvenanceSet {
    fn provenance_for_owner(&self, owner: ProvenanceOwner) -> Option<Provenance> {
        match owner {
            ProvenanceOwner::Local(local) => self.local_data[local],
            ProvenanceOwner::Field(field) => self.field_data.get(&field).copied().flatten(),
        }
    }

    fn owner_for_place<'tcx, D: HasLocalDecls<'tcx>>(
        &self,
        local_decls: &D,
        place: Place<'tcx>,
    ) -> Option<ProvenanceOwner> {
        if let Some(local) = place.as_local()
            && self.local_data[local].is_some()
        {
            return Some(ProvenanceOwner::Local(local));
        }

        let (field, _, _) = direct_raw_pointer_field_slot(local_decls, place)?;
        self.field_data
            .get(&field)
            .copied()
            .flatten()
            .map(|_| ProvenanceOwner::Field(field))
    }

    pub(crate) fn disable_owner(&mut self, owner: ProvenanceOwner) -> bool {
        match owner {
            ProvenanceOwner::Local(local) => {
                let changed = self.local_data[local].is_some();
                self.local_data[local] = None;
                changed
            }
            ProvenanceOwner::Field(field) => {
                let Some(provenance) = self.field_data.get_mut(&field) else {
                    return false;
                };
                let changed = provenance.is_some();
                *provenance = None;
                changed
            }
        }
    }
}

pub trait HasProvenanceSet {
    fn provenance_set<I, J>(&self, is_candidate: I, is_mutable: J) -> ProvenanceSet
    where
        I: Fn(Local) -> bool,
        J: Fn(Local) -> bool;
}

impl HasProvenanceSet for Body<'_> {
    fn provenance_set<I, J>(&self, is_candidate: I, is_mutable: J) -> ProvenanceSet
    where
        I: Fn(Local) -> bool,
        J: Fn(Local) -> bool,
    {
        let body = self;
        let mut local_data = IndexVec::from_elem_n(None, body.local_decls.len());
        let mut field_data = FxHashMap::default();
        let mut provenance_data = IndexVec::new();

        for (provenance, (local, local_decl)) in local_data
            .iter_mut()
            .zip(body.local_decls.iter_enumerated())
        {
            if local_decl.ty.is_any_ptr() && is_candidate(local) {
                let data = if local.index() <= body.arg_count {
                    ProvenanceData::PlaceHolder(local, is_mutable(local)) // Parameters
                } else {
                    ProvenanceData::Local(local, is_mutable(local)) // Locals
                };
                *provenance = Some(provenance_data.push(data));
            }
        }

        for (field, is_mutable) in collect_direct_raw_pointer_field_slots(body) {
            field_data.entry(field).or_insert_with(|| {
                Some(provenance_data.push(ProvenanceData::Field(field, is_mutable)))
            });
        }

        ProvenanceSet {
            local_data,
            field_data,
            provenance_data,
            tree_borrow_local: RefCell::new(UnionFind::new(body.local_decls.len())),
        }
    }
}

fn collect_direct_raw_pointer_field_slots<'tcx>(
    body: &Body<'tcx>,
) -> FxHashMap<StructFieldSlot, bool> {
    struct Vis<'body, 'tcx> {
        body: &'body Body<'tcx>,
        fields: FxHashMap<StructFieldSlot, bool>,
    }

    impl<'tcx> Visitor<'tcx> for Vis<'_, 'tcx> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            if let Some((field, _, is_mutable)) = direct_raw_pointer_field_slot(self.body, *place) {
                self.fields
                    .entry(field)
                    .and_modify(|mutable| *mutable |= is_mutable)
                    .or_insert(is_mutable);
            }
            self.super_place(place, context, location);
        }
    }

    let mut vis = Vis {
        body,
        fields: FxHashMap::default(),
    };
    vis.visit_body(body);
    vis.fields
}

fn direct_raw_pointer_field_slots_in_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut ty: Ty<'tcx>,
) -> Vec<StructFieldSlot> {
    let mut fields = vec![];
    loop {
        if let TyKind::Adt(adt_def, args) = ty.kind()
            && adt_def.did().is_local()
            && adt_def.is_struct()
            && !adt_def.is_union()
        {
            for (field_index, field_def) in adt_def.all_fields().enumerate() {
                if is_direct_raw_ptr_ty(field_def.ty(tcx, args)) {
                    fields.push(StructFieldSlot {
                        struct_did: adt_def.did().expect_local(),
                        field_index,
                    });
                }
            }
        }
        let Some(pointee) = ty.builtin_deref(true) else {
            break;
        };
        ty = pointee;
    }
    fields
}

pub struct GBorrowInferCtxt {
    pub provenances: FxHashMap<LocalDefId, ProvenanceSet>,
    pub lifetime_flows: LifetimeFlowResults,
    pub field_users: FxHashMap<StructFieldSlot, FxHashSet<LocalDefId>>,
}

impl GBorrowInferCtxt {
    pub fn new<I, J, K, L>(program: &RustProgram, is_candidate: I, is_mutable: K) -> Self
    where
        I: Fn(LocalDefId) -> J,
        J: Fn(Local) -> bool,
        K: Fn(LocalDefId) -> L,
        L: Fn(Local) -> bool,
    {
        let lifetime_flows = analyze_program_lifetime_flow(program);
        let mut provenances = FxHashMap::default();
        let mut field_users: FxHashMap<StructFieldSlot, FxHashSet<LocalDefId>> =
            FxHashMap::default();
        for f in program.functions.iter().copied() {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(f)
                .borrow();
            let is_candidate = is_candidate(f);
            let is_mutable = is_mutable(f);
            provenances.insert(f, body.provenance_set(is_candidate, is_mutable));
            for field in collect_direct_raw_pointer_field_slots(&body)
                .keys()
                .copied()
            {
                field_users.entry(field).or_default().insert(f);
            }
        }

        GBorrowInferCtxt {
            provenances,
            lifetime_flows,
            field_users,
        }
    }

    pub fn _all_pointers(program: &RustProgram) -> Self {
        GBorrowInferCtxt::new(program, |_| |_| true, |_| |_| false)
    }

    // Classify immutable pointers (their loans do not demote pointers)
    pub fn classified_pointers(
        program: &RustProgram,
        mutables: &FxHashMap<LocalDefId, IndexVec<Local, bool>>,
    ) -> Self {
        GBorrowInferCtxt::new(
            program,
            |_| |_| true,
            |did| {
                let mutables = mutables.get(&did);
                move |local| {
                    if let Some(mutables) = mutables {
                        mutables[local]
                    } else {
                        false
                    }
                }
            },
        )
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "L_({})"]
    pub struct Loan {
    }
}

impl<C> DebugWithContext<C> for Loan {}

pub struct BorrowData<'tcx> {
    location: Location,
    pub(crate) borrowed: Place<'tcx>,
    pub(crate) assigned: Borrower,
}

impl BorrowData<'_> {
    pub(crate) fn location(&self) -> Location {
        self.location
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Borrower {
    Assign(ProvenanceOwner),
    #[allow(unused)]
    CallArg(LocalDefId, usize),
}

impl std::fmt::Debug for BorrowData<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?} @ {:?}", self.borrowed, self.location))
    }
}

pub struct BorrowSet<'tcx> {
    pub(crate) loans: IndexVec<Loan, BorrowData<'tcx>>,
    location_map: FxHashMap<Location, Vec<Loan>>,
    pub(crate) local_map: SparseBitMatrix<Local, Loan>,
}

pub trait HasBorrowSet<'tcx> {
    fn borrow_set<'local, 'global: 'local>(
        &self,
        tcx: TyCtxt<'tcx>,
        provenance_set: &'local ProvenanceSet,
        global_borrow_ctxt: &'global GBorrowInferCtxt,
    ) -> BorrowSet<'tcx>;
}

impl<'tcx> HasBorrowSet<'tcx> for Body<'tcx> {
    fn borrow_set<'local, 'global: 'local>(
        &self,
        tcx: TyCtxt<'tcx>,
        provenance_set: &'local ProvenanceSet,
        global_borrow_ctxt: &'global GBorrowInferCtxt,
    ) -> BorrowSet<'tcx> {
        struct Vis<'tcx, 'this, D> {
            loans: IndexVec<Loan, BorrowData<'tcx>>,
            location_map: FxHashMap<Location, Vec<Loan>>,
            local_decl: &'this D,
            tcx: TyCtxt<'tcx>,
            provenance_set: &'this ProvenanceSet,
            global_borrow_ctxt: &'this GBorrowInferCtxt,
        }
        impl<'tcx, 'this, D: HasLocalDecls<'tcx>> Visitor<'tcx> for Vis<'tcx, 'this, D> {
            fn visit_assign(
                &mut self,
                lhs: &Place<'tcx>,
                rvalue: &Rvalue<'tcx>,
                location: Location,
            ) {
                let Some(assigned_owner) =
                    self.provenance_set.owner_for_place(self.local_decl, *lhs)
                else {
                    return self.super_assign(lhs, rvalue, location);
                };

                let rvalue_ty = rvalue.ty(self.local_decl, self.tcx);
                if !rvalue_ty.is_any_ptr() {
                    return self.super_assign(lhs, rvalue, location);
                }

                match rvalue {
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        let mut loans = vec![];
                        let loan = self.loans.push(BorrowData {
                            location,
                            borrowed: *place,
                            assigned: Borrower::Assign(assigned_owner),
                        });
                        loans.push(loan);

                        for other_local in self
                            .provenance_set
                            .tree_borrow_local
                            .borrow_mut()
                            .group(place.local)
                        {
                            if place.local == other_local {
                                continue;
                            }
                            let loan = self.loans.push(BorrowData {
                                location,
                                borrowed: Place::from(other_local),
                                assigned: Borrower::Assign(assigned_owner),
                            });
                            loans.push(loan);
                        }

                        self.location_map.insert(location, loans);
                    }
                    Rvalue::CopyForDeref(place)
                    | Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                        let mut loans = vec![];
                        let loan = self.loans.push(BorrowData {
                            location,
                            borrowed: place.project_deeper(&[PlaceElem::Deref], self.tcx),
                            assigned: Borrower::Assign(assigned_owner),
                        });
                        loans.push(loan);

                        for other_local in self
                            .provenance_set
                            .tree_borrow_local
                            .borrow_mut()
                            .group(place.local)
                        {
                            if place.local == other_local {
                                continue;
                            }
                            let loan = self.loans.push(BorrowData {
                                location,
                                borrowed: Place::from(other_local),
                                assigned: Borrower::Assign(assigned_owner),
                            });
                            loans.push(loan);
                        }
                        self.location_map.insert(location, loans);
                    }
                    _ => {}
                }
            }

            fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
                let Some(mir_call) = terminator.as_call(self.tcx) else {
                    return self.super_terminator(terminator, location);
                };
                disallow_interprocedural!();

                // specially handle borrowing method (e.g., offset) calls for pointers,
                // just like assingments of Ralue::Use(Operand::Copy(place) | Operand::Move(place)).
                if let CallKind::RustLib(def_id) = &mir_call.func {
                    if is_borrowing_method(*def_id, self.tcx) {
                        let arg0 = &mir_call.args[0].node;
                        if let Some(arg0_place) = arg0.place()
                            && let Some(assigned_owner) = self
                                .provenance_set
                                .owner_for_place(self.local_decl, mir_call.destination)
                        {
                            let mut loans = vec![];
                            let loan = self.loans.push(BorrowData {
                                location,
                                borrowed: arg0_place.project_deeper(&[PlaceElem::Deref], self.tcx),
                                assigned: Borrower::Assign(assigned_owner),
                            });
                            loans.push(loan);

                            for other_local in self
                                .provenance_set
                                .tree_borrow_local
                                .borrow_mut()
                                .group(arg0_place.local)
                            {
                                if arg0_place.local == other_local {
                                    continue;
                                }
                                let loan = self.loans.push(BorrowData {
                                    location,
                                    borrowed: Place::from(other_local),
                                    assigned: Borrower::Assign(assigned_owner),
                                });
                                loans.push(loan);
                            }
                            self.location_map.insert(location, loans);
                        }
                    }
                } else if let Some(callee) = mir_call.func.did()
                    && let Some(callee) = callee.as_local()
                    && let Some(callee_provenance_set) =
                        self.global_borrow_ctxt.provenances.get(&callee)
                {
                    for (arg_index, arg) in mir_call.args.iter().enumerate() {
                        let arg = &arg.node;
                        if let Some(arg) = arg.place() {
                            let callee_local = Local::from_usize(arg_index + 1);
                            if callee_provenance_set.local_data[callee_local].is_some() {
                                let loan = self.loans.push(BorrowData {
                                    location,
                                    borrowed: arg.project_deeper(&[PlaceElem::Deref], self.tcx),
                                    assigned: Borrower::CallArg(callee, arg_index),
                                });
                                // self.location_map.insert(location, loan);
                                self.location_map
                                    .entry(location)
                                    .and_modify(|loans| loans.push(loan))
                                    .or_default()
                                    .push(loan);
                            }
                        }
                    }
                };
                self.super_terminator(terminator, location)
            }
        }

        let mut vis = Vis {
            loans: IndexVec::new(),
            location_map: FxHashMap::default(),
            local_decl: self,
            tcx,
            provenance_set,
            global_borrow_ctxt,
        };
        vis.visit_body(self);

        let Vis {
            loans,
            location_map,
            ..
        } = vis;

        let mut local_map = SparseBitMatrix::new(loans.len());

        for (loan, borrow_data) in loans.iter_enumerated() {
            local_map.insert(borrow_data.borrowed.local, loan);
        }

        BorrowSet {
            loans,
            location_map,
            local_map,
        }
    }
}

#[derive(Clone, Copy)]
pub struct SubsetConstraint {
    sup: Provenance,
    sub: Provenance,
    _location: Location,
}

#[derive(Clone, Copy)]
pub struct MembershipConstraint {
    loan: Loan,
    provenance: Provenance,
}

pub struct ProvenanceConstraintGraph {
    subset: Vec<SubsetConstraint>,
    membership: Vec<MembershipConstraint>,
}

impl ProvenanceConstraintGraph {
    pub fn new<'tcx, 'local, 'global: 'local>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        provenance_set: &'local ProvenanceSet,
        global_borrow_ctxt: &'global GBorrowInferCtxt,
    ) -> Self {
        struct Vis<'this, 'tcx> {
            tcx: TyCtxt<'tcx>,
            body: &'this Body<'tcx>,
            graph: &'this mut ProvenanceConstraintGraph,
            borrow_set: &'this BorrowSet<'tcx>,
            provenance_set: &'this ProvenanceSet,
            global_borrow_ctxt: &'this GBorrowInferCtxt,
        }

        impl<'tcx> Visitor<'tcx> for Vis<'_, 'tcx> {
            fn visit_assign(
                &mut self,
                place: &Place<'tcx>,
                rvalue: &Rvalue<'tcx>,
                location: Location,
            ) {
                let Some(loans) = self.borrow_set.location_map.get(&location) else {
                    return self.super_assign(place, rvalue, location);
                };
                for &loan in loans {
                    let BorrowData {
                        location: _,
                        borrowed: rhs,
                        ..
                    } = &self.borrow_set.loans[loan];

                    let Some(lhs_owner) = self.provenance_set.owner_for_place(self.body, *place)
                    else {
                        return self.super_assign(place, rvalue, location);
                    };
                    let lhs_provenance =
                        self.provenance_set.provenance_for_owner(lhs_owner).unwrap();

                    self.graph.membership.push(MembershipConstraint {
                        loan,
                        provenance: lhs_provenance,
                    });

                    if !rhs.projection.is_empty()
                        && rhs
                            .projection
                            .iter()
                            .all(|projection| matches!(projection, PlaceElem::Deref))
                            // rhs provenance might have been disabled by previous iteration, so need a guard here
                        && self.provenance_set.local_data[rhs.local].is_some()
                    {
                        let rhs_provenance = self.provenance_set.local_data[rhs.local].unwrap();
                        self.graph.subset.push(SubsetConstraint {
                            sup: lhs_provenance,
                            sub: rhs_provenance,
                            _location: location,
                        });
                    }
                }
            }

            fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
                let Some(mir_call) = terminator.as_call(self.tcx) else {
                    return self.super_terminator(terminator, location);
                };
                disallow_interprocedural!();
                // specially handle borrowing method (e.g., offset) calls for pointers,
                // just like assingments of Ralue::Use(Operand::Copy(place) | Operand::Move(place)).
                if let CallKind::RustLib(def_id) = &mir_call.func {
                    if is_borrowing_method(*def_id, self.tcx) {
                        let arg0 = &mir_call.args[0].node;
                        if let Some(arg0_place) = arg0.place() {
                            self.visit_assign(
                                &mir_call.destination,
                                &Rvalue::Use(Operand::Copy(arg0_place)),
                                location,
                            );
                        }
                    }
                } else if let Some(callee) = mir_call.func.did()
                    && let Some(callee) = callee.as_local()
                    && let Some(callee_provenance_set) =
                        self.global_borrow_ctxt.provenances.get(&callee)
                {
                    for (arg_index, arg) in mir_call.args.iter().enumerate() {
                        let arg = &arg.node;
                        if let Some(_arg) = arg.place() {
                            let callee_local = Local::from_usize(arg_index + 1);
                            if callee_provenance_set.local_data[callee_local].is_some() {
                                // TODO incorporating interprocedural constraints
                            }
                        }
                    }
                };
            }
        }

        let mut graph = ProvenanceConstraintGraph {
            subset: vec![],
            membership: vec![],
        };

        Vis {
            tcx,
            body,
            graph: &mut graph,
            borrow_set,
            provenance_set,
            global_borrow_ctxt,
        }
        .visit_body(body);

        if let Some(lifetime_flow) = global_borrow_ctxt
            .lifetime_flows
            .get(&body.source.def_id().expect_local())
        {
            for (source, target) in lifetime_flow.body.depth0_value_flows() {
                let Some(source_provenance) = provenance_set.provenance_for_owner(source) else {
                    continue;
                };
                let Some(target_provenance) = provenance_set.provenance_for_owner(target) else {
                    continue;
                };
                graph.subset.push(SubsetConstraint {
                    sup: target_provenance,
                    sub: source_provenance,
                    _location: Location::START,
                });
            }
        }

        graph
    }
}

pub fn is_borrowing_method(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    !def_id.is_local() && tcx.def_kind(def_id) == rustc_hir::def::DefKind::AssocFn && {
        let name = tcx.item_name(def_id);
        let name = name.as_str();
        name == "offset" || name == "as_ptr" || name == "as_mut_ptr"
    }
}

#[allow(unused)]
pub struct BorrowInferenceResults<'tcx> {
    // pub provenance_set: ProvenanceSet,
    pub borrow_set: BorrowSet<'tcx>,
    pub constraint_graph: ProvenanceConstraintGraph,
    pub location_map: DenseLocationMap,
    pub provenance_liveness: ProvenanceLiveness,
    pub killed: Killed,
    pub subset_closure: SubSetClosure,
    pub requires: ProvenanceRequiresLoan,
    pub loan_liveness: LoanLiveness,
    pub invalidates: Invalidates,
    pub errors: Errors,
}

pub fn borrow_inference<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    global_borrow_ctxt: &GBorrowInferCtxt,
) -> BorrowInferenceResults<'tcx> {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();

    let provenance_set = global_borrow_ctxt.provenances.get(&def_id).unwrap();
    let borrow_set = body.borrow_set(tcx, provenance_set, global_borrow_ctxt);
    let location_map = DenseLocationMap::new(body);
    let provenance_liveness = compute_provenance_liveness(&location_map, tcx, body, provenance_set);
    let killed = compute_killed(body, tcx, &location_map, &borrow_set);
    let constraint_graph =
        ProvenanceConstraintGraph::new(tcx, body, &borrow_set, provenance_set, global_borrow_ctxt);
    let subset_closure = compute_subset_closure(provenance_set, &constraint_graph);
    let requires = compute_requires(&borrow_set, provenance_set, &constraint_graph);
    let loan_liveness = compute_loan_liveness(
        tcx,
        body,
        &borrow_set,
        &location_map,
        &provenance_liveness,
        &requires,
        &killed,
    );
    let invalidates = compute_invalidates(tcx, body, &borrow_set, provenance_set, &location_map);
    let errors = compute_errors(&borrow_set, &loan_liveness, &invalidates);

    BorrowInferenceResults {
        borrow_set,
        location_map,
        provenance_liveness,
        killed,
        constraint_graph,
        subset_closure,
        requires,
        loan_liveness,
        invalidates,
        errors,
    }
}

/// One borrow conflict (an invalid loan) attributed to its owners: the slot that
/// issued the loan (`assigned`) and the slots whose provenance required the loan and
/// is live at the error point. Keyed by the public `ProvenanceOwner` so callers
/// outside this module can translate to their own slot space. This is the raw
/// material for the unified analysis's §8 guarded-exclusion clauses.
#[derive(Clone, Debug)]
pub struct ConflictEdge {
    pub issuer: Option<ProvenanceOwner>,
    pub requirers: Vec<ProvenanceOwner>,
}

/// §8 verifier (read-only): run `borrow_inference` with a given ref-candidacy +
/// mutability and return, per function, the conflict edges (invalid loans attributed
/// to their issuer/requirer owners). Mirrors the error-extraction of
/// `demote_pointers_iterative_with_fields` WITHOUT mutating the `ProvenanceSet` — so
/// it is faithful for a Round-0 (all-candidate) set; a *partial* candidacy that
/// represents demotions would also need the `tree_borrow_local` union replay the
/// demotion loop performs (the caller's concern).
pub fn borrow_conflicts<I, J, K, L>(
    program: &RustProgram,
    is_candidate: I,
    is_mutable: K,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let ctxt = GBorrowInferCtxt::new(program, is_candidate, is_mutable);
    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let inference = borrow_inference(program.tcx, f, &ctxt);
        let invalid_loans = invalid_loan_set(&inference);
        if invalid_loans.is_empty() {
            continue;
        }
        let provenance_set = ctxt.provenances.get(&f).unwrap();
        out.insert(
            f,
            extract_conflict_edges(&inference, provenance_set, &invalid_loans),
        );
    }
    out
}

/// The set of invalid loans (live ∧ invalidated) across all error points.
fn invalid_loan_set(inference: &BorrowInferenceResults<'_>) -> DenseBitSet<Loan> {
    let mut invalid_loans = DenseBitSet::new_empty(inference.borrow_set.loans.len());
    for row in inference.errors.rows() {
        if let Some(loans) = inference.errors.row(row) {
            invalid_loans.union(loans);
        }
    }
    invalid_loans
}

/// Attribute each invalid loan to its issuer (`assigned`) and the live provenances
/// that required it — the `ConflictEdge` shape consumed by the §8 guard encoder.
/// Shared by `borrow_conflicts` (round-0) and `borrow_conflicts_replaying` (CEGAR).
fn extract_conflict_edges(
    inference: &BorrowInferenceResults<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
) -> Vec<ConflictEdge> {
    let BorrowInferenceResults {
        borrow_set,
        provenance_liveness,
        requires,
        errors,
        ..
    } = inference;

    let mut edges = Vec::new();
    for loan in invalid_loans.iter() {
        let borrow_data = &borrow_set.loans[loan];
        let issuer = match borrow_data.assigned {
            Borrower::Assign(owner) => Some(owner),
            Borrower::CallArg(..) => None,
        };
        let mut requirers = Vec::new();
        let mut seen: FxHashSet<Provenance> = FxHashSet::default();
        for row in errors.rows() {
            let Some(loans) = errors.row(row) else {
                continue;
            };
            if !loans.contains(loan) {
                continue;
            }
            let Some(live) = provenance_liveness.row(row) else {
                continue;
            };
            for provenance in live.iter() {
                if requires.contains(provenance, loan) && seen.insert(provenance) {
                    requirers.push(provenance_set.provenance_data[provenance].owner());
                }
            }
        }
        edges.push(ConflictEdge { issuer, requirers });
    }
    edges
}

/// §8 BB2-i — the CEGAR validate verifier with **union replay**. Unlike
/// `borrow_conflicts` (round-0, no demotions), this takes a *partial* candidacy: a
/// pointer local is a `Ref` candidate iff `is_ref`, induces a borrow demotion+union
/// iff `is_raw`, and is neither (an `Owning` slot) otherwise. It reproduces the
/// model-dependent loans that the chosen `Raw` slots create — replaying
/// `demote_pointers_iterative_with_fields`'s `tree_borrow_local` union via the shared
/// `collect_invalid_loan_demotions` — then returns the conflict edges that remain.
///
/// Algorithm: build the ctxt with candidacy `is_ref ∨ is_raw` (so `Raw` slots still
/// carry loans whose `borrowed.local` is the union base; `Owning` slots are excluded
/// and induce no union). For each function, demote the model's `Raw` witnesses with
/// their unions to a fixpoint (each round demotes ≥1 fresh `Raw` local, so ≤|Raw|
/// rounds), then extract the residual conflicts over the surviving `Ref` candidates.
///
/// Invariant (`assert`ed, release-active since BB3-c): every model-`Raw` local that was NOT a demotion witness
/// (so it kept its provenance through the fixpoint) is *inert* — it appears in no residual
/// conflict edge. This is the relaxation of an earlier, too-strong "every `Raw` slot is a
/// witness" assert. A non-witness `Raw` local can legitimately arise from coherence's
/// flow-insensitive equate-closure: a DEAD copy `let _r = p` is `equate`d to `p`, so
/// committing `¬ref(p)` drags `_r` `Raw`, yet `_r` is never live at the conflict and is
/// never demoted. Such a local cannot be the live issuer/requirer of a residual invalid
/// loan (else `to_demote` would be non-empty and the loop would not have broken), and
/// `extract_conflict_edges` draws owners from exactly those live sources — so it is
/// provably absent from `edges`. The `assert` is a tripwire on that inert-ness; BB3-c made it
/// release-active so it guards the future BO→codegen path — in the proven-inert valid case it
/// never fires (a release panic here would mean the inert-ness proof was wrong, i.e. a genuine
/// soundness bug, not the harmless dead-copy case).
///
/// CAVEAT (adversarial review, 2026-06-24): the inert-ness invariant also absorbs the
/// Owning-issuer case (a loan whose `issuer` is classed `Owning` vanishes under the replay
/// candidacy, leaving a former requirer non-witness) — that requirer is likewise inert.
/// What stays DEFERRED to BB3 is the separate *under-report*: an `Owning` slot issues no
/// loan, so a conflict *caused by* an `Owning` pointer's exclusivity is invisible to the
/// replay. BO output is unconsumed by codegen (the §8 guardrail) until that lands.
pub fn borrow_conflicts_replaying<I, J, M, N, K, L>(
    program: &RustProgram,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    // Pass-1 candidacy keeps `Raw` slots as candidates so their loans (and union
    // bases) exist; the demotion loop then removes them. `Owning` slots (neither
    // ref nor raw) are non-candidates from the start and induce no union.
    let is_candidate = |did: LocalDefId| {
        let ref_f = is_ref(did);
        let raw_f = is_raw(did);
        move |local: Local| ref_f(local) || raw_f(local)
    };
    let mut ctxt = GBorrowInferCtxt::new(program, is_candidate, is_mutable);

    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let is_raw_f = is_raw(f);

        // Demote the model's `Raw` witnesses (with their unions) to a fixpoint, then
        // collect the residual conflict edges from the final inference.
        let edges = loop {
            let inference = borrow_inference(program.tcx, f, &ctxt);
            let invalid_loans = invalid_loan_set(&inference);
            if invalid_loans.is_empty() {
                break Vec::new();
            }

            // Decide which `Raw` witnesses to demote this round (still candidates).
            let to_demote: Vec<(Local, Local)> = {
                let provenance_set = ctxt.provenances.get(&f).unwrap();
                let demotions =
                    collect_invalid_loan_demotions(&inference, provenance_set, &invalid_loans);
                demotions
                    .local_witnesses
                    .into_iter()
                    .filter(|(local, _base)| {
                        is_raw_f(*local) && provenance_set.local_data[*local].is_some()
                    })
                    .collect()
            };

            if to_demote.is_empty() {
                // No more `Raw` demotions possible: the remaining invalid loans are
                // genuine conflicts over the surviving `Ref` candidates.
                let provenance_set = ctxt.provenances.get(&f).unwrap();
                break extract_conflict_edges(&inference, provenance_set, &invalid_loans);
            }

            drop(inference);
            let provenance_set = ctxt.provenances.get_mut(&f).unwrap();
            for (local, base) in to_demote {
                provenance_set.disable_owner(ProvenanceOwner::Local(local));
                provenance_set.tree_borrow_local.get_mut().union(local, base);
            }
        };

        // Stray-Raw inert-ness invariant (relaxed from the former "every Raw slot is a
        // demotion witness", which coherence violates). A model-`Raw` local that was NOT a
        // witness — so it kept its provenance (`local_data.is_some()`) through the demotion
        // fixpoint — can legitimately arise from coherence's flow-insensitive equate-closure
        // (e.g. a DEAD copy `let _r = p`: committing `¬ref(p)` drags `_r` Raw, yet `_r` is
        // never live at the conflict). Such a local is provably *inert*: it cannot be the
        // live issuer/requirer of a residual invalid loan (else `to_demote` would have been
        // non-empty and the loop would not have broken), and `extract_conflict_edges` draws
        // owners from exactly those live sources — so it appears in NO residual edge. We
        // assert that inert-ness (a real tripwire) instead of panicking on the valid case.
        let provenance_set = ctxt.provenances.get(&f).unwrap();
        assert!(
            provenance_set
                .local_data
                .iter_enumerated()
                .all(|(local, data)| {
                    if !(is_raw_f(local) && data.is_some()) {
                        return true;
                    }
                    // inert: named by no residual conflict edge (issuer or requirer)
                    !edges.iter().any(|e| {
                        matches!(e.issuer, Some(ProvenanceOwner::Local(l)) if l == local)
                            || e.requirers
                                .iter()
                                .any(|o| matches!(o, ProvenanceOwner::Local(l) if *l == local))
                    })
                }),
            "BB2-i stray-Raw: a non-witness Raw local appears in a residual edge in {f:?} \
             — the inert-ness invariant (stray Raw ⟹ in no residual edge) is violated"
        );

        if !edges.is_empty() {
            out.insert(f, edges);
        }
    }
    out
}

#[allow(unused)]
pub fn dump_borrow_inference_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    inference: &BorrowInferenceResults<'tcx>,
    global_borrow_ctxt: &GBorrowInferCtxt,
    w: &mut dyn std::io::Write,
) -> std::io::Result<()> {
    let BorrowInferenceResults {
        borrow_set,
        location_map,
        provenance_liveness,
        killed: _killed,
        constraint_graph: _constraint_graph,
        subset_closure: _subset_closure,
        requires: _requires,
        loan_liveness,
        invalidates: _invalidates,
        errors,
    } = inference;
    let provenance_set = global_borrow_ctxt
        .provenances
        .get(&body.source.def_id().expect_local())
        .unwrap();

    rustc_middle::mir::pretty::write_mir_fn(
        tcx,
        body,
        &mut |pass_where, w| match pass_where {
            PassWhere::BeforeLocation(location) => {
                let point_index = location_map.point_from_location(location);
                let live_loans = loan_liveness
                    .row(point_index)
                    .iter()
                    .flat_map(|loans| loans.iter())
                    .map(|loan| format!("{:?}", &borrow_set.loans[loan]))
                    .join(", ");

                w.write_fmt(format_args!("\t// live loans: [{live_loans}]\n",))?;

                Ok(())
            }
            PassWhere::AfterLocation(location) => {
                let point_index = location_map.point_from_location(location);
                let errors = errors
                    .row(point_index)
                    .iter()
                    .flat_map(|loans| loans.iter())
                    .map(|loan| format!("{:?}", &borrow_set.loans[loan]))
                    .join(", ");

                if !errors.is_empty() {
                    let error_notification = format!("errors: [{errors}]");
                    w.write_fmt(format_args!("\t// {error_notification}\n"))?;
                }

                let live_provenances = provenance_liveness
                    .row(point_index)
                    .iter()
                    .flat_map(|provenances| provenances.iter())
                    .map(|provenance| format!("{:?}", provenance_set.provenance_data[provenance]))
                    .join(", ");

                w.write_fmt(format_args!(
                    "\t// live provenances: [{live_provenances}]\n",
                ))?;

                Ok(())
            }
            _ => Ok(()),
        },
        w,
        PrettyPrintMirOptions {
            include_extra_comments: false,
        },
    )?;

    for point_index in errors.rows() {
        let illegal_accesses = errors
            .row(point_index)
            .iter()
            .flat_map(|loans| loans.iter())
            .map(|loan| format!("{:?}", &borrow_set.loans[loan]))
            .join(", ");

        if illegal_accesses.is_empty() {
            continue;
        }

        writeln!(
            w,
            "illegal accesses: [{illegal_accesses}] @ {:?}",
            location_map.to_location(point_index)
        )?;
    }

    Ok(())
}

#[allow(unused)]
pub fn dump_coarse_inferred_bounds(program: &RustProgram, global_borrow_ctxt: &GBorrowInferCtxt) {
    let tcx = program.tcx;

    for f in program.functions.iter() {
        let body = &*program
            .tcx
            .mir_drops_elaborated_and_const_checked(f)
            .borrow();

        let provenance_set = &global_borrow_ctxt.provenances[f];
        let return_place = RETURN_PLACE;
        let Some(return_provenance) = provenance_set.local_data[return_place] else {
            continue;
        };
        println!("{} inferred bounds:", program.tcx.def_path_str(*f));
        let BorrowInferenceResults { subset_closure, .. } =
            borrow_inference(tcx, *f, global_borrow_ctxt);

        for arg in body.args_iter() {
            if let Some(arg_provenance) = provenance_set.local_data[arg]
                && subset_closure.contains(arg_provenance, return_provenance)
            {
                for var_debug_info in body.var_debug_info.iter() {
                    if var_debug_info
                        .argument_index
                        .is_some_and(|arg_index| arg_index == arg.as_u32() as u16)
                    {
                        println!("'{}: 'return", var_debug_info.name);
                    }
                }
            }
        }
    }
}

/// The demotions an invalid-loan set induces, collected WITHOUT mutating the
/// `ProvenanceSet`. Each `(local, base)` in `local_witnesses` means "demoting
/// `local` unions it with `base`" — `base` is the invalid loan's `borrowed.local`,
/// exactly as `demote_pointers_iterative_with_fields` does. `Field` owners are
/// demoted but carry no union, so they are returned separately. This is the shared,
/// faithful core consumed by both the production demote loop (which applies every
/// witness) and the §8 CEGAR validate replay (which gates them on the model's `Raw`
/// slots) — a single source of truth so the union semantics cannot diverge.
pub(crate) struct InvalidLoanDemotions {
    pub local_witnesses: Vec<(Local, Local)>,
    pub demoted_fields: FxHashSet<StructFieldSlot>,
}

/// Collect the demotion witnesses induced by `invalid_loans` from one function's
/// inference results. Mirrors the requirer + issuer demotion paths of
/// `demote_pointers_iterative_with_fields` but is pure (no mutation), so callers
/// decide which witnesses to apply.
pub(crate) fn collect_invalid_loan_demotions(
    inference: &BorrowInferenceResults<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
) -> InvalidLoanDemotions {
    let BorrowInferenceResults {
        borrow_set,
        errors,
        provenance_liveness,
        requires,
        ..
    } = inference;

    let mut local_witnesses = Vec::new();
    let mut demoted_fields = FxHashSet::default();

    // Requirer path: every live provenance that requires an invalid loan is demoted
    // and unioned with that loan's borrowed cell.
    for loan in invalid_loans.iter() {
        let borrow_data = &borrow_set.loans[loan];
        for row in errors.rows() {
            let Some(loans) = errors.row(row) else {
                continue;
            };
            if !loans.contains(loan) {
                continue;
            }
            let Some(live_provenances) = provenance_liveness.row(row) else {
                continue;
            };
            for provenance in live_provenances.iter() {
                if !requires.contains(provenance, loan) {
                    continue;
                }
                match provenance_set.provenance_data[provenance].owner() {
                    ProvenanceOwner::Local(local) => {
                        local_witnesses.push((local, borrow_data.borrowed.local));
                    }
                    ProvenanceOwner::Field(field) => {
                        demoted_fields.insert(field);
                    }
                }
            }
        }
    }

    // Issuer path: the loan's assigned borrower is demoted and unioned likewise.
    for loan in invalid_loans.iter() {
        let borrow_data = &borrow_set.loans[loan];
        if let Borrower::Assign(assigned) = borrow_data.assigned {
            match assigned {
                ProvenanceOwner::Local(local) => {
                    local_witnesses.push((local, borrow_data.borrowed.local));
                }
                ProvenanceOwner::Field(field) => {
                    demoted_fields.insert(field);
                }
            }
        }
    }

    InvalidLoanDemotions {
        local_witnesses,
        demoted_fields,
    }
}

#[allow(dead_code)]
pub fn demote_pointers_iterative(
    program: &RustProgram,
    global_borrow_ctxt: &mut GBorrowInferCtxt,
) -> FxHashMap<LocalDefId, DenseBitSet<Local>> {
    demote_pointers_iterative_with_fields(program, global_borrow_ctxt).locals
}

pub struct DemotionResults {
    pub locals: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    pub fields: FxHashSet<StructFieldSlot>,
}

pub fn demote_pointers_iterative_with_fields(
    program: &RustProgram,
    global_borrow_ctxt: &mut GBorrowInferCtxt,
) -> DemotionResults {
    let mut demoted = FxHashMap::default();
    let mut demoted_fields = FxHashSet::default();

    let tcx = program.tcx;

    for &f in &program.functions {
        let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        demoted.insert(f, DenseBitSet::new_empty(body.local_decls.len()));
    }

    let mut worklist: VecDeque<LocalDefId> = program.functions.iter().copied().collect();
    let mut in_worklist: FxHashSet<LocalDefId> = worklist.iter().copied().collect();

    while let Some(f) = worklist.pop_front() {
        in_worklist.remove(&f);

        let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();

        let inference = borrow_inference(tcx, f, global_borrow_ctxt);

        let mut invalid_loans = DenseBitSet::new_empty(inference.borrow_set.loans.len());
        for row in inference.errors.rows() {
            if let Some(loans) = inference.errors.row(row) {
                invalid_loans.union(loans);
            }
        }

        if invalid_loans.is_empty() {
            continue;
        }

        let mut demoted_locals = DenseBitSet::new_empty(body.local_decls.len());
        let mut demoted_field_slots = FxHashSet::default();

        let changed = {
            let provenance_set = global_borrow_ctxt.provenances.get_mut(&f).unwrap();

            // Collect the demotion witnesses the invalid loans induce (requirer +
            // issuer paths), then apply every one: production demotes all of them.
            // The §8 CEGAR replay reuses `collect_invalid_loan_demotions` but applies
            // only the model's `Raw` witnesses.
            let InvalidLoanDemotions {
                local_witnesses,
                demoted_fields,
            } = collect_invalid_loan_demotions(&inference, provenance_set, &invalid_loans);
            for (local, base) in local_witnesses {
                demoted_locals.insert(local);
                provenance_set.tree_borrow_local.get_mut().union(local, base);
            }
            demoted_field_slots.extend(demoted_fields);

            let mut changed = false;
            for (local, provenance) in provenance_set.local_data.iter_enumerated_mut() {
                if demoted_locals.contains(local) && provenance.is_some() {
                    changed = true;
                    *provenance = None;
                }
            }
            for field in demoted_field_slots.iter().copied() {
                changed |= provenance_set.disable_owner(ProvenanceOwner::Field(field));
            }
            changed
        };

        if changed && !in_worklist.contains(&f) {
            worklist.push_back(f);
            in_worklist.insert(f);
        }

        for field in demoted_field_slots.iter().copied() {
            if !demoted_fields.insert(field) {
                continue;
            }
            let users = global_borrow_ctxt
                .field_users
                .get(&field)
                .cloned()
                .unwrap_or_default();
            for user in users {
                if let Some(provenance_set) = global_borrow_ctxt.provenances.get_mut(&user) {
                    provenance_set.disable_owner(ProvenanceOwner::Field(field));
                }
                if !in_worklist.contains(&user) {
                    worklist.push_back(user);
                    in_worklist.insert(user);
                }
            }
        }

        demoted.get_mut(&f).unwrap().union(&demoted_locals);
    }

    DemotionResults {
        locals: demoted,
        fields: demoted_fields,
    }
}

/// Analyse which raw pointer locals within a function can potentially be a mutable references.
/// Currently there is no safety guarantee, as we need to
/// 1. study what formal guarantee can we obtain from our demoting strategy;
/// 2. implement the necessary fixpoint iteration to compute inferred bounds.
pub fn mutable_references_no_guarantee(
    program: &RustProgram,
    mutables: &FxHashMap<LocalDefId, IndexVec<Local, bool>>,
) -> BorrowPromotionResults {
    classified_references_with_fields_no_guarantee(program, mutables)
}

pub fn classified_references_with_fields_no_guarantee(
    program: &RustProgram,
    mutables: &FxHashMap<LocalDefId, IndexVec<Local, bool>>,
) -> BorrowPromotionResults {
    let mut mutable_references = FxHashMap::default();
    let mut shared_references = FxHashMap::default();
    let mut mutable_fields = FxHashSet::default();
    let mut shared_fields = FxHashSet::default();

    let mut global_borrow_ctxt = GBorrowInferCtxt::classified_pointers(program, mutables);
    // let demoted = demote_pointers(program, &global_borrow_ctxt);
    let demoted = demote_pointers_iterative_with_fields(program, &mut global_borrow_ctxt);

    for (&f, demoted) in demoted.locals.iter() {
        let provenance_set = &global_borrow_ctxt.provenances[&f];
        let mut promoted_mutable = DenseBitSet::new_empty(demoted.domain_size());
        let mut promoted_shared = DenseBitSet::new_empty(demoted.domain_size());
        for (local, local_data) in provenance_set.local_data.iter_enumerated() {
            if let Some(d) = local_data {
                let is_mutable = &provenance_set.provenance_data[*d].is_mutable();
                if *is_mutable {
                    promoted_mutable.insert(local);
                } else {
                    promoted_shared.insert(local);
                }
            }
        }
        promoted_mutable.subtract(demoted);
        promoted_shared.subtract(demoted);

        mutable_references.insert(f, promoted_mutable);
        shared_references.insert(f, promoted_shared);
    }

    for provenance_set in global_borrow_ctxt.provenances.values() {
        for (&field, &provenance) in &provenance_set.field_data {
            if demoted.fields.contains(&field) {
                continue;
            }
            let Some(provenance) = provenance else {
                continue;
            };
            if provenance_set.provenance_data[provenance].is_mutable() {
                mutable_fields.insert(field);
            } else {
                shared_fields.insert(field);
            }
        }
    }

    BorrowPromotionResults {
        mutable_locals: mutable_references,
        shared_locals: shared_references,
        mutable_fields,
        shared_fields,
        lifetime_flows: global_borrow_ctxt.lifetime_flows,
    }
}

#[cfg(test)]
mod tests;
