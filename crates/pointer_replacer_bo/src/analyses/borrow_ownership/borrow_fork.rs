//! The BO-owned part of the production borrow analysis (the master-merge cleanup's legacy-copy
//! stage, the user's word in main's session 11-02). Everything else -- the types, the fact
//! computations, `GBorrowInferCtxt`, `demote_pointers_iterative_with_fields` -- is the legacy
//! crate's `analyses::borrow`, read unchanged. BO owns only:
//! - [`borrow_set`], the loan builder, which differs from the legacy one by one rule: a C-variadic
//!   callee has no parameter local past its fixed inputs, so no loan is bound there (tisp's
//!   `mk_list`, RQ3 / analysis-fanout 018). The legacy builder lacks it; master's code is not
//!   changed here (D12), and the PR text names the difference.
//! - [`borrow_inference`], the legacy driver with that builder.
//! - the conflict-edge verifiers BO added ([`borrow_conflicts`], [`borrow_conflicts_replaying`],
//!   [`collect_invalid_loan_demotions`]) and [`LoanLocation`].

use rustc_hash::FxHashMap;
#[cfg(test)]
use rustc_hash::FxHashSet;
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{
        Body, HasLocalDecls, Local, Location, Operand, Place, PlaceElem, Rvalue, Terminator,
        visit::Visitor,
    },
    ty::TyCtxt,
};
use rustc_mir_dataflow::points::DenseLocationMap;
use rustc_span::def_id::LocalDefId;

use crate::analyses::{
    borrow::{
        BorrowData, BorrowInferenceResults, BorrowSet, Borrower, GBorrowInferCtxt, Loan,
        ProvenanceConstraintGraph, ProvenanceOwner, ProvenanceSet, errors::compute_errors,
        invalidates::compute_invalidates, is_borrowing_method, killed::compute_killed,
        loan_liveness::compute_loan_liveness, provenance_liveness::compute_provenance_liveness,
        requires::compute_requires, subset_closure::compute_subset_closure,
    },
    mir::{CallKind, TerminatorExt},
};
#[cfg(test)]
use crate::{analyses::borrow::Provenance, utils::rustc::RustProgram};

/// A loan's location (the legacy `BorrowData` keeps the field without an accessor).
pub(crate) trait LoanLocation {
    fn location(&self) -> Location;
}

impl LoanLocation for BorrowData<'_> {
    fn location(&self) -> Location {
        self.location
    }
}

/// The loan set of one body: the legacy `HasBorrowSet` builder with the C-variadic rule.
pub(crate) fn borrow_set<'tcx, 'local, 'global: 'local>(
    body: &Body<'tcx>,
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
        fn visit_assign(&mut self, lhs: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
            let Some(assigned_owner) = self.provenance_set.owner_for_place(self.local_decl, *lhs)
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
                // A C-variadic callee has no parameter local past its fixed
                // inputs: `_(i+1)` there is a body local (tisp's `mk_list`,
                // RQ3 / analysis-fanout 018), so no loan is bound to it.
                let fixed = self
                    .tcx
                    .fn_sig(callee)
                    .skip_binder()
                    .inputs()
                    .skip_binder()
                    .len();
                for (arg_index, arg) in mir_call.args.iter().enumerate().take(fixed) {
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
        local_decl: body,
        tcx,
        provenance_set,
        global_borrow_ctxt,
    };
    vis.visit_body(body);

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

/// The legacy `borrow_inference`, with [`borrow_set`] for the loan set.
pub(crate) fn borrow_inference<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    global_borrow_ctxt: &GBorrowInferCtxt,
) -> BorrowInferenceResults<'tcx> {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();

    let provenance_set = global_borrow_ctxt.provenances.get(&def_id).unwrap();
    let borrow_set = borrow_set(body, tcx, provenance_set, global_borrow_ctxt);
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
    /// BO-only repair-class marker. Ordinary borrow conflicts keep this false; an exact
    /// ESC-GAP ② selected loan sets it so the unified repair loop can use that class's issuer
    /// kill switch without changing A-prime selection for any ordinary row.
    pub(crate) esc_issuer_first: bool,
}

/// §8 verifier (read-only): run `borrow_inference` with a given ref-candidacy +
/// mutability and return, per function, the conflict edges (invalid loans attributed
/// to their issuer/requirer owners). Mirrors the error-extraction of
/// `demote_pointers_iterative_with_fields` WITHOUT mutating the `ProvenanceSet` — so
/// it is faithful for a Round-0 (all-candidate) set; a *partial* candidacy that
/// represents demotions would also need the `tree_borrow_local` union replay the
/// demotion loop performs (the caller's concern).
#[cfg(test)]
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
#[cfg(test)]
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
#[cfg(test)]
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
        edges.push(ConflictEdge {
            issuer,
            requirers,
            esc_issuer_first: false,
        });
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
#[cfg(test)]
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
                provenance_set
                    .tree_borrow_local
                    .get_mut()
                    .union(local, base);
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

/// The demotions an invalid-loan set induces, collected WITHOUT mutating the
/// `ProvenanceSet`. Each `(local, base)` in `local_witnesses` means "demoting
/// `local` unions it with `base`" — `base` is the invalid loan's `borrowed.local`,
/// exactly as `demote_pointers_iterative_with_fields` does. `Field` owners carry no
/// union and are not collected: the §8 CEGAR validate replay, this collection's one
/// consumer here, gates the local witnesses on the model's `Raw` slots. (The legacy demote
/// loop keeps its own copy of these paths.)
pub(crate) struct InvalidLoanDemotions {
    pub local_witnesses: Vec<(Local, Local)>,
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
                    ProvenanceOwner::Field(_) => {}
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
                ProvenanceOwner::Field(_) => {}
            }
        }
    }

    InvalidLoanDemotions { local_witnesses }
}

#[allow(dead_code)]
#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::mir::VarDebugInfoContents;

    use super::*;

    fn build_rust_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = vec![];
        let mut structs = vec![];
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    /// Map a source-level variable name to its MIR `Local` (via debug info).
    fn local_by_name(tcx: TyCtxt<'_>, did: LocalDefId, name: &str) -> Local {
        let body = &*tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        for vdi in body.var_debug_info.iter() {
            if vdi.name.as_str() == name
                && let VarDebugInfoContents::Place(place) = &vdi.value
                && let Some(local) = place.as_local()
            {
                return local;
            }
        }
        panic!("no local named `{name}` in {did:?}");
    }

    fn edge_involves(edge: &ConflictEdge, local: Local) -> bool {
        let target = ProvenanceOwner::Local(local);
        edge.issuer == Some(target) || edge.requirers.contains(&target)
    }

    /// BB2-i (§8 CEGAR validate, union-replay): given a partial candidacy that marks `x`
    /// `Raw` (production's iteration-1 demotion — `probe` confirmed `iter1={x}`,
    /// `final={x,y}`), the verifier must replay the `tree_borrow_local` union and surface
    /// the resulting `y` conflict — the model-dependent conflict the union creates. Plain
    /// BB0 `borrow_conflicts` (no union) does NOT see it, because `y = &mut local` alone
    /// is sound. This is the differential that proves the replay does real work.
    #[test]
    fn bb2i_replay_surfaces_union_induced_conflict() {
        ::utils::compilation::run_compiler_on_str(
            "
            unsafe fn f() {
                let mut local = 0i32;
                let x = &mut local as *mut _;
                let y = &mut local as *mut _;
                *x = 1;
                *y = 2;
            }
            ",
            |tcx| {
                let program = build_rust_program(tcx);
                let f = program.functions[0];
                let x = local_by_name(tcx, f, "x");
                let y = local_by_name(tcx, f, "y");

                let is_mutable = |_: LocalDefId| |_: Local| true;
                // Candidacy: `x` is Raw (demoted, induces a union); everything else Ref.
                let is_ref = move |did: LocalDefId| move |local: Local| !(did == f && local == x);
                let is_raw = move |did: LocalDefId| move |local: Local| did == f && local == x;

                // BB0 (no union replay): `x` is simply a non-candidate, so `y = &mut local`
                // alone is sound — round-0 finds NO conflict at all for `f`. Asserting
                // emptiness (not merely "no y") pins the union as the *sole* cause.
                let bb0 = borrow_conflicts(&program, is_ref, is_mutable);
                assert!(
                    bb0.get(&f).is_none_or(|edges| edges.is_empty()),
                    "BB0 (no union) must find NO conflict for `f`; got {bb0:?}"
                );

                // BB2-i replay: demote `x` + union(x, local) ⇒ `y = &mut local` now conflicts.
                let replay = borrow_conflicts_replaying(&program, is_ref, is_raw, is_mutable);
                let replay_involves_y = replay
                    .get(&f)
                    .is_some_and(|edges| edges.iter().any(|e| edge_involves(e, y)));
                assert!(
                    replay_involves_y,
                    "BB2-i replay must surface the union-induced `y` conflict; got {replay:?}"
                );
            },
        )
        .unwrap();
    }
}
