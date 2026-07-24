// MIRRORED glue + orchestration from production `borrow/mod.rs` @ fc3bd4cf — comment-sync only
// (NO include_str! tripwire): `invalid_loan_set`, `extract_conflict_edges`, and the two
// orchestration entry points reproduce production's logic, and their drift changes conflict edges
// on the fixture suite ⇒ it CANNOT hide from the equivalence differential (tripwires are for leaves
// whose drift can hide, e.g. places_conflict; differentials for the rest). Production names are kept
// verbatim (`borrow_conflicts`/`borrow_conflicts_replaying`/`invalid_loan_set`/
// `extract_conflict_edges`) so 3b/NB6 diffs are 1:1 — the module path is the only distinguisher.
//
// The fork's ONLY behavioral seam is `overwrite_with_engine_facts`: after the PUBLIC production
// `borrow_inference` produces all facts, this replaces its `invalidates` + `errors` with the BO
// engine's (byte-identical at 3a; 3b makes `invalidates` write-aware). Everything else is production,
// reached via its public API + the 7-field visibility manifest (see the 3a task doc).
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::borrow::{
        BorrowInferenceResults, Borrower, ConflictEdge, GBorrowInferCtxt, Loan, Provenance,
        ProvenanceOwner, ProvenanceSet, StructFieldSlot, borrow_inference,
        collect_invalid_loan_demotions,
    },
    utils::rustc::RustProgram,
};

/// BO-local L2 edge attribution. The ordinary conflict edge remains unchanged;
/// `invalidators` are access roots captured from the exact error rows that made
/// this loan invalid.
#[derive(Clone, Debug)]
pub(crate) struct WitnessedConflictEdge {
    pub(crate) edge: ConflictEdge,
    pub(crate) loan: usize,
    pub(crate) invalidators: Vec<Local>,
}

/// The 3a fork seam. Run production `borrow_inference` for every fact, then REPLACE `invalidates`
/// + `errors` with the BO engine's. At 3a the BO `invalidates` is a byte-identical copy, so the
/// replacement is a no-op on behavior (the equivalence gate). At 3b `invalidates` becomes
/// write-aware and this is where the engines diverge.
fn overwrite_with_engine_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    f: LocalDefId,
    ctxt: &GBorrowInferCtxt,
    inference: &mut BorrowInferenceResults<'tcx>,
) {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
    let provenance_set = ctxt.provenances.get(&f).unwrap();
    inference.invalidates = super::invalidates::compute_invalidates(
        tcx,
        body,
        &inference.borrow_set,
        provenance_set,
        &inference.location_map,
    );
    inference.errors = super::errors::compute_errors(
        &inference.borrow_set,
        &inference.loan_liveness,
        &inference.invalidates,
    );
}

/// L2-only fork seam. The invalidation and error matrices are computed exactly
/// as above; the returned side witnesses are write-only metadata filtered to
/// rows that survived `loan_liveness ∩ invalidates`.
fn overwrite_with_engine_facts_capturing<'tcx>(
    tcx: TyCtxt<'tcx>,
    f: LocalDefId,
    ctxt: &GBorrowInferCtxt,
    inference: &mut BorrowInferenceResults<'tcx>,
) -> Vec<super::invalidates::InvalidationAccess> {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
    let provenance_set = ctxt.provenances.get(&f).unwrap();
    let (invalidates, mut accesses) = super::invalidates::compute_invalidates_capturing(
        tcx,
        body,
        &inference.borrow_set,
        provenance_set,
        &inference.location_map,
    );
    inference.invalidates = invalidates;
    inference.errors = super::errors::compute_errors(
        &inference.borrow_set,
        &inference.loan_liveness,
        &inference.invalidates,
    );
    accesses.retain(|access| {
        inference
            .errors
            .row(access.point)
            .is_some_and(|loans| loans.contains(access.loan))
    });
    accesses
}

/// The set of invalid loans (live ∧ invalidated) across all error points.
/// (Verbatim from `borrow/mod.rs::invalid_loan_set` @ fc3bd4cf.)
fn invalid_loan_set(inference: &BorrowInferenceResults<'_>) -> DenseBitSet<Loan> {
    let mut invalid_loans = DenseBitSet::new_empty(inference.borrow_set.loans.len());
    for row in inference.errors.rows() {
        if let Some(loans) = inference.errors.row(row) {
            invalid_loans.union(loans);
        }
    }
    invalid_loans
}

/// Attribute each invalid loan to its issuer + the live provenances that required it.
/// (Verbatim from `borrow/mod.rs::extract_conflict_edges` @ fc3bd4cf.)
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

/// Attach the invalidating access roots to the unchanged one-edge-per-loan
/// aggregation. Event unioning happens only on the L2 feature-on path.
fn extract_witnessed_conflict_edges(
    inference: &BorrowInferenceResults<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
    accesses: Vec<super::invalidates::InvalidationAccess>,
) -> Vec<WitnessedConflictEdge> {
    let mut invalidators_by_loan: FxHashMap<Loan, Vec<Local>> = FxHashMap::default();
    for access in accesses {
        invalidators_by_loan
            .entry(access.loan)
            .or_default()
            .push(access.accessor);
    }

    extract_conflict_edges(inference, provenance_set, invalid_loans)
        .into_iter()
        .zip(invalid_loans.iter())
        .map(|(edge, loan)| WitnessedConflictEdge {
            edge,
            loan: loan.index(),
            invalidators: invalidators_by_loan.remove(&loan).unwrap_or_default(),
        })
        .collect()
}

/// §8 verifier (round-0). Verbatim from `borrow/mod.rs::borrow_conflicts` @ fc3bd4cf, except the
/// fork seam (`overwrite_with_engine_facts`) replaces the facts' `invalidates`/`errors` with BO's.
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
        let mut inference = borrow_inference(program.tcx, f, &ctxt);
        overwrite_with_engine_facts(program.tcx, f, &ctxt, &mut inference);
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

/// §8 BB2-i replaying verifier. Verbatim from `borrow/mod.rs::borrow_conflicts_replaying` @
/// fc3bd4cf, except: (1) the fork seam replaces `invalidates`/`errors`; (2) the private
/// `disable_owner(ProvenanceOwner::Local(local))` call — whose Local branch is exactly
/// `local_data[local] = None`, and whose return is ignored here — is inlined as that field write
/// (per the 7-field manifest, no method exposed).
pub fn borrow_conflicts_replaying<I, J, M, N, K, L>(
    program: &RustProgram,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let is_candidate = |did: LocalDefId| {
        let ref_f = is_ref(did);
        let raw_f = is_raw(did);
        move |local: Local| ref_f(local) || raw_f(local)
    };
    let mut ctxt = GBorrowInferCtxt::new(program, is_candidate, is_mutable);

    // §NB5-F2 — field candidacy: a struct-field slot the model settled `Raw` is a raw pointer, not a
    // borrow, so its loan must be disabled — the field analogue of a Raw local's `local_data=None`
    // demotion below. A field slot is `Raw` CRATE-WIDE, so disable it in EVERY function's provenance
    // set (the crate-wide hammer). `disable_owner` is a no-op where a function has no provenance for
    // that field, so passing the whole raw-field list is safe. Cleared field loans stop regenerating
    // the field conflicts that Option A (NB5-F) had to decline, so those programs now accept with the
    // field `Raw`. Genuinely un-dischargeable field residuals (never disabled here) still hit the
    // `residual_nonref_field` decline backstop in the caller — B narrows the decline set, not deletes it.
    for provenance_set in ctxt.provenances.values_mut() {
        for &field in raw_fields {
            provenance_set.disable_owner(ProvenanceOwner::Field(field));
        }
    }

    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let is_raw_f = is_raw(f);

        let edges = loop {
            let mut inference = borrow_inference(program.tcx, f, &ctxt);
            overwrite_with_engine_facts(program.tcx, f, &ctxt, &mut inference);
            let invalid_loans = invalid_loan_set(&inference);
            if invalid_loans.is_empty() {
                break Vec::new();
            }

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
                let provenance_set = ctxt.provenances.get(&f).unwrap();
                break extract_conflict_edges(&inference, provenance_set, &invalid_loans);
            }

            drop(inference);
            let provenance_set = ctxt.provenances.get_mut(&f).unwrap();
            for (local, base) in to_demote {
                // production: `provenance_set.disable_owner(ProvenanceOwner::Local(local));`
                // (Local branch = this field write; return value is ignored here).
                provenance_set.local_data[local] = None;
                provenance_set
                    .tree_borrow_local
                    .get_mut()
                    .union(local, base);
            }
        };

        // BB2-i stray-Raw inert-ness invariant (verbatim; release-active tripwire).
        let provenance_set = ctxt.provenances.get(&f).unwrap();
        assert!(
            provenance_set
                .local_data
                .iter_enumerated()
                .all(|(local, data)| {
                    if !(is_raw_f(local) && data.is_some()) {
                        return true;
                    }
                    !edges.iter().any(|e| {
                        matches!(e.issuer, Some(ProvenanceOwner::Local(l)) if l == local)
                            || e.requirers
                                .iter()
                                .any(|o| matches!(o, ProvenanceOwner::Local(l) if *l == local))
                    })
                }),
            "BB2-i stray-Raw (fork engine): a non-witness Raw local appears in a residual edge in \
             {f:?} — the inert-ness invariant (stray Raw ⟹ in no residual edge) is violated"
        );

        if !edges.is_empty() {
            out.insert(f, edges);
        }
    }
    out
}

/// L2 witnessed replay. This is a feature-on sibling of
/// `borrow_conflicts_replaying`: the plain function and all of its consumers
/// retain their original output shape and perform no capture allocation.
pub(crate) fn borrow_conflicts_replaying_witnessed<I, J, M, N, K, L>(
    program: &RustProgram,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
) -> FxHashMap<LocalDefId, Vec<WitnessedConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let is_candidate = |did: LocalDefId| {
        let ref_f = is_ref(did);
        let raw_f = is_raw(did);
        move |local: Local| ref_f(local) || raw_f(local)
    };
    let mut ctxt = GBorrowInferCtxt::new(program, is_candidate, is_mutable);

    for provenance_set in ctxt.provenances.values_mut() {
        for &field in raw_fields {
            provenance_set.disable_owner(ProvenanceOwner::Field(field));
        }
    }

    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let is_raw_f = is_raw(f);

        let edges = loop {
            let mut inference = borrow_inference(program.tcx, f, &ctxt);
            let accesses =
                overwrite_with_engine_facts_capturing(program.tcx, f, &ctxt, &mut inference);
            let invalid_loans = invalid_loan_set(&inference);
            if invalid_loans.is_empty() {
                break Vec::new();
            }

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
                let provenance_set = ctxt.provenances.get(&f).unwrap();
                break extract_witnessed_conflict_edges(
                    &inference,
                    provenance_set,
                    &invalid_loans,
                    accesses,
                );
            }

            drop(inference);
            let provenance_set = ctxt.provenances.get_mut(&f).unwrap();
            for (local, base) in to_demote {
                provenance_set.local_data[local] = None;
                provenance_set
                    .tree_borrow_local
                    .get_mut()
                    .union(local, base);
            }
        };

        let provenance_set = ctxt.provenances.get(&f).unwrap();
        assert!(
            provenance_set
                .local_data
                .iter_enumerated()
                .all(|(local, data)| {
                    if !(is_raw_f(local) && data.is_some()) {
                        return true;
                    }
                    !edges.iter().any(|witnessed| {
                        let edge = &witnessed.edge;
                        matches!(edge.issuer, Some(ProvenanceOwner::Local(l)) if l == local)
                            || edge
                                .requirers
                                .iter()
                                .any(|o| matches!(o, ProvenanceOwner::Local(l) if *l == local))
                    })
                }),
            "BB2-i stray-Raw (fork engine): a non-witness Raw local appears in a residual edge in \
             {f:?} — the inert-ness invariant (stray Raw ⟹ in no residual edge) is violated"
        );

        if !edges.is_empty() {
            out.insert(f, edges);
        }
    }
    out
}
