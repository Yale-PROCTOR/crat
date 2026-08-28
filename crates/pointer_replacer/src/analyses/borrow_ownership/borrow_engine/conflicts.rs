// MIRRORED glue + orchestration from production `borrow/mod.rs` @ fc3bd4cf — comment-sync only
// (NO include_str! tripwire): `invalid_loan_set`, `extract_conflict_edges`, and the two
// orchestration entry points reproduce production's logic, and their drift changes conflict edges
// on the fixture suite ⇒ it CANNOT hide from the equivalence differential (tripwires are for leaves
// whose drift can hide, e.g. places_conflict; differentials for the rest). Production names are kept
// verbatim (`borrow_conflicts`/`borrow_conflicts_replaying`/`invalid_loan_set`/
// `extract_conflict_edges`) so 3b/NB6 diffs are 1:1 — the module path is the only distinguisher.
//
// NB5-O adds the BO-owned origin-replay seam: production `borrow_inference` still supplies the
// frozen base facts, then `NativeBorrowContext` replaces subset/requires/loan-liveness from retained
// BO-native body flows before this module replaces invalidates/errors with the BO engine's.
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;

use super::{
    a5_places_conflict::ParameterOverlap,
    origin_replay::{NativeBorrowContext, NativeInference},
};
use crate::{
    analyses::{
        borrow::{
            BorrowInferenceResults, Borrower, ConflictEdge, GBorrowInferCtxt, Loan, Provenance,
            ProvenanceOwner, ProvenanceSet, StructFieldSlot, collect_invalid_loan_demotions,
        },
        borrow_ownership::{
            coherence::SelectedCopyLendLoans,
            export::{self, LoanClass},
            origin_flow::OriginFlowResults,
        },
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
    pub(crate) loan_location: crate::analyses::borrow_ownership::l2::MirLocationKey,
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
    copy_lends: &DenseBitSet<Loan>,
    parameter_overlap: Option<&ParameterOverlap>,
) -> Vec<(Local, Local)> {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
    let provenance_set = ctxt.provenances.get(&f).unwrap();
    let (invalidates, parameter_conflicts) = match parameter_overlap {
        Some(parameter_overlap) => {
            super::invalidates::compute_invalidates_with_copy_lends_and_parameter_overlap(
                tcx,
                body,
                &inference.borrow_set,
                provenance_set,
                &inference.location_map,
                copy_lends,
                parameter_overlap,
            )
        }
        None => (
            super::invalidates::compute_invalidates_with_copy_lends(
                tcx,
                body,
                &inference.borrow_set,
                provenance_set,
                &inference.location_map,
                copy_lends,
            ),
            Vec::new(),
        ),
    };
    inference.invalidates = invalidates;
    inference.errors = super::errors::compute_errors(
        &inference.borrow_set,
        &inference.loan_liveness,
        &inference.invalidates,
    );
    parameter_conflicts
}

/// L2-only fork seam. The invalidation and error matrices are computed exactly
/// as above; the returned side witnesses are write-only metadata filtered to
/// rows that survived `loan_liveness ∩ invalidates`.
fn overwrite_with_engine_facts_capturing<'tcx>(
    tcx: TyCtxt<'tcx>,
    f: LocalDefId,
    ctxt: &GBorrowInferCtxt,
    inference: &mut BorrowInferenceResults<'tcx>,
    copy_lends: &DenseBitSet<Loan>,
) -> Vec<super::invalidates::InvalidationAccess> {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
    let provenance_set = ctxt.provenances.get(&f).unwrap();
    let (invalidates, mut accesses) =
        super::invalidates::compute_invalidates_capturing_with_copy_lends(
            tcx,
            body,
            &inference.borrow_set,
            provenance_set,
            &inference.location_map,
            copy_lends,
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

/// E-R4 capture: record loan-level identity for the COMPLETE final `BorrowSet`.
///
/// Deliberately NOT folded into `extract_conflict_edges`: that function is a
/// verbatim mirror of `borrow/mod.rs` and must stay so, and
/// `extract_witnessed_conflict_edges` zips its output against
/// `invalid_loans.iter()` — any reordering or filtering there would silently
/// mis-associate loans.
///
/// It is also called BEFORE the callers' `invalid_loans.is_empty()` early exit,
/// because a conflict-free function is precisely the case where every loan
/// SURVIVED and a re-route has something to match against.
///
/// The kind derivation is textually the engine's own expression (`invalidates.rs`,
/// both `is_mutable` sites) applied to the loan record, keyed on the BASE local
/// with projections ignored (R-Q1a §0.4).
fn record_loan_identities(
    fn_did: LocalDefId,
    inference: &BorrowInferenceResults<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
    copy_lends: &DenseBitSet<Loan>,
) {
    use crate::analyses::borrow_ownership::export;
    if !export::capturing() {
        return;
    }
    for (loan, data) in inference.borrow_set.loans.iter_enumerated() {
        let mutable = provenance_set.local_data[data.borrowed.local]
            .map(|p| provenance_set.provenance_data[p].is_mutable());
        // D5 payloads restored: both are key components now (§1.1 correction 2).
        let borrower = match data.assigned {
            Borrower::Assign(owner) => export::BorrowerKind::Assign {
                owner: export::OwnerKey::from_owner(owner),
            },
            Borrower::CallArg(callee, arg_index) => export::BorrowerKind::CallArg {
                callee: callee.local_def_index.as_u32(),
                arg_index,
            },
        };
        export::record_loan(export::LoanIdentity {
            key: export::LoanKey {
                fn_did,
                place: export::PlaceKey::from_place(data.borrowed),
                location: export::location_key(data.location()),
                borrower,
            },
            run_local_handle: loan.index(),
            kind: export::LoanKind::from_provenance_mutability(mutable),
            class: if copy_lends.contains(loan) {
                LoanClass::CopyLend
            } else {
                LoanClass::Existing
            },
            invalid: invalid_loans.contains(loan),
        });
    }
}

/// Attribute each invalid loan to its issuer + the live provenances that required it.
/// (Verbatim from `borrow/mod.rs::extract_conflict_edges` @ fc3bd4cf.)
fn extract_conflict_edges(
    inference: &NativeInference<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
) -> Vec<ConflictEdge> {
    let BorrowInferenceResults {
        borrow_set,
        provenance_liveness,
        requires,
        errors,
        ..
    } = &inference.facts;

    let mut edges = Vec::new();
    for loan in invalid_loans.iter() {
        let borrow_data = &borrow_set.loans[loan];
        let mut issuer = match borrow_data.assigned {
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
                // §HLZ-PORT: `row` is the error POINT and is already in scope — the same shape
                // the colleague's own edit has. `Off` keeps the whole-body predicate verbatim.
                let required = match &inference.localized_requires {
                    Some(localized) => localized.contains(row, provenance, loan),
                    None => requires.contains(provenance, loan),
                };
                // §6.4 drop attribution: a requirer the WHOLE-BODY relation keeps at a live,
                // erroring point and the point-keyed one drops. `all_only` says whether it is
                // reachable using `All` edges alone — those apply at every point, so `all_only =
                // false` attributes the drop to a LOCATED reborrow edge rather than to any
                // approximation A2 introduces.
                if let Some(closure) = &inference.all_only_closure
                    && !required
                    && requires.contains(provenance, loan)
                {
                    let all_only = closure
                        .get(&loan)
                        .is_some_and(|set| set.contains(provenance));
                    // Was the requirer even live where the loan was reserved? If not, its
                    // liveness at the error point comes from a LATER definition, so the value it
                    // holds there cannot be the borrow reserved earlier — which is what makes the
                    // drop a true point-sensitive unreachability rather than a lost path.
                    let reserve_point = inference
                        .facts
                        .location_map
                        .point_from_location(borrow_set.loans[loan].location());
                    let live_at_reserve = inference
                        .facts
                        .provenance_liveness
                        .row(reserve_point)
                        .is_some_and(|live| live.contains(provenance));
                    let verdict = census_drop(inference, loan, provenance, row, live_at_reserve);
                    crate::analyses::borrow_ownership::borrow_engine::record_requirer_drop(
                        format!(
                            "loan={} point={row:?} provenance={provenance:?} owner={:?} \
                             all_only_reachable={all_only} live_at_reserve={live_at_reserve} \
                             {verdict}",
                            loan.index(),
                            provenance_set.provenance_data[provenance].owner(),
                        ),
                    );
                }
                // Instrument control: run the SAME census over requirers the port KEEPS. A census
                // that can only ever answer "unreachable" would make "0 counterexamples" vacuous;
                // these rows demonstrate the reachability arm firing on the same code path.
                if let Some(_closure) = &inference.all_only_closure
                    && required
                    && requires.contains(provenance, loan)
                {
                    let reserve_point = inference
                        .facts
                        .location_map
                        .point_from_location(borrow_set.loans[loan].location());
                    let live_at_reserve = inference
                        .facts
                        .provenance_liveness
                        .row(reserve_point)
                        .is_some_and(|live| live.contains(provenance));
                    let verdict = census_drop(inference, loan, provenance, row, live_at_reserve);
                    crate::analyses::borrow_ownership::borrow_engine::record_requirer_drop(
                        format!(
                            "control=kept loan={} point={row:?} provenance={provenance:?} \
                             live_at_reserve={live_at_reserve} {verdict}",
                            loan.index(),
                        ),
                    );
                }
                if required && seen.insert(provenance) {
                    requirers.push(provenance_set.provenance_data[provenance].owner());
                }
            }
        }
        let esc_issuer_first = if let Some(&(resolved_source, resolved_destination)) =
            inference.escaped_presentations.get(&loan)
        {
            issuer = Some(resolved_source);
            requirers.clear();
            requirers.push(resolved_destination);
            true
        } else {
            false
        };
        edges.push(ConflictEdge {
            issuer,
            requirers,
            esc_issuer_first,
        });
    }
    edges
}

/// §8.1 census — per-drop proof obligation, re-derived INDEPENDENTLY of the walk.
///
/// For a requirer `q` the whole-body relation keeps at a live erroring point `e` and the
/// point-keyed relation drops, this recomputes the liveness-gated propagation of `q` from the
/// loan's reservation point using only the raw CFG, `provenance_liveness` and `killed` — none of
/// the walk's own state. If `e` is reachable under that gate the drop is a **COUNTEREXAMPLE** and
/// the realized path is printed; otherwise the drop is **PROVEN-TRUE-UNREACHABLE** and the gap is
/// located.
///
/// The gap is necessarily EPOCH-SEPARATING and that follows from backward liveness rather than
/// from a second check: `q` is dead on exit at the gap point `p` but live at `e`, and `e` is
/// CFG-reachable from `p`; a backward may-liveness that reports `q` dead at `p` asserts that every
/// path out of `p` redefines `q` before any use, so the use that makes `q` live at `e` is fed by a
/// definition strictly after `p`. The value `q` holds at `e` therefore cannot be the borrow
/// reserved before `p`.
fn census_drop(
    inference: &NativeInference<'_>,
    loan: Loan,
    q: Provenance,
    e: rustc_mir_dataflow::points::PointIndex,
    live_at_reserve: bool,
) -> String {
    use rustc_mir_dataflow::points::PointIndex;
    let (Some(succ), Some(reserve_of)) = (&inference.succ_points, &inference.loan_reserve) else {
        return "verdict=NO-CENSUS".to_string();
    };
    if !live_at_reserve {
        // Not live where the loan was reserved: the walk never seeds it, and its liveness at the
        // error point is fed by a later definition. Nothing to trace.
        return "verdict=PROVEN-TRUE-UNREACHABLE gap=seed reason=not-live-at-reserve".to_string();
    }
    let reserve = reserve_of[&loan];
    let live = |p: PointIndex| {
        inference
            .facts
            .provenance_liveness
            .row(p)
            .is_some_and(|r| r.contains(q))
    };
    let killed = |p: PointIndex| inference.facts.killed[p].contains(loan);

    // Gated forward closure, with parent links so a counterexample can print its path.
    let mut parent: FxHashMap<PointIndex, PointIndex> = FxHashMap::default();
    let mut seen: FxHashSet<PointIndex> = FxHashSet::default();
    let mut work: Vec<PointIndex> = Vec::new();
    if live(reserve) {
        for &s in succ.get(&reserve).map(|v| &v[..]).unwrap_or(&[]) {
            if seen.insert(s) {
                parent.insert(s, reserve);
                work.push(s);
            }
        }
    }
    while let Some(p) = work.pop() {
        if killed(p) || !live(p) {
            continue;
        }
        for &s in succ.get(&p).map(|v| &v[..]).unwrap_or(&[]) {
            if seen.insert(s) {
                parent.insert(s, p);
                work.push(s);
            }
        }
    }
    if seen.contains(&e) {
        let mut path = vec![e];
        let mut cur = e;
        while let Some(&pp) = parent.get(&cur) {
            path.push(pp);
            cur = pp;
            if path.len() > 64 {
                break;
            }
        }
        path.reverse();
        return format!(
            "verdict=COUNTEREXAMPLE realized_path={:?}",
            path.iter().map(|p| p.index()).collect::<Vec<_>>()
        );
    }

    // Locate the gap: a point the gate REACHED whose raw successor set leads on toward `e`, and at
    // which the gate then failed. Restrict to points that can still reach `e` in the raw CFG.
    let mut reaches_e: FxHashSet<PointIndex> = FxHashSet::default();
    reaches_e.insert(e);
    let mut changed = true;
    while changed {
        changed = false;
        for (&p, outs) in succ.iter() {
            if !reaches_e.contains(&p) && outs.iter().any(|s| reaches_e.contains(s)) {
                reaches_e.insert(p);
                changed = true;
            }
        }
    }
    let mut gap = None;
    for &p in seen.iter().chain(std::iter::once(&reserve)) {
        if reaches_e.contains(&p) && (killed(p) || !live(p)) {
            let reason = if killed(p) { "killed" } else { "dead-on-exit" };
            match gap {
                Some((g, _)) if p.index() >= g => {}
                _ => gap = Some((p.index(), reason)),
            }
        }
    }
    match gap {
        Some((p, reason)) => format!(
            "verdict=PROVEN-TRUE-UNREACHABLE gap_point={p} gap_reason={reason} \
             epoch_separating=by-backward-liveness"
        ),
        // No gated-reached point on a path to `e` at all: the propagation never entered `e`'s
        // dominating region, which is a stronger form of the same conclusion.
        None => "verdict=PROVEN-TRUE-UNREACHABLE gap=no-gated-point-reaches-error".to_string(),
    }
}

/// §HLZ-PORT — the demotion-witness half of the SAME predicate.
///
/// Production `collect_invalid_loan_demotions` (`borrow/mod.rs:1246`) and
/// `extract_conflict_edges` above test `requires` over the same `(error row, live provenance)`
/// pairs. Between them sits the release-active BB2-i stray-Raw assertion: a non-witness Raw local
/// must appear in no residual edge. Point-keying ONE of the two would let a local be dropped from
/// the witness set while surviving as a requirer (or the reverse) and fire it. So the fork carries
/// its own copy, and under `Off` it delegates to production verbatim rather than duplicating it.
fn collect_invalid_loan_demotions_forked(
    inference: &NativeInference<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
) -> Vec<(Local, Local)> {
    let Some(localized) = &inference.localized_requires else {
        return collect_invalid_loan_demotions(&inference.facts, provenance_set, invalid_loans)
            .local_witnesses;
    };

    let mut local_witnesses = Vec::new();
    for loan in invalid_loans.iter() {
        local_witnesses.extend(local_witnesses_for_loan(
            inference,
            provenance_set,
            localized,
            loan,
        ));
    }

    local_witnesses
}

fn local_witnesses_for_loan(
    inference: &NativeInference<'_>,
    provenance_set: &ProvenanceSet,
    localized: &super::loan_liveness::LocalizedRequires,
    loan: Loan,
) -> Vec<(Local, Local)> {
    let BorrowInferenceResults {
        borrow_set,
        errors,
        provenance_liveness,
        ..
    } = &inference.facts;
    let borrow_data = &borrow_set.loans[loan];
    let mut local_witnesses = Vec::new();

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
            if !localized.contains(row, provenance, loan) {
                continue;
            }
            if let ProvenanceOwner::Local(local) =
                provenance_set.provenance_data[provenance].owner()
            {
                local_witnesses.push((local, borrow_data.borrowed.local));
            }
        }
    }

    if let Borrower::Assign(ProvenanceOwner::Local(local)) = borrow_data.assigned {
        local_witnesses.push((local, borrow_data.borrowed.local));
    }
    local_witnesses
}

fn escaped_demotion_exemptions(
    inference: &NativeInference<'_>,
    provenance_set: &ProvenanceSet,
    invalid_loans: &DenseBitSet<Loan>,
) -> FxHashSet<(Local, Local)> {
    let Some(localized) = &inference.localized_requires else {
        assert!(
            inference.escaped_lends.is_empty(),
            "escaped CopyLends require localized replay"
        );
        return FxHashSet::default();
    };
    let mut selected = FxHashSet::default();
    let mut ordinary = FxHashSet::default();
    for loan in invalid_loans.iter() {
        let target = if inference.escaped_lends.contains(loan) {
            &mut selected
        } else {
            &mut ordinary
        };
        for pair in local_witnesses_for_loan(inference, provenance_set, localized, loan) {
            target.insert(pair);
        }
    }
    selected.retain(|pair| !ordinary.contains(pair));
    selected
}

/// Addendum 61 convergence tripwire. A marked row may exist only while its presented source is
/// still `Ref`; after issuer-first repair demotes that source, the active-loan filter must remove
/// the selected loan before the next replay. This check precedes the generic stray-Raw invariant
/// so persistence is reported as the class-specific STOP rather than looking like an ordinary
/// replay failure.
fn assert_escaped_conflicts_pre_demotion<'a>(
    edges: impl Iterator<Item = &'a ConflictEdge>,
    is_ref: impl Fn(Local) -> bool,
    registered: usize,
) {
    let mut marked = 0;
    for edge in edges.filter(|edge| edge.esc_issuer_first) {
        marked += 1;
        match edge.issuer {
            Some(ProvenanceOwner::Local(source)) => assert!(
                is_ref(source),
                "②-selected loan conflict persisted after its resolved source was demoted"
            ),
            Some(ProvenanceOwner::Field(_)) => {
                // Field slots are held out of the ②-minimal wave. Keep this explicit so a future
                // field-bearing allowlist row cannot silently bypass the Local convergence check.
                panic!("②-minimal selected source unexpectedly resolved to a field")
            }
            None => panic!("②-selected conflict presentation lost its resolved-source issuer"),
        }
    }
    assert!(
        marked <= registered && marked <= 36,
        "② conflict presentation count exceeded its matched allowlist class"
    );
}

/// Attach the invalidating access roots to the unchanged one-edge-per-loan
/// aggregation. Event unioning happens only on the L2 feature-on path.
fn extract_witnessed_conflict_edges(
    inference: &NativeInference<'_>,
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
        .map(|(edge, loan)| {
            let location = inference.facts.borrow_set.loans[loan].location();
            WitnessedConflictEdge {
                edge,
                loan: loan.index(),
                loan_location: crate::analyses::borrow_ownership::l2::MirLocationKey::new(
                    location.block.index() as u32,
                    location.statement_index,
                ),
                invalidators: invalidators_by_loan.remove(&loan).unwrap_or_default(),
            }
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
    let flows =
        crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(program);
    borrow_conflicts_with_flows(program, &flows, is_candidate, is_mutable)
}

pub(crate) fn borrow_conflicts_with_flows<I, J, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_candidate: I,
    is_mutable: K,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let ctxt = NativeBorrowContext::new(program, flows, is_candidate, is_mutable);
    let no_copy_lends = FxHashSet::default();
    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let mut inference = ctxt.infer(program.tcx, f, &[], &no_copy_lends, &no_copy_lends);
        overwrite_with_engine_facts(
            program.tcx,
            f,
            &ctxt.borrow,
            &mut inference.facts,
            &inference.copy_lends,
            None,
        );
        let invalid_loans = invalid_loan_set(&inference);
        if invalid_loans.is_empty() {
            continue;
        }
        let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
        out.insert(
            f,
            extract_conflict_edges(&inference, provenance_set, &invalid_loans),
        );
    }
    out
}

/// §HLZ-PORT witness instrument (test-only). Per function, one row per loan:
/// `(loan index, is the borrower a `CallArg`, number of points at which the loan is live)`.
///
/// Exists because the port's `CallArg` claim (§2.4(a) of the port-exploration record) is about
/// `loan_liveness`, which no public entry point exposes — the conflict-edge surface reports the
/// ABSENCE of an edge in both modes and so cannot distinguish "never live" from "live but inert".
/// Reads the facts BEFORE `overwrite_with_engine_facts`, so it observes the loan-liveness stage
/// alone with no invalidation coupling.
#[cfg(test)]
pub(crate) fn loan_liveness_census<I, J, K, L>(
    program: &RustProgram,
    is_candidate: I,
    is_mutable: K,
) -> FxHashMap<LocalDefId, Vec<(usize, bool, usize)>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let flows =
        crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(program);
    let ctxt = NativeBorrowContext::new(program, &flows, is_candidate, is_mutable);
    let no_copy_lends = FxHashSet::default();
    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let inference = ctxt.infer(program.tcx, f, &[], &no_copy_lends, &no_copy_lends);
        let mut rows = Vec::new();
        for (loan, data) in inference.borrow_set.loans.iter_enumerated() {
            let live_points = inference
                .loan_liveness
                .rows()
                .filter(|&row| {
                    inference
                        .loan_liveness
                        .row(row)
                        .is_some_and(|loans| loans.contains(loan))
                })
                .count();
            rows.push((
                loan.index(),
                matches!(data.assigned, Borrower::CallArg(..)),
                live_points,
            ));
        }
        out.insert(f, rows);
    }
    out
}

/// §HLZ-PORT witness instrument (test-only) — the DEMOTION side, observed on its own.
///
/// The adversarial review's point (2026-08-25, §39 addendum 15): asserting that conflict edges
/// and demotion witnesses agree only proves they are mutually consistent, and the same
/// incomplete predicate applied to both can delete a required invalidation on both sides while
/// keeping BB2-i silent. So the two are witnessed SEPARATELY — this returns the demotion
/// witnesses directly, with no reference to the edge set.
#[cfg(test)]
pub(crate) fn demotion_witness_census<I, J, K, L>(
    program: &RustProgram,
    is_candidate: I,
    is_mutable: K,
) -> FxHashMap<LocalDefId, Vec<(usize, usize)>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let flows =
        crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(program);
    let ctxt = NativeBorrowContext::new(program, &flows, is_candidate, is_mutable);
    let no_copy_lends = FxHashSet::default();
    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let mut inference = ctxt.infer(program.tcx, f, &[], &no_copy_lends, &no_copy_lends);
        overwrite_with_engine_facts(
            program.tcx,
            f,
            &ctxt.borrow,
            &mut inference.facts,
            &inference.copy_lends,
            None,
        );
        let invalid_loans = invalid_loan_set(&inference);
        let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
        let mut witnesses: Vec<(usize, usize)> =
            collect_invalid_loan_demotions_forked(&inference, provenance_set, &invalid_loans)
                .into_iter()
                .map(|(local, base)| (local.index(), base.index()))
                .collect();
        witnesses.sort();
        witnesses.dedup();
        out.insert(f, witnesses);
    }
    out
}

#[cfg(test)]
fn borrow_conflicts_wrapped<I, J, K, L>(
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
    use crate::analyses::borrow::borrow_inference;

    let ctxt = GBorrowInferCtxt::new(program, is_candidate, is_mutable);
    let mut out = FxHashMap::default();
    for f in program.functions.iter().copied() {
        let mut inference = borrow_inference(program.tcx, f, &ctxt);
        let copy_lends = DenseBitSet::new_empty(inference.borrow_set.loans.len());
        let escaped_lends = DenseBitSet::new_empty(inference.borrow_set.loans.len());
        overwrite_with_engine_facts(program.tcx, f, &ctxt, &mut inference, &copy_lends, None);
        let invalid_loans = invalid_loan_set(&inference);
        if invalid_loans.is_empty() {
            continue;
        }
        let provenance_set = ctxt.provenances.get(&f).unwrap();
        // §HLZ-PORT: this test-only path runs production `borrow_inference` directly and never
        // goes through `NativeBorrowContext::infer`, so it has no localized relation by
        // construction — `None` keeps it on the whole-body predicate, which is what it compares.
        let inference = NativeInference {
            facts: inference,
            copy_lends,
            escaped_lends,
            escaped_presentations: FxHashMap::default(),
            localized_requires: None,
            all_only_closure: None,
            succ_points: None,
            loan_reserve: None,
        };
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
    let flows =
        crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(program);
    borrow_conflicts_replaying_with_flows(program, &flows, is_ref, is_raw, is_mutable, raw_fields)
}

pub(crate) fn borrow_conflicts_replaying_with_flows<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
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
    let selected = SelectedCopyLendLoans::default();
    borrow_conflicts_replaying_with_flows_and_copy_lends(
        program, flows, is_ref, is_raw, is_mutable, raw_fields, &selected,
    )
}

pub(crate) fn borrow_conflicts_replaying_with_flows_and_copy_lends<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let escaped = SelectedCopyLendLoans::default();
    borrow_conflicts_replaying_with_flows_impl(
        program,
        flows,
        is_ref,
        is_raw,
        is_mutable,
        raw_fields,
        selected_copy_lends,
        &escaped,
        None,
    )
}

pub(crate) fn borrow_conflicts_replaying_with_flows_and_copy_lends_and_escaped<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
    escaped_copy_lends: &SelectedCopyLendLoans,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    borrow_conflicts_replaying_with_flows_impl(
        program,
        flows,
        is_ref,
        is_raw,
        is_mutable,
        raw_fields,
        selected_copy_lends,
        escaped_copy_lends,
        None,
    )
}

pub(crate) fn borrow_conflicts_replaying_with_flows_and_parameter_overlap<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
    parameter_overlaps: &FxHashMap<LocalDefId, ParameterOverlap>,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let escaped = SelectedCopyLendLoans::default();
    borrow_conflicts_replaying_with_flows_impl(
        program,
        flows,
        is_ref,
        is_raw,
        is_mutable,
        raw_fields,
        selected_copy_lends,
        &escaped,
        Some(parameter_overlaps),
    )
}

pub(crate) fn borrow_conflicts_replaying_with_flows_and_parameter_overlap_and_escaped<
    I,
    J,
    M,
    N,
    K,
    L,
>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
    escaped_copy_lends: &SelectedCopyLendLoans,
    parameter_overlaps: &FxHashMap<LocalDefId, ParameterOverlap>,
) -> FxHashMap<LocalDefId, Vec<ConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    borrow_conflicts_replaying_with_flows_impl(
        program,
        flows,
        is_ref,
        is_raw,
        is_mutable,
        raw_fields,
        selected_copy_lends,
        escaped_copy_lends,
        Some(parameter_overlaps),
    )
}

fn borrow_conflicts_replaying_with_flows_impl<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
    escaped_copy_lends: &SelectedCopyLendLoans,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, ParameterOverlap>>,
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
    let mut ctxt = NativeBorrowContext::new(program, flows, is_candidate, is_mutable);

    // §NB5-F2 — field candidacy: a struct-field slot the model settled `Raw` is a raw pointer, not a
    // borrow, so its loan must be disabled — the field analogue of a Raw local's `local_data=None`
    // demotion below. A field slot is `Raw` CRATE-WIDE, so disable it in EVERY function's provenance
    // set (the crate-wide hammer). `disable_owner` is a no-op where a function has no provenance for
    // that field, so passing the whole raw-field list is safe. Cleared field loans stop regenerating
    // the field conflicts that Option A (NB5-F) had to decline, so those programs now accept with the
    // field `Raw`. Genuinely un-dischargeable field residuals (never disabled here) still hit the
    // `residual_nonref_field` decline backstop in the caller — B narrows the decline set, not deletes it.
    for provenance_set in ctxt.borrow.provenances.values_mut() {
        for &field in raw_fields {
            provenance_set.disable_owner(ProvenanceOwner::Field(field));
        }
    }

    let mut out = FxHashMap::default();
    let no_copy_lends = FxHashSet::default();
    for f in program.functions.iter().copied() {
        let is_ref_f = is_ref(f);
        let is_raw_f = is_raw(f);
        let copy_lends = selected_copy_lends.get(&f).unwrap_or(&no_copy_lends);
        let escaped_copy_lends = escaped_copy_lends.get(&f).unwrap_or(&no_copy_lends);
        let escaped_borrower_locals = escaped_copy_lends
            .iter()
            .map(|identity| match identity.borrower {
                export::BorrowerKind::Assign {
                    owner: export::OwnerKey::Local(local),
                } => Local::from_u32(local),
                other => panic!("② feeder borrower must be a local temp, got {other:?}"),
            })
            .collect::<FxHashSet<_>>();
        assert_eq!(
            escaped_borrower_locals.len(),
            escaped_copy_lends.len(),
            "② exemption identities must map one-to-one to temp borrowers"
        );

        let edges = loop {
            let mut inference =
                ctxt.infer(program.tcx, f, raw_fields, copy_lends, escaped_copy_lends);
            let parameter_conflicts = overwrite_with_engine_facts(
                program.tcx,
                f,
                &ctxt.borrow,
                &mut inference.facts,
                &inference.copy_lends,
                parameter_overlaps.and_then(|overlaps| overlaps.get(&f)),
            );
            let parameter_edges = parameter_conflicts
                .into_iter()
                .filter(|(left, right)| is_ref_f(*left) && is_ref_f(*right))
                .map(|(left, right)| ConflictEdge {
                    issuer: Some(ProvenanceOwner::Local(left)),
                    requirers: vec![ProvenanceOwner::Local(right)],
                    esc_issuer_first: false,
                })
                .collect::<Vec<_>>();
            let invalid_loans = invalid_loan_set(&inference);
            if invalid_loans.is_empty() {
                // E-R4: a conflict-free function is exactly the case where every
                // loan SURVIVED, so this branch must record rather than exit
                // silently. Capturing only where edges are extracted would export
                // the invalid subset and nothing else.
                record_loan_identities(
                    f,
                    &inference,
                    ctxt.borrow.provenances.get(&f).unwrap(),
                    &invalid_loans,
                    &inference.copy_lends,
                );
                break parameter_edges;
            }

            let to_demote: Vec<(Local, Local)> = {
                let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
                let exemptions =
                    escaped_demotion_exemptions(&inference, provenance_set, &invalid_loans);
                assert!(exemptions.len() <= escaped_copy_lends.len());
                let local_witnesses = collect_invalid_loan_demotions_forked(
                    &inference,
                    provenance_set,
                    &invalid_loans,
                );
                local_witnesses
                    .into_iter()
                    .filter(|pair| !exemptions.contains(pair))
                    .filter(|(local, _base)| {
                        is_raw_f(*local) && provenance_set.local_data[*local].is_some()
                    })
                    .collect()
            };

            if to_demote.is_empty() {
                let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
                // E-R4: record from the FINAL inference — the loop above may
                // replay demotions, so earlier iterations are not the accepted
                // borrow set.
                record_loan_identities(
                    f,
                    &inference,
                    provenance_set,
                    &invalid_loans,
                    &inference.copy_lends,
                );
                let mut edges = extract_conflict_edges(&inference, provenance_set, &invalid_loans);
                edges.extend(parameter_edges);
                break edges;
            }

            drop(inference);
            let provenance_set = ctxt.borrow.provenances.get_mut(&f).unwrap();
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
        let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
        assert_escaped_conflicts_pre_demotion(edges.iter(), &is_ref_f, escaped_copy_lends.len());
        assert!(
            provenance_set
                .local_data
                .iter_enumerated()
                .all(|(local, data)| {
                    if !(is_raw_f(local) && data.is_some()) {
                        return true;
                    }
                    if escaped_borrower_locals.contains(&local) {
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
    flows: &OriginFlowResults,
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
    let selected = SelectedCopyLendLoans::default();
    borrow_conflicts_replaying_witnessed_with_copy_lends(
        program, flows, is_ref, is_raw, is_mutable, raw_fields, &selected,
    )
}

pub(crate) fn borrow_conflicts_replaying_witnessed_with_copy_lends<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
) -> FxHashMap<LocalDefId, Vec<WitnessedConflictEdge>>
where
    I: Fn(LocalDefId) -> J,
    J: Fn(Local) -> bool,
    M: Fn(LocalDefId) -> N,
    N: Fn(Local) -> bool,
    K: Fn(LocalDefId) -> L,
    L: Fn(Local) -> bool,
{
    let escaped = SelectedCopyLendLoans::default();
    borrow_conflicts_replaying_witnessed_with_copy_lends_and_escaped(
        program,
        flows,
        is_ref,
        is_raw,
        is_mutable,
        raw_fields,
        selected_copy_lends,
        &escaped,
    )
}

pub(crate) fn borrow_conflicts_replaying_witnessed_with_copy_lends_and_escaped<I, J, M, N, K, L>(
    program: &RustProgram,
    flows: &OriginFlowResults,
    is_ref: I,
    is_raw: M,
    is_mutable: K,
    raw_fields: &[StructFieldSlot],
    selected_copy_lends: &SelectedCopyLendLoans,
    escaped_copy_lends: &SelectedCopyLendLoans,
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
    let mut ctxt = NativeBorrowContext::new(program, flows, is_candidate, is_mutable);

    for provenance_set in ctxt.borrow.provenances.values_mut() {
        for &field in raw_fields {
            provenance_set.disable_owner(ProvenanceOwner::Field(field));
        }
    }

    let mut out = FxHashMap::default();
    let no_copy_lends = FxHashSet::default();
    for f in program.functions.iter().copied() {
        let is_raw_f = is_raw(f);
        let copy_lends = selected_copy_lends.get(&f).unwrap_or(&no_copy_lends);
        let escaped_copy_lends = escaped_copy_lends.get(&f).unwrap_or(&no_copy_lends);
        let escaped_borrower_locals = escaped_copy_lends
            .iter()
            .map(|identity| match identity.borrower {
                export::BorrowerKind::Assign {
                    owner: export::OwnerKey::Local(local),
                } => Local::from_u32(local),
                other => panic!("② feeder borrower must be a local temp, got {other:?}"),
            })
            .collect::<FxHashSet<_>>();
        assert_eq!(
            escaped_borrower_locals.len(),
            escaped_copy_lends.len(),
            "② exemption identities must map one-to-one to temp borrowers"
        );

        let edges = loop {
            let mut inference =
                ctxt.infer(program.tcx, f, raw_fields, copy_lends, escaped_copy_lends);
            let accesses = overwrite_with_engine_facts_capturing(
                program.tcx,
                f,
                &ctxt.borrow,
                &mut inference.facts,
                &inference.copy_lends,
            );
            let invalid_loans = invalid_loan_set(&inference);
            if invalid_loans.is_empty() {
                // D2: the witnessed/L2 replay is structurally identical to the
                // Mode-A one and had no capture at all, so `loans` was silently
                // empty under CRAT_BO_L2_GUARDED_COMMITS=1 — the plan-of-record
                // configuration. Same Gap-B reasoning applies here: a
                // conflict-free function is where every loan SURVIVED.
                record_loan_identities(
                    f,
                    &inference,
                    ctxt.borrow.provenances.get(&f).unwrap(),
                    &invalid_loans,
                    &inference.copy_lends,
                );
                break Vec::new();
            }

            let to_demote: Vec<(Local, Local)> = {
                let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
                let exemptions =
                    escaped_demotion_exemptions(&inference, provenance_set, &invalid_loans);
                assert!(exemptions.len() <= escaped_copy_lends.len());
                let local_witnesses = collect_invalid_loan_demotions_forked(
                    &inference,
                    provenance_set,
                    &invalid_loans,
                );
                local_witnesses
                    .into_iter()
                    .filter(|pair| !exemptions.contains(pair))
                    .filter(|(local, _base)| {
                        is_raw_f(*local) && provenance_set.local_data[*local].is_some()
                    })
                    .collect()
            };

            if to_demote.is_empty() {
                let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
                // D2: record from the FINAL inference of this call, exactly as
                // the Mode-A path does.
                record_loan_identities(
                    f,
                    &inference,
                    provenance_set,
                    &invalid_loans,
                    &inference.copy_lends,
                );
                break extract_witnessed_conflict_edges(
                    &inference,
                    provenance_set,
                    &invalid_loans,
                    accesses,
                );
            }

            drop(inference);
            let provenance_set = ctxt.borrow.provenances.get_mut(&f).unwrap();
            for (local, base) in to_demote {
                provenance_set.local_data[local] = None;
                provenance_set
                    .tree_borrow_local
                    .get_mut()
                    .union(local, base);
            }
        };

        let provenance_set = ctxt.borrow.provenances.get(&f).unwrap();
        assert_escaped_conflicts_pre_demotion(
            edges.iter().map(|witnessed| &witnessed.edge),
            |local| !is_raw_f(local),
            escaped_copy_lends.len(),
        );
        assert!(
            provenance_set
                .local_data
                .iter_enumerated()
                .all(|(local, data)| {
                    if !(is_raw_f(local) && data.is_some()) {
                        return true;
                    }
                    if escaped_borrower_locals.contains(&local) {
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

#[cfg(test)]
mod nb5o_tests {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::ty::TyCtxt;

    use super::*;

    fn program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = vec![];
        let mut structs = vec![];
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else {
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

    fn canonical(
        edges: FxHashMap<LocalDefId, Vec<ConflictEdge>>,
    ) -> Vec<(String, Vec<(String, Vec<String>)>)> {
        let mut out = edges
            .into_iter()
            .map(|(f, edges)| {
                let mut edges = edges
                    .into_iter()
                    .map(|edge| {
                        let mut requirers = edge
                            .requirers
                            .into_iter()
                            .map(|owner| format!("{owner:?}"))
                            .collect::<Vec<_>>();
                        requirers.sort();
                        (format!("{:?}", edge.issuer), requirers)
                    })
                    .collect::<Vec<_>>();
                edges.sort();
                (f.local_def_index.index().to_string(), edges)
            })
            .collect::<Vec<_>>();
        out.sort();
        out
    }

    #[test]
    fn nb5o_native_replay_matches_wrapped_edges() {
        let code = r#"
            #[inline(never)]
            unsafe fn id(p: *mut i32) -> *mut i32 { p }
            unsafe fn f(p: *mut i32) -> i32 {
                let mut cell = 0;
                let a = &mut cell as *mut i32;
                let b = &mut cell as *mut i32;
                let q = id(p);
                *a = 1;
                *b = *q;
                *a
            }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let wrapped = borrow_conflicts_wrapped(
                &program,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| true,
            );
            let native = borrow_conflicts(
                &program,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| true,
            );
            assert!(
                !wrapped.is_empty(),
                "replay fixture must exercise a conflict"
            );
            assert_eq!(canonical(native), canonical(wrapped));
        })
        .unwrap();
    }

    #[test]
    fn a5_w1_effective_parameter_overlap_reaches_replay() {
        let code = "unsafe fn f(x: *mut i32, y: *mut i32) { *x = *y + 1; }";
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let function = program.functions[0];
            let flows = crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(
                &program,
            );
            let selected = SelectedCopyLendLoans::default();
            let overlaps = FxHashMap::from_iter([(
                function,
                ParameterOverlap::from_pairs([(Local::from_usize(1), Local::from_usize(2))]),
            )]);
            let baseline = borrow_conflicts_replaying_with_flows_and_copy_lends(
                &program,
                &flows,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| false,
                |_: LocalDefId| |_: Local| true,
                &[],
                &selected,
            );
            let precise = borrow_conflicts_replaying_with_flows_and_parameter_overlap(
                &program,
                &flows,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| false,
                |_: LocalDefId| |_: Local| true,
                &[],
                &selected,
                &overlaps,
            );

            assert!(baseline.is_empty(), "distinct bases are the old blind spot");
            assert!(
                precise
                    .get(&function)
                    .is_some_and(|edges| !edges.is_empty()),
                "effective overlap must create a real replay conflict"
            );
        })
        .unwrap();
    }

    #[test]
    fn a5_w6_shared_shared_reads_stay_compatible() {
        let code = "unsafe fn f(x: *const i32, y: *const i32) -> i32 { *x + *y }";
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let function = program.functions[0];
            let flows = crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(
                &program,
            );
            let selected = SelectedCopyLendLoans::default();
            let overlaps = FxHashMap::from_iter([(
                function,
                ParameterOverlap::from_pairs([(Local::from_usize(1), Local::from_usize(2))]),
            )]);
            let precise = borrow_conflicts_replaying_with_flows_and_parameter_overlap(
                &program,
                &flows,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| false,
                |_: LocalDefId| |_: Local| false,
                &[],
                &selected,
                &overlaps,
            );

            assert!(precise.is_empty());
        })
        .unwrap();
    }

    #[test]
    fn a5_w12_parameter_overlap_changes_no_loan_identity_or_class() {
        use crate::analyses::borrow_ownership::export::{BorrowerKind, LoanClass, with_bo_export};

        let code = r#"
unsafe fn g(p: *mut i32) { *p = 9; }
unsafe fn f(p: *mut i32) -> i32 {
    g(p);
    *p
}
"#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|&did| tcx.item_name(did.to_def_id()).as_str() == "f")
                .expect("CALL_ARG function f");
            let flows = crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(
                &program,
            );
            let selected = SelectedCopyLendLoans::default();
            let overlaps = FxHashMap::from_iter([(
                function,
                ParameterOverlap::from_pairs([(Local::from_usize(1), Local::from_usize(2))]),
            )]);

            // Conflict equality is deliberately excluded. W1 owns that
            // territory and requires A5 to add parameter-overlap conflicts;
            // H3 compares the complete old-loan observation only.
            let (_, baseline_export) = with_bo_export(|| {
                borrow_conflicts_replaying_with_flows_and_copy_lends(
                    &program,
                    &flows,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| false,
                    |_: LocalDefId| |_: Local| true,
                    &[],
                    &selected,
                )
            });
            let (_, precise_export) = with_bo_export(|| {
                borrow_conflicts_replaying_with_flows_and_parameter_overlap(
                    &program,
                    &flows,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| false,
                    |_: LocalDefId| |_: Local| true,
                    &[],
                    &selected,
                    &overlaps,
                )
            });

            assert!(
                !baseline_export.loans.is_empty(),
                "CALL_ARG structural precondition: existing old-loan population"
            );
            assert!(
                baseline_export
                    .loans
                    .iter()
                    .any(|loan| matches!(loan.key.borrower, BorrowerKind::CallArg { .. })),
                "fixture must carry an existing CallArg population"
            );
            assert!(
                baseline_export
                    .loans
                    .iter()
                    .all(|loan| loan.class == LoanClass::Existing)
            );
            assert_eq!(precise_export.loans, baseline_export.loans);
        })
        .unwrap();
    }

    #[test]
    fn a5_precise_replay_does_not_widen_copy_lend_class() {
        use crate::analyses::borrow_ownership::{
            coherence::SelectedCopyLendLoan,
            export::{LoanClass, with_bo_export},
        };

        let code = "unsafe fn f(x: *const i32, y: *const i32) -> i32 { \
                    let q = x; *q + *y }";
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let function = program.functions[0];
            let flows = crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(
                &program,
            );
            let empty_selected = SelectedCopyLendLoans::default();
            let (_, seed_export) = with_bo_export(|| {
                borrow_conflicts_replaying_with_flows_and_copy_lends(
                    &program,
                    &flows,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| false,
                    |_: LocalDefId| |_: Local| false,
                    &[],
                    &empty_selected,
                )
            });
            let seed = seed_export
                .loans
                .iter()
                .find(|loan| loan.key.fn_did == function)
                .expect("fixture loan");
            let selected_identity = SelectedCopyLendLoan {
                location: seed.key.location,
                borrowed: seed.key.place.clone(),
                borrower: seed.key.borrower,
            };
            let selected = SelectedCopyLendLoans::from_iter([(
                function,
                FxHashSet::from_iter([selected_identity]),
            )]);
            let overlaps = FxHashMap::from_iter([(
                function,
                ParameterOverlap::from_pairs([(Local::from_usize(1), Local::from_usize(2))]),
            )]);

            let (baseline_edges, baseline_export) = with_bo_export(|| {
                borrow_conflicts_replaying_with_flows_and_copy_lends(
                    &program,
                    &flows,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| false,
                    |_: LocalDefId| |_: Local| false,
                    &[],
                    &selected,
                )
            });
            let (precise_edges, precise_export) = with_bo_export(|| {
                borrow_conflicts_replaying_with_flows_and_parameter_overlap(
                    &program,
                    &flows,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| false,
                    |_: LocalDefId| |_: Local| false,
                    &[],
                    &selected,
                    &overlaps,
                )
            });

            assert_eq!(canonical(precise_edges), canonical(baseline_edges));
            assert_eq!(precise_export.loans, baseline_export.loans);
            assert_eq!(
                precise_export
                    .loans
                    .iter()
                    .filter(|loan| loan.class == LoanClass::CopyLend)
                    .count(),
                1,
                "A5 must preserve exact typed CopyLend membership"
            );
        })
        .unwrap();
    }
}
