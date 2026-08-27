//! BO → rewriter export surface (E-R1..E-R4).
//!
//! Specification: `docs/agents/plan/2026-07-28-m05-export-surface-spec.md`.
//! Ruling basis: Q11 (loan-level identity) and R-Q1a (kind derived fork-side).
//!
//! # Contract
//!
//! Everything here is **recording-only**. No value in this module influences a
//! constraint, a clause, a selector, an acceptance decision, or an emitted
//! model. The capture is a write-only side channel, exactly like the existing
//! [`super::solver::with_selector_trace`] diagnostic it is modelled on.
//!
//! # Why a scoped thread-local rather than threaded parameters
//!
//! The M0.5 spec proposed threading a flag and a cursor through
//! `emit_crate_ownership_constraints`, `InferCtxt`, and `extract_conflict_edges`.
//! Recon against current source found three problems with that:
//!
//! 1. `BoOwnDatabase<'opt>` borrows the `Optimize` owned by `KindSolver`, so
//!    returning it would forbid moving the solver — which several existing call
//!    sites do.
//! 2. `extract_conflict_edges` has no `LocalDefId` in scope, and widening its
//!    signature risks the ordering contract `extract_witnessed_conflict_edges`
//!    depends on (it zips against `invalid_loans.iter()`).
//! 3. The capture points in the emission path run *before* verification, so a
//!    flag resolved inside verification would be resolved too late.
//!
//! A scoped thread-local recorder solves all three: it needs no signature
//! changes, it is `None` (and therefore free) on the production path, and its
//! scope is established by the caller before any capture point runs.
//!
//! # The env switch (`CRAT_BO_EXPORT`), and why it exists now
//!
//! D4 descoped an earlier `CRAT_BO_EXPORT` because it gated onto **nothing** —
//! it turned on a recorder no one read. That objection is spent: the switch now
//! gates [`arm_capture`], the production arm in `bo_c1::run::run_bo`, which is
//! a real consumer of the decision.
//!
//! Semantics: resolve-once per process, fail loud on anything other than `0`
//! or `1`, **default OFF**.
//!
//! - **Off (default):** `arm_capture` is inert, so the corpus worker pays no
//!   recording cost and its `t_emit_s`/`t_fixpoint_s` stay comparable to rows
//!   banked before the arm existed.
//! - **On:** the accepted-run region records, which makes the corpus-scale
//!   export-identity check reproducible directly — no temporary ambient patch
//!   of the kind the first such measurement needed.
//!
//! [`with_bo_export`] is **not** gated. It is the explicit-scope API used by
//! tests and by any future in-process consumer that has already decided it
//! wants a recording; the flag governs the *ambient* arm, not the explicit one.

use std::cell::RefCell;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Location, Place};
use z3::ast::Bool;

use super::{l2::MirLocationKey, solver::SlotRef, ssa::constraint::Var};

// ---------------------------------------------------------------------------
// Flag gating — resolve once, fail loud, default off
// ---------------------------------------------------------------------------

/// `CRAT_BO_EXPORT ∈ {0,1}`; unset means `0`. Anything else fails loudly.
///
/// Pure parse, so every branch is testable without touching the process
/// environment — mutating env in a parallel test binary is the D10 race class
/// this project has already paid for twice.
pub(crate) fn export_enabled_from_value(value: Option<&str>) -> bool {
    match value {
        None | Some("0") => false,
        Some("1") => true,
        Some(other) => panic!("CRAT_BO_EXPORT must be 0 or 1, got {other:?}"),
    }
}

fn export_enabled_from_env() -> bool {
    match std::env::var("CRAT_BO_EXPORT") {
        Ok(value) => export_enabled_from_value(Some(&value)),
        Err(std::env::VarError::NotPresent) => export_enabled_from_value(None),
        Err(error) => panic!("CRAT_BO_EXPORT is not valid Unicode: {error}"),
    }
}

/// Resolved at most once per process, so no two capture points can disagree.
static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

pub(crate) fn flag_enabled() -> bool {
    *FLAG.get_or_init(export_enabled_from_env)
}

// ---------------------------------------------------------------------------
// §1.2 Lifetime-free keys
// ---------------------------------------------------------------------------

/// One MIR projection element, lifetime-free and **total**.
///
/// D19/§1.2: the previous `PlaceKey` kept only `Deref` (as a *count*) and
/// `Field`, discarding `Index`, `ConstantIndex`, `Subslice`, `Downcast` and
/// `OpaqueCast`. That made `arr[i]` and `arr[j]` the SAME key, and — because
/// derefs were counted rather than sequenced — made `(*p).f` and `*(p.f)`
/// indistinguishable. A key built on that is not a key, so the encoding is
/// total and ordered now.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ProjKey {
    Deref,
    Field(u32),
    /// The MIR `Local` holding the index. Body-scoped, which is fine because
    /// `LoanKey` is scoped by `fn_did`; do NOT "normalize" it away.
    Index(u32),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    /// `VariantIdx`. The symbol name in the real `ProjectionElem` is not
    /// identity and is dropped deliberately.
    Downcast(u32),
    OpaqueCast,
    Subtype,
    UnwrapUnsafeBinder,
}

/// Lifetime-free, **order-preserving** projection of a MIR [`Place`].
///
/// `Place<'tcx>` cannot escape the analysis, so it is projected here — the same
/// pattern L2 established with [`MirLocationKey`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PlaceKey {
    pub local: Local,
    pub proj: Vec<ProjKey>,
}

impl PlaceKey {
    pub(crate) fn from_place(place: Place<'_>) -> Self {
        use rustc_middle::mir::ProjectionElem;
        let proj = place
            .projection
            .iter()
            .map(|elem| match elem {
                ProjectionElem::Deref => ProjKey::Deref,
                ProjectionElem::Field(f, _) => ProjKey::Field(f.as_u32()),
                ProjectionElem::Index(local) => ProjKey::Index(local.as_u32()),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => ProjKey::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                },
                ProjectionElem::Subslice { from, to, from_end } => {
                    ProjKey::Subslice { from, to, from_end }
                }
                ProjectionElem::Downcast(_, variant) => ProjKey::Downcast(variant.as_u32()),
                ProjectionElem::OpaqueCast(_) => ProjKey::OpaqueCast,
                ProjectionElem::Subtype(_) => ProjKey::Subtype,
                ProjectionElem::UnwrapUnsafeBinder(_) => ProjKey::UnwrapUnsafeBinder,
            })
            .collect();
        PlaceKey {
            local: place.local,
            proj,
        }
    }

    /// Derived view, kept so E-R2/E-R4 consumers written against the old shape
    /// do not change. The lossy form is no longer what is STORED.
    pub(crate) fn derefs(&self) -> usize {
        self.proj
            .iter()
            .filter(|p| matches!(p, ProjKey::Deref))
            .count()
    }

    /// Derived view; see [`PlaceKey::derefs`].
    pub(crate) fn fields(&self) -> Vec<u32> {
        self.proj
            .iter()
            .filter_map(|p| match p {
                ProjKey::Field(f) => Some(*f),
                _ => None,
            })
            .collect()
    }
}

pub(crate) fn location_key(location: Location) -> MirLocationKey {
    MirLocationKey::new(location.block.as_u32(), location.statement_index)
}

// ---------------------------------------------------------------------------
// §5.1 E-R4 — loan identity and the R-Q1a kind
// ---------------------------------------------------------------------------

/// The engine's effective per-loan kind, derived by exactly the expression the
/// invalidation path uses (R-Q1a §0.3).
///
/// **Three-valued on purpose.** The engine's guard is
/// `if let Some(p) = local_data[..] && !is_mutable(p) { continue }`, so a loan
/// whose base local has *no* provenance is **not** skipped. Collapsing that
/// case into [`LoanKind::Shared`] would invert the behaviour, which is why
/// [`LoanKind::skips_invalidation`] is the only predicate callers may branch on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoanKind {
    /// Provenance exists and is mutable — the immutable-skip does not fire.
    Mut,
    /// Provenance exists and is immutable — the immutable-skip fires.
    Shared,
    /// No provenance for the base local — the skip does not fire.
    NoProvenance,
}

/// How the loan entered BO replay. Orthogonal to mutability [`LoanKind`]: A12 uses this typed
/// class to apply shared CopyLend invalidation without changing older syntactic loan semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoanClass {
    Existing,
    CopyLend,
}

impl LoanKind {
    /// Reproduces the engine's branch at `borrow_engine/invalidates.rs`.
    ///
    /// This is the sole legal way to consume a `LoanKind` as a boolean.
    pub(crate) fn skips_invalidation(self) -> bool {
        matches!(self, LoanKind::Shared)
    }

    /// Derive from the raw provenance lookup, keeping `None` distinct.
    pub(crate) fn from_provenance_mutability(mutable: Option<bool>) -> Self {
        match mutable {
            Some(true) => LoanKind::Mut,
            Some(false) => LoanKind::Shared,
            None => LoanKind::NoProvenance,
        }
    }
}

/// Owner of an `Assign` borrow, mirrored lifetime-free with a total order.
///
/// D5 payload, restored: the spec always required it, M0 dropped it. As a
/// display field that was a precision loss; as a **key** component it is a
/// correctness question, which is why D5 became blocking for §1.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum OwnerKey {
    Local(u32),
    Field { struct_did: u32, field_index: usize },
}

impl OwnerKey {
    pub(crate) fn from_owner(owner: crate::analyses::borrow::ProvenanceOwner) -> Self {
        use crate::analyses::borrow::ProvenanceOwner;
        match owner {
            ProvenanceOwner::Local(l) => OwnerKey::Local(l.as_u32()),
            ProvenanceOwner::Field(f) => OwnerKey::Field {
                struct_did: f.struct_did.local_def_index.as_u32(),
                field_index: f.field_index,
            },
        }
    }
}

/// Which loan this is. Orthogonal to [`LoanKind`]: it feeds the access-dependent
/// self-loan skip, not the kind derivation (R-Q1a §0.5).
///
/// Both payloads are the D5 restoration. `arg_index` alone happened to separate
/// two `CallArg` loans at one terminator, but only because a terminator has one
/// callee — an accident of the current shape, not a property of the key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum BorrowerKind {
    Assign { owner: OwnerKey },
    CallArg { callee: u32, arg_index: usize },
}

/// The **stable content identity** of one loan (§1.3).
///
/// D19: `BorrowSet` loan *numbering* permutes between runs and between CEGAR
/// rounds, because `utils/dsa/union_find.rs` uses a `RandomState`-hashed
/// `HashSet` and `borrow/mod.rs` pushes sibling loans in `group()` iteration
/// order. An index into that numbering is therefore not an identity, which is
/// exactly what E-R4 was created to provide (ruling Q11).
///
/// **`kind` is deliberately NOT a component.** It is a pure function of
/// `fn_did` and the borrowed base local (R-Q1a §0.4), so it adds zero
/// discriminating power — and a *derived* component in an identity key is a
/// drift hazard: if the derivation ever moved, one loan would silently become
/// two identities. Keys are built from inputs, not from analysis outputs.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct LoanKey {
    pub fn_did: LocalDefId,
    pub place: PlaceKey,
    pub location: MirLocationKey,
    pub borrower: BorrowerKind,
}

impl LoanKey {
    /// Total order over primitives. `LocalDefId` is projected through
    /// `local_def_index.as_u32()`, the idiom `l2::StableLoanKey` already uses.
    fn ord_key(&self) -> (u32, &Local, &Vec<ProjKey>, MirLocationKey, BorrowerKind) {
        (
            self.fn_did.local_def_index.as_u32(),
            &self.place.local,
            &self.place.proj,
            self.location,
            self.borrower,
        )
    }
}

impl Ord for LoanKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ord_key().cmp(&other.ord_key())
    }
}

impl PartialOrd for LoanKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Ruling Q11: borrowed place, kind, program point — all three present, now
/// carried by a content key rather than by a run-local index.
///
/// `PartialEq` is **hand-written to exclude `run_local_handle`**, and that is a
/// contract requirement rather than a convenience. The handle is documented as
/// "never compare across runs"; deriving equality made the compiler compare it
/// across runs anyway, so two exports with identical CONTENT compared unequal
/// whenever D19 permuted the numbering. A field that is not identity must not
/// participate in identity.
#[derive(Clone, Debug, Eq)]
pub(crate) struct LoanIdentity {
    pub key: LoanKey,
    /// Run-local handle. **NOT an identity** (D19): `BorrowSet` numbering
    /// permutes between runs AND between CEGAR rounds. Valid only for
    /// correlating against other facts from the SAME inference — never
    /// serialize it, never compare it across runs, never use it as a map key.
    pub run_local_handle: usize,
    /// Attribute, not key — see [`LoanKey`].
    pub kind: LoanKind,
    pub class: LoanClass,
    /// Whether this loan was in the final round's invalid set. **Surviving
    /// loans are `false`** — those are the ones a re-route must match against.
    pub invalid: bool,
}

impl PartialEq for LoanIdentity {
    fn eq(&self, other: &Self) -> bool {
        // `run_local_handle` deliberately excluded — see the type doc.
        self.key == other.key
            && self.kind == other.kind
            && self.class == other.class
            && self.invalid == other.invalid
    }
}

/// One residual conflict the accepted model tolerated, flattened to owner keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResidualConflict {
    pub fn_did: LocalDefId,
    pub issuer: Option<SlotRef>,
    pub requirers: Vec<SlotRef>,
}

// ---------------------------------------------------------------------------
// §3 E-R2 — per-version ownership and move points
// ---------------------------------------------------------------------------

/// One consume site: a `(local, location)` pair the ownership emission visited.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VersionSite {
    pub fn_did: LocalDefId,
    pub local: Local,
    pub location: MirLocationKey,
    pub use_var: Option<Var>,
    pub def_var: Option<Var>,
}

// ---------------------------------------------------------------------------
// §4 E-R3 — selector provenance
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum BoundaryRole {
    Source,
    Sink,
}

/// Stable runtime identity of one T2 endpoint assertion. Artifact writers
/// render `fn_did` through `TyCtxt::def_path_str`; the in-process key keeps the
/// typed MIR/function identities used by construction.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct T2AssertKey {
    pub(crate) fn_did: LocalDefId,
    pub(crate) location: MirLocationKey,
    pub(crate) callee: String,
    pub(crate) role: BoundaryRole,
    pub(crate) var: Var,
}

impl T2AssertKey {
    pub(crate) fn sort_key(&self) -> (u32, MirLocationKey, &str, BoundaryRole, u32) {
        (
            self.fn_did.local_def_index.as_u32(),
            self.location,
            self.callee.as_str(),
            self.role,
            self.var.as_u32(),
        )
    }

    pub(crate) fn label(&self, function_path: &str) -> String {
        let role = match self.role {
            BoundaryRole::Source => "source",
            BoundaryRole::Sink => "sink",
        };
        format!(
            "t2-assert[{role}]({function_path}:{}:{}:{},{:?})",
            self.location.block, self.location.statement_index, self.callee, self.var,
        )
    }
}

/// The allocation or free call site behind one retractable selector.
///
/// Index-aligned with `Selectors::sources()` / `Selectors::sinks()` by
/// construction: `push_source_owning` / `push_sink_owning` are the only writers
/// of those vectors and each performs a single push.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SelectorSite {
    pub role: BoundaryRole,
    pub var: Var,
    /// The call site, when the emission walk knew it. `None` means the boundary
    /// was reached without an active call cursor — recorded rather than guessed.
    pub call: Option<CallSite>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallSite {
    pub fn_did: LocalDefId,
    pub location: MirLocationKey,
    pub callee: String,
}

// ---------------------------------------------------------------------------
// The capture itself
// ---------------------------------------------------------------------------

/// Everything the export records during one analysis run.
///
/// `PartialEq` is derived so a witness can compare the WHOLE record rather than
/// a hand-picked subset of fields (F5: the previous D16 witness compared 3 of 6
/// and called it "byte-identical").
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct BoExport {
    /// E-R2 consume sites, in emission order.
    pub version_sites: Vec<VersionSite>,
    /// E-R2 per-`Var` ownership, evaluated from the accepted model.
    pub version_owns: Option<IndexVec<Var, bool>>,
    /// E-R3 selector provenance, index-aligned with `Selectors`.
    pub source_sites: Vec<SelectorSite>,
    pub sink_sites: Vec<SelectorSite>,
    /// E-R4 loan identity for the complete final `BorrowSet`.
    pub loans: Vec<LoanIdentity>,
    /// E-R4 certificate: the residual conflicts the accepted model TOLERATES.
    ///
    /// **Empty on every fixture measured so far, but NOT provably empty — an
    /// earlier version of this doc claimed it was, and that claim is
    /// RETRACTED.** Acceptance is `committed == 0`, a round in which no
    /// residual was *committable*, which is weaker than "no residuals".
    ///
    /// The retracted argument ran: every conflict reaching the commit stage
    /// has a committable `Ref` owner, because a non-`Ref` FIELD residual
    /// declines (`residual_nonref_field`) and a non-`Ref` LOCAL residual trips
    /// `guard_slots_are_ref`. **Both guards are vacuous on an edge with no
    /// owners at all** — `.find()` over an empty iterator is `None`, `.all()`
    /// over an empty iterator is `true` — so they wave such an edge through,
    /// `representative` returns `None`, and it contributes nothing to
    /// `committed`. `representative`'s own doc names this case: "kept
    /// defensive (e.g. an empty edge)".
    ///
    /// Owner-less edges are producible by construction, not hypothetically: a
    /// `Borrower::CallArg` loan gets `issuer: None`
    /// (`borrow_engine/conflicts.rs`, the `Borrower::CallArg(..) => None`
    /// arm) and no membership constraint (`borrow_engine/origin_replay.rs`
    /// skips every non-`Assign` borrower), so no provenance can ever `require`
    /// it and its requirer list is necessarily empty. `map_edges_to_slots`
    /// `.map()`s rather than filters, so the empty edge reaches the conflict
    /// set intact.
    ///
    /// What is NOT established is whether such an edge can survive to an
    /// *accepting* round; no fixture exhibits one (ledger D15). So: empty in
    /// practice, unproven in general, and a consumer must not assume either
    /// way.
    ///
    /// **`Option`, not `Vec` — D14.** `None` means the accept point never ran,
    /// so nothing was recorded; `Some(vec![])` means it ran and tolerated no
    /// residual. As a bare `Vec` those two states were indistinguishable, and
    /// that is exactly why no test could detect deletion of the recorder: the
    /// default value and the recorded value were the same value. A consumer
    /// must not read `None` as "no residuals".
    ///
    /// **`None` on the L2 path** (see the ledger's D2 adjacent gap):
    /// `record_residuals`' sole call site is inside the Mode-A accept, so under
    /// `CRAT_BO_L2_GUARDED_COMMITS=1` the certificate is never recorded — which
    /// this type now says out loud instead of presenting as an empty set.
    pub residual_conflicts: Option<Vec<ResidualConflict>>,
}

impl BoExport {
    /// A move point is a site where the token leaves this local.
    ///
    /// **Ownership disappearance alone is not sufficient** and this method does
    /// not claim it is: a `free` sink also forces the def version non-owning,
    /// as do returns and by-value calls. Callers must conjoin the MIR-shape
    /// check that the location is an assignment `other = this` (R-Q1a follow-on
    /// finding #7). This returns the *candidate* sites only.
    pub(crate) fn move_point_candidates(
        &self,
        fn_did: LocalDefId,
        local: Local,
    ) -> Vec<MirLocationKey> {
        let Some(owns) = self.version_owns.as_ref() else {
            return Vec::new();
        };
        let owned = |v: Option<Var>| v.is_some_and(|v| owns.get(v).copied().unwrap_or(false));
        self.version_sites
            .iter()
            .filter(|s| s.fn_did == fn_did && s.local == local)
            .filter(|s| owned(s.use_var) && !owned(s.def_var))
            .map(|s| s.location)
            .collect()
    }

    /// Surviving loans — the ones a re-route may match against (§5.3).
    pub(crate) fn surviving_loans(&self) -> impl Iterator<Item = &LoanIdentity> {
        self.loans.iter().filter(|l| !l.invalid)
    }
}

thread_local! {
    /// `None` by default, so any path that has NOT armed performs no
    /// allocation, no collection and no sorting. Mirrors
    /// `solver::SELECTOR_TRACE_CAPTURE`.
    ///
    /// No longer the same as "the production path": `run_bo` arms the recorder
    /// around its accepted-run region, so the sweep worker does allocate and
    /// collect. See the module doc.
    static BO_EXPORT_CAPTURE: RefCell<Option<BoExport>> = const { RefCell::new(None) };
}

/// RAII arm for the **allow-list** capture discipline.
///
/// # Why an allow-list
///
/// M0 spent two cycles trying to make a deny-list work: suspend capture at
/// every probe surface that must not record. Both cycles shipped an
/// enumeration that turned out to be incomplete (F1 found four surfaces; ADV-1
/// then found a fifth and sixth reached through a helper). Enumeration is the
/// wrong correctness input — it fails open, silently, and each new probe
/// surface is a new chance to miss one.
///
/// Inverted: capture is armed **only** around the accepted-run region. Anything
/// outside that scope — probes, helpers, `solve_with_demotion`,
/// `explain_unsat`, and every surface not yet written — records nothing **by
/// construction**, with no list to maintain and nothing to keep in sync.
///
/// Drop ends the scope, so an early `return` out of the armed region is
/// correct without restructuring the region into a closure.
pub(crate) struct CaptureArm {
    prev: Option<BoExport>,
    /// `false` when `CRAT_BO_EXPORT` is off: the arm installed nothing and must
    /// therefore restore nothing, or it would clobber an enclosing scope.
    armed: bool,
}

impl Drop for CaptureArm {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        BO_EXPORT_CAPTURE.with(|c| *c.borrow_mut() = self.prev.take());
        // Non-`Send` scaffolding must not outlive the scope.
        VERSION_ASTS.with(|c| *c.borrow_mut() = None);
    }
}

impl CaptureArm {
    /// Take the recording and end the scope, in CANONICAL order.
    ///
    /// `loans` is sorted by [`LoanKey`] before it leaves the scope. Without
    /// this the vector carries `BorrowSet` index order, which D19 permutes
    /// between runs and between CEGAR rounds — so two analyses of the same
    /// program produced exports with identical CONTENT in different ORDER, and
    /// `BoExport`'s derived `PartialEq` compares `Vec`s order-sensitively.
    ///
    /// That was not hypothetical: it made the probe-barrage witness flake
    /// (838/1 then 839/0 on consecutive runs), differing only in two loans
    /// swapping position. Canonicalising here is what makes E-R4 reproducible
    /// for the consumer the content key was introduced for — an unordered
    /// identity set is not much use if the container it ships in is unordered
    /// too.
    ///
    /// Recording-only is unaffected: this runs after the analysis, on the way
    /// out of the scope.
    pub(crate) fn finish(self) -> BoExport {
        if !self.armed {
            return BoExport::default();
        }
        let mut captured = BO_EXPORT_CAPTURE
            .with(|c| c.borrow_mut().take())
            .unwrap_or_default();
        captured.loans.sort_by(|a, b| a.key.cmp(&b.key));
        // `self`'s Drop still runs, restoring the previous scope.
        captured
    }
}

/// Arm capture for the accepted-run region, **if `CRAT_BO_EXPORT=1`**.
///
/// Off by default, in which case this is one `OnceLock` read and the returned
/// arm is inert: nothing is installed, nothing is restored on drop, and
/// `finish()` yields an empty export. See the module doc for why the flag
/// exists now when D4 removed its predecessor.
pub(crate) fn arm_capture() -> CaptureArm {
    if !flag_enabled() {
        return CaptureArm {
            prev: None,
            armed: false,
        };
    }
    arm_scope()
}

/// Unconditional arm — the explicit-scope primitive behind [`with_bo_export`],
/// deliberately NOT flag-gated.
///
/// Witnesses of the *positional* allow-list property use this rather than
/// [`arm_capture`]: "probes outside the armed region record nothing" is
/// orthogonal to whether the ambient flag is set, and testing it through the
/// gated entry would make it pass vacuously whenever the flag is off (i.e.
/// always, by default).
pub(crate) fn arm_scope() -> CaptureArm {
    let prev = BO_EXPORT_CAPTURE.with(|c| c.replace(Some(BoExport::default())));
    VERSION_ASTS.with(|c| *c.borrow_mut() = None);
    CaptureArm { prev, armed: true }
}

/// Run `f` with export capture active, returning its result and the recording.
///
/// The returned value is the exact result of `f`; the capture cannot influence
/// it. Nesting is safe — the previous capture is restored on unwind as well as
/// on normal return.
pub(crate) fn with_bo_export<T>(f: impl FnOnce() -> T) -> (T, BoExport) {
    let arm = arm_scope();
    let output = f();
    (output, arm.finish())
}

/// Whether capture is active.
///
/// Active if and only if a scope is open — [`with_bo_export`] or
/// [`arm_capture`]. There is no env-driven enablement (D4, descoped), and off
/// any scope this is one thread-local read of an `Option` with every capture
/// point short-circuiting on it. Inside `run_bo`'s armed region it is true.
pub(crate) fn capturing() -> bool {
    BO_EXPORT_CAPTURE.with(|c| c.borrow().is_some())
}

/// Mutate the active capture, or do nothing when inactive.
///
/// Every capture point funnels through here, so "zero work when off" is a
/// property of one function rather than of every call site.
pub(crate) fn record(f: impl FnOnce(&mut BoExport)) {
    if !capturing() {
        return;
    }
    BO_EXPORT_CAPTURE.with(|c| {
        if let Some(export) = c.borrow_mut().as_mut() {
            f(export);
        }
    });
}

// ---------------------------------------------------------------------------
// E-R3 call cursor
// ---------------------------------------------------------------------------
//
// The data a `SelectorSite` needs is split across two frames that never meet:
// the MIR walk knows `(fn_did, location)` at the terminator, while the callee
// name is only known one frame deeper, in the boundary dispatch. Rather than
// widen either signature, both halves are parked in scoped thread-locals and
// joined at the push site. Same shape as `solver::with_selector_trace` and
// `infer::with_own_assume_site`.

thread_local! {
    static LOCATION_CURSOR: RefCell<Option<(LocalDefId, MirLocationKey)>> =
        const { RefCell::new(None) };
    static CALLEE_CURSOR: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Set the `(fn_did, location)` half for the duration of `f`.
pub(crate) fn with_terminator_site<T>(
    fn_did: LocalDefId,
    location: Location,
    f: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<(LocalDefId, MirLocationKey)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOCATION_CURSOR.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore =
        Restore(LOCATION_CURSOR.with(|c| c.replace(Some((fn_did, location_key(location))))));
    f()
}

/// Set the callee-name half for the duration of `f`.
pub(crate) fn with_callee<T>(callee: &str, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<String>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CALLEE_CURSOR.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(CALLEE_CURSOR.with(|c| c.replace(Some(callee.to_owned()))));
    f()
}

/// Join both halves. `None` when either is missing — recorded as unknown rather
/// than guessed.
pub(crate) fn current_call_site() -> Option<CallSite> {
    let (fn_did, location) = LOCATION_CURSOR.with(|c| *c.borrow())?;
    let callee = CALLEE_CURSOR.with(|c| c.borrow().clone())?;
    Some(CallSite {
        fn_did,
        location,
        callee,
    })
}

/// Join the always-scoped call cursor into the key used by T2 construction.
/// Unlike `record_selector`, this is normative construction input and
/// therefore remains available when export capture is off.
pub(crate) fn current_t2_assert_key(role: BoundaryRole, var: Var) -> T2AssertKey {
    let call = current_call_site().unwrap_or_else(|| {
        panic!("T2 endpoint assertion emitted outside a modeled call-site cursor")
    });
    T2AssertKey {
        fn_did: call.fn_did,
        location: call.location,
        callee: call.callee,
        role,
        var,
    }
}

/// Record one retractable selector at its push site (E-R3).
pub(crate) fn record_selector(role: BoundaryRole, var: Var) {
    record(|export| {
        let site = SelectorSite {
            role,
            var,
            call: current_call_site(),
        };
        match role {
            BoundaryRole::Source => export.source_sites.push(site),
            BoundaryRole::Sink => export.sink_sites.push(site),
        }
    });
}

/// Record one consume site during ownership emission (E-R2).
pub(crate) fn record_version_site(
    fn_did: LocalDefId,
    local: Local,
    location: Location,
    use_var: Option<Var>,
    def_var: Option<Var>,
) {
    record(|export| {
        export.version_sites.push(VersionSite {
            fn_did,
            local,
            location: location_key(location),
            use_var,
            def_var,
        })
    });
}

thread_local! {
    /// Emission scaffolding, deliberately NOT a field of [`BoExport`]:
    /// `z3::ast::Bool` is not `Send`, and `BoExport` has to cross the
    /// `run_compiler_on_str` boundary. The ASTs never leave the analysis; only
    /// the evaluated `bool`s do.
    static VERSION_ASTS: RefCell<Option<IndexVec<Var, Bool>>> = const { RefCell::new(None) };
}

/// Stash the emission's `Var -> Bool` map so the model readout can evaluate it
/// after the database has been dropped. Cloned rather than borrowed:
/// `BoOwnDatabase` borrows the `Optimize` the solver owns, but `Bool` is itself
/// lifetime-free, so the snapshot carries no borrow.
pub(crate) fn record_version_asts(asts: &IndexVec<Var, Bool>) {
    if !capturing() {
        return;
    }
    VERSION_ASTS.with(|c| *c.borrow_mut() = Some(asts.clone()));
}

/// Evaluate the stashed ASTs against a live model (E-R2).
///
/// `eval` runs only when a capture is active AND the ASTs were stashed, so the
/// model evaluation costs nothing on the production path.
pub(crate) fn record_version_owns_from(
    eval: impl FnOnce(&IndexVec<Var, Bool>) -> IndexVec<Var, bool>,
) {
    if !capturing() {
        return;
    }
    let owns = VERSION_ASTS.with(|c| c.borrow().as_ref().map(eval));
    if let Some(owns) = owns {
        record(|export| export.version_owns = Some(owns));
    }
}

/// Record one loan's identity (E-R4).
pub(crate) fn record_loan(identity: LoanIdentity) {
    record(|export| export.loans.push(identity));
}

/// Start a fresh validation round (D1).
///
/// The borrow oracle runs once per CEGAR round, each time under a DIFFERENT
/// candidacy predicate. Without this reset `loans` would accumulate the union
/// over all rounds — including loans from models the loop went on to reject —
/// and `surviving_loans()` would mix stale pre-commit loans with accepted ones.
/// Clearing at the start of every round leaves exactly the accepted round's
/// `BorrowSet` behind when the loop exits.
///
/// Residuals are cleared with them: they are recorded at the accept point and
/// must describe the same round.
pub(crate) fn begin_round() {
    record(|export| {
        export.loans.clear();
        // Back to "not recorded this round" — NOT to "recorded, none found".
        export.residual_conflicts = None;
    });
}

// `snapshot()` and `with_capture_suspended()` were DELETED in the allow-list
// cycle, and the second deletion is not merely tidying orphaned code.
// `with_capture_suspended` IS the deny-list primitive: leaving it callable
// would let one line silently re-create the discipline this module just
// abandoned, and make the tripwire in `model_accepts_with_flows` unreachable
// for whatever it wrapped. Capture is positional now — armed around the
// accepted run, inert everywhere else — and there is deliberately no API for
// making an exception.

/// Record the residual conflicts present at acceptance (E-R4 certificate).
///
/// Called at the `committed == 0` accept point, where the residual set is the
/// one the accepted model tolerates.
pub(crate) fn record_residuals(residuals: Vec<ResidualConflict>) {
    record(|export| export.residual_conflicts = Some(residuals));
}

/// E-R1 is the accepted model itself, which existing entry points already
/// return. This alias exists so the four E-R names are all nameable.
pub(crate) type AcceptedModel = FxHashMap<SlotRef, SlotKindAlias>;
pub(crate) use super::domain::SlotKind as SlotKindAlias;

#[cfg(test)]
mod tests;
