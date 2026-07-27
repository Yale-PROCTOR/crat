# M0 — known defects found by post-implementation adversarial review

Five review lenses ran against `f9ee8fee` (read-only, no builds). 38 raw
findings. The ones below I re-verified against source myself and accept as
**real**. They are recorded here rather than silently fixed, because AGENTS.md
rule 6 makes adversarial review a review-only step and M0's authorized scope
ended at RED→GREEN.

**M0 should not be merged until D1–D4 are resolved.** The suite is green
(830 passed) and the constraints hold (zero production edits, frozen rewriter
and corpus untouched), but E-R4's contract is not met.

## D1 — `export.loans` accumulates across CEGAR rounds (HIGH)

`record_loan_identities` fires once per function per call of
`borrow_conflicts_replaying_with_flows`, and `verify_to_fixpoint_counting`
calls the oracle **once per validation round** (`for _ in 0..cap`). So after
N rounds `export.loans` holds ~N copies of each function's loan set, each
derived from a *different* candidacy predicate, each stamped with that round's
`invalid` bit.

Consequence: `surviving_loans()` mixes loans from rejected intermediate models
with the accepted one. E-R4 claims "the COMPLETE final `BorrowSet`"; it
delivers the union over all rounds. A §5.3 admissibility lookup could match a
re-route against a loan that the accepted model does not contain — the exact
failure Q1's condition exists to prevent.

Fix direction: clear `loans` at the start of each round, or key the recorder
by round and keep only the last, or capture at the accept point rather than
inside the oracle.

## D2 — the L2 path captures no loans at all (HIGH)

`borrow_conflicts_replaying_witnessed` — the L2 oracle — has no
`record_loan_identities` call on either loop exit. With
`CRAT_BO_L2_GUARDED_COMMITS=1`, `export.loans` is empty and
`surviving_loans()` yields nothing, silently.

L2 is the plan-of-record configuration (GREEN-3, 24/26 recovery). The commit
message's Gap-B claim is true for the Mode-A function only; the structurally
identical witnessed variant was missed.

## D3 — RED 15b is a tautology and cannot detect drift (HIGH)

`loan_kind_matches_engine_skip` asserts
`kind.skips_invalidation() == (kind == LoanKind::Shared)`, which is true by
the definition of `skips_invalidation`. It cannot fail if the fork-side
derivation drifts from the engine — which is the *only* failure mode R-Q1a's
runtime witness was supposed to guard.

**The commit message's claim that the four R-Q1a witnesses include "kind
matches the engine's skip contract" is therefore an overclaim.** The
derivation is correct by inspection (all five lenses independently confirmed
the expression, the key, and the `NoProvenance` handling), but it is not
guarded at runtime.

Fix direction: re-run the engine's own guard expression over the recorded
loans inside the test and compare, rather than comparing the enum to itself.

## D4 — `CRAT_BO_EXPORT` is a dead switch (HIGH)

`export_enabled_from_env()` exists, is fail-loud, and is tested — but nothing
on any capture path consults it. Capture is enabled solely by the
`with_bo_export` scope. Setting `CRAT_BO_EXPORT=1` records nothing.

The module doc claims the flag exists so "a corpus worker needs to request
capture without a Rust-level scope" — which is precisely what it cannot do.

## Accepted as real, lower severity

- **D5 (MEDIUM)** `BorrowerKind` drops both payloads the spec requires (the
  `Assign` `ProvenanceOwner`, the `CallArg` callee `LocalDefId`), defeating
  §0.5's stated reason for exporting it: a consumer cannot reproduce the
  self-loan skip without the owner to compare against the accessing place.
  Undeclared deviation.
- **D6 (MEDIUM)** `VERSION_ASTS` is the one capture thread-local without an
  RAII guard: a nested `with_bo_export` wipes the outer scope's snapshot, and
  a panic leaves it set.
- **D7 (MEDIUM)** Spec fields still missing: `BorrowCertificate::ref_slots` /
  `raw_slots`, `SelectorSite::local`, and the in-analysis
  surviving/leaked selector partition (which makes spec RED 11's "surviving"
  half and RED 12 unimplementable as written).
- **D8 (MEDIUM)** Four spec RED tests remain absent (2, 7, 12, 13), and five
  present ones assert non-emptiness where the spec asks for cardinality.
  RED 14's weakening is what let D1 through.
- **D9 (MEDIUM)** The import-denylist matcher is defeated by brace-grouped
  imports (`use crate::{rewriter::…}`) — the idiomatic form a developer
  merging imports would write.

## Confirmed clean

- The R-Q1a **derivation itself** is faithful: same two-step lookup, same key
  (`borrowed.local`, projections ignored), `NoProvenance` correctly distinct
  from `Shared`, same `ProvenanceSet` object as the engine, and the on-path
  `is_mutable()` sweep re-verifies as exactly the two `invalidates.rs` sites.
- **Recording-only holds.** No capture site mutates solver state, changes
  control flow or iteration order, or allocates when off. Two specific hazards
  were chased and refuted: the new eager `.unwrap()` cannot panic (the same
  unwrap already runs unconditionally later), and `read_version_owns` running
  before `read_kinds` cannot perturb kinds (disjoint decl sets).
- **Mirror and ordering contracts intact.** `extract_conflict_edges` is
  byte-identical to `borrow/mod.rs`'s version; the
  `.zip(invalid_loans.iter())` contract is unperturbed; no signature changed.
- All three declared deviations verified true as stated.
