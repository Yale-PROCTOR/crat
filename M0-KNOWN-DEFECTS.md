# M0 defect ledger

Five adversarial review lenses ran against `f9ee8fee` (read-only). 38 raw
findings; nine re-verified and accepted. Four were HIGH and blocked merge.

**Status: D1–D4 CLOSED, each with a named witness test. D5–D9 remain open and
are recorded below with a recommended disposition.**

Suite after fixes: **834 passed, 0 failed, 7 ignored.**

## Closed

### D1 — `export.loans` accumulated across CEGAR rounds — **CLOSED**

*Was:* the oracle runs once per validation round, each under a different
candidacy predicate, and the recorder appended. `export.loans` held the union
over all rounds, so `surviving_loans()` mixed loans from rejected intermediate
models with the accepted one.

*Fix:* `export::begin_round()` clears `loans` and `residual_conflicts` at the
top of **both** round loops (`borrow_verify.rs:682` Mode-A,
`borrow_verify.rs:975` L2). What survives the loop is exactly the accepted
round's `BorrowSet`. Chose per-round reset over capture-at-accept because the
oracle is where the loan set exists; the accept point only sees conflicts.

*Witnesses:* `loan_identity_covers_the_complete_borrow_set` (spec RED 14's
**restored cardinality equality** — one record per `(fn_did, loan)`), and
`multi_round_export_holds_only_the_final_round`.

> **The RED-weakening trap — on the record for future milestones.**
> I had weakened RED 14 from the spec's cardinality equality to a
> non-emptiness check. That single weakening is what let D1 through: with the
> recorder appending N copies of every loan, no non-emptiness assertion could
> ever see it. **A weakened assertion does not merely test less — it can be
> precisely the assertion that would have caught the defect.** When a spec
> names a cardinality, implement the cardinality.

### D2 — the L2 path captured no loans — **CLOSED**

*Was:* `borrow_conflicts_replaying_witnessed` — the L2 oracle — had no
capture on either loop exit, so `loans` was silently empty under
`CRAT_BO_L2_GUARDED_COMMITS=1`, the plan-of-record configuration.

*Fix:* `record_loan_identities` wired on both witnessed exits, with the same
Gap-B reasoning (capture before the `invalid_loans.is_empty()` early break).
Capture now exists on all four replay exits across the two paths.

*Witness:* `l2_path_records_loans` — solves an L2-on fixture and asserts
non-empty **and** round-correct (one record per loan) loans.

### D3 — the R-Q1a witness was a tautology — **CLOSED**

*Was:* `loan_kind_matches_engine_skip` asserted
`skips_invalidation() == (kind == Shared)` — true by the definition of the
method, unable to fail if the derivation drifted. **The commit message's claim
that the four R-Q1a witnesses included "kind matches the engine's skip
contract" was therefore an overclaim, and is withdrawn here.**

*Fix:* replaced with `loan_kind_matches_ground_truth_provider` and
`loan_kind_follows_the_provider_both_ways`. Ground truth is a
`SelectiveMut` provider the test supplies: the derivation must reproduce
`is_mutable(fn_did, borrowed.local)` for a known answer. This simultaneously
witnesses the **base-local keying** of R-Q1a §0.4 — a derivation keyed on the
projected place would look up a different local and disagree.

*Proof the witness can fail:* mutating the derivation to key on
`Local::from_u32(0)` makes **3 of 4** kind tests fail with precise
diagnostics ("derivation disagreed with the supplied provider for base local
_1 … the key or the lookup has drifted"). Verified, then reverted.

### D4 — `CRAT_BO_EXPORT` was a dead switch — **CLOSED**

*Was:* the flag was parsed, validated, and tested — and consulted by nothing.
Setting it to 1 recorded nothing, contradicting the module doc's claim that a
corpus worker could request capture without a Rust-level scope.

*Fix:* `capturing()` now consults a resolve-once `OnceLock<bool>` and installs
a capture buffer lazily when the flag is on. Scope-based enablement is
unchanged for tests. Feature-off identity is preserved: with the flag unset,
`capturing()` is one thread-local read returning false.

*Witness:* `export_flag_gates_capture`, plus `export_flag_rejects_invalid_value`.

> **Secondary finding, fixed in passing.** Wiring the flag into `capturing()`
> made RED 1's `set_var("CRAT_BO_EXPORT", "2")` a **data race**: the suite runs
> tests in parallel, and another thread's `capturing()` would observe the
> temporary invalid value and panic. Split into a pure
> `export_enabled_from_value(Option<&str>)` plus a thin env reader — the same
> split `rewriter::decision_snapshot_pre_transform_enabled_from_value` already
> uses. RED 1 now exercises the parse without touching the process
> environment.

## Open — recorded, not fixed

Outside M0's authorized fix scope; recommended for M0.1.

- **D5 (MEDIUM)** `BorrowerKind` drops both payloads the spec requires (the
  `Assign` `ProvenanceOwner`, the `CallArg` callee `LocalDefId`). §0.5's
  stated reason for exporting `BorrowerKind` — letting a consumer reproduce
  the access-dependent self-loan skip — is not met without the owner.
- **D6 (MEDIUM)** `VERSION_ASTS` is the one capture thread-local without an
  RAII guard: a nested `with_bo_export` wipes the outer snapshot; a panic
  leaves it set.
- **D7 (MEDIUM)** Spec fields still missing: `BorrowCertificate::ref_slots` /
  `raw_slots`, `SelectorSite::local`, and the in-analysis surviving/leaked
  selector partition (which makes spec RED 12 and the "surviving" half of
  RED 11 unimplementable as written).
- **D8 (MEDIUM)** Spec RED tests 2, 7, 12, 13 remain absent.
- **D9 (MEDIUM)** The import-denylist matcher is defeated by brace-grouped
  imports (`use crate::{rewriter::…}`).

## Confirmed clean (unchanged by the fixes)

- The **R-Q1a derivation** is faithful: same two-step lookup, same base-local
  key, `NoProvenance` correctly distinct from `Shared`, same `ProvenanceSet`
  object as the engine, and the on-path `is_mutable()` sweep re-verifies as
  exactly the two `invalidates.rs` sites.
- **Recording-only holds.** No capture site mutates solver state, changes
  control flow or iteration order, or allocates when off.
- **Mirror and ordering contracts intact.** `extract_conflict_edges` is
  byte-identical to `borrow/mod.rs`'s version; the `.zip(invalid_loans.iter())`
  contract is unperturbed; no signature changed.

## Environment notes (required by the M0 verification list)

**Frozen-corpus symlink workaround.** `benchmarks/rs-*` is `.gitignore`d, so
the frozen corpus does not exist in any git worktree — only in the main
checkout. `bo_c1::rs_crown_catalog_contract` needs it, and fails in a fresh
worktree with a missing-input error that reads like a regression but is
environmental (same family as the `deps_crate` traps). Workaround:

```
ln -sfn /Users/p51lee/dev/crat/benchmarks/rs-crown <worktree>/benchmarks/rs-crown
ln -sfn /Users/p51lee/dev/crat/deps_crate/target   <worktree>/deps_crate/target
```

**The symlink points into the REAL frozen corpus**, so it is acceptable only
with a digest check standing guard. Frozen-tree digest, recomputed at the end
of this milestone:

```
find -L benchmarks/rs-crown -type f -name '*.rs' | sort | xargs shasum -a 256 | shasum -a 256
9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621
```

This check belongs in every future verification list that uses the symlink: if
it moves, the frozen corpus was written through the link and comparability
with CROWN's published numbers is void.

**Machine scope.** Unit scope only throughout. No corpus-scale run; those
remain queued behind the pairwise-probing sweep, which owns the corpus
machine. `cargo build`/`cargo test -p pointer_replacer` at `-j 6` only.
