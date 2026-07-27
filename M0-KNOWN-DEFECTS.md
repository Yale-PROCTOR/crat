# M0 defect ledger

Five adversarial review lenses ran against `f9ee8fee` (read-only). 38 raw
findings; nine re-verified and accepted. Four were HIGH and blocked merge.

**Status after delta verification of `9f21eac8`: D1, D2, D3 CLOSED. D4 NOT
CLOSED — my fix is incomplete and its witness cannot fail. D5–D9 remain open.
Two new defects (D10, D11) were introduced by the fix delta and are recorded.**

M0 remains **not merge-ready**.

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

*Verification caveat, accepted:* the review notes neither witness **pins the
round count**, so on these small fixtures they may accept in one round and
would then not have failed against the pre-fix behaviour. The fix is correct
by construction (`begin_round()` at the top of both loop bodies, before the
oracle, with the accept returning inside the same iteration), but a fixture
with an asserted `stats.rounds > 1` would make the witness load-bearing.
Registered for M0.1.

*Useful correction from the review:* candidacy is **not** model-dependent
(`is_candidate` reduces to `slot_for_local_depth(local, 0).is_some()`,
constant across rounds), so loan indices are stable and cross-round entries
collide exactly on `(fn_did, loan)` — which is precisely what the restored
cardinality assertion keys on. The dedup check is the right shape.

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

*Witness:* `l2_path_records_loans`. **Caveat the review is right about:**
every assertion it makes is already satisfied on the Mode-A path, so it is
non-distinguishing — it would pass with the L2 capture removed unless the L2
route is actually taken. The code fix itself was verified by direct reading of
both exits, not via this test.

*Adjacent gap, still open:* the L2 accept path never records **residuals**, so
`export.residual_conflicts` is unconditionally empty under
`CRAT_BO_L2_GUARDED_COMMITS=1`. That pre-dates the delta; what the delta
changed is that `begin_round()`'s clear makes the emptiness indistinguishable
from "recorded, none found".

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

### D4 — `CRAT_BO_EXPORT` was a dead switch — **NOT CLOSED**

*Was:* the flag was parsed, validated, and tested — and consulted by nothing.
Setting it to 1 recorded nothing, contradicting the module doc's claim that a
corpus worker could request capture without a Rust-level scope.

*Fix:* `capturing()` now consults a resolve-once `OnceLock<bool>` and installs
a capture buffer lazily when the flag is on. Scope-based enablement is
unchanged for tests. Feature-off identity is preserved: with the flag unset,
`capturing()` is one thread-local read returning false.

*Witness:* `export_flag_gates_capture` — **and the delta review is right that
this witness cannot fail.** It asserts `!capturing() || flag`, which holds
byte-identically with the flag branch deleted. It is the same tautology class
as D3, reintroduced in the fix for D4.

**Why D4 is still open — the fix is write-only.** `capturing()` now installs a
buffer when the flag is on, but **nothing can retrieve it**: `with_bo_export`
is the only reader of `BO_EXPORT_CAPTURE`, and it installs its own fresh
buffer on entry. So `CRAT_BO_EXPORT=1` makes capture *run* and then discards
everything — the corpus-worker capability the module doc promises still does
not exist. The flag now gates, but gates onto nothing.

*Required to close:* a drain API (e.g. `take_export() -> BoExport`) so the
flag path has a reader, plus a witness that actually fails with the flag
branch removed. Both are M0.1 work; I did not start another fix cycle without
authorization, having just seen an unverified fix introduce two new defects.

*Secondary, also open:* on the flag path the buffer is never bracketed, so
`version_sites`, `source_sites` and `sink_sites` grow for the process
lifetime — `begin_round()` clears only `loans` and `residual_conflicts`.

> **Secondary finding, fixed in passing.** Wiring the flag into `capturing()`
> made RED 1's `set_var("CRAT_BO_EXPORT", "2")` a **data race**: the suite runs
> tests in parallel, and another thread's `capturing()` would observe the
> temporary invalid value and panic. Split into a pure
> `export_enabled_from_value(Option<&str>)` plus a thin env reader — the same
> split `rewriter::decision_snapshot_pre_transform_enabled_from_value` already
> uses. RED 1 now exercises the parse without touching the process
> environment.

## Introduced by the fix delta

- **D10 (HIGH)** `capture_solve_l2` mutates `CRAT_BO_L2_GUARDED_COMMITS` with
  `set_var` inside a parallel test binary — **the same data-race class I had
  just fixed for `CRAT_BO_EXPORT`**, reintroduced one test-helper over. It is
  panic-safe within its own thread (`catch_unwind` + `remove_var` +
  `resume_unwind`) but not safe against a concurrently running test. Fix: an
  L2 mode provider parameter, or a serial-test guard.
- **D11 (MEDIUM)** `model_accepts_with_flows` calls the loan-recording oracle
  **outside** either CEGAR loop, so no `begin_round()` precedes it. Latent
  today (nothing opens a scope around it), but D4's flag path would make it
  live: with the flag on, that call would append loans with no round reset,
  reopening D1 by another route.

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
