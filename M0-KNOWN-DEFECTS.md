# M0 defect ledger

Five adversarial review lenses ran against `f9ee8fee` (read-only). 38 raw
findings; nine re-verified and accepted. Four were HIGH and blocked merge.

**Status after fix cycle 3: D1, D2, D3, D4, D10, D11, D12 CLOSED — every
closure mutation-tested. D5–D9 remain open, plus one new spec-vs-reality
finding (D13). M0 is merge-ready on the export surface's own terms; the
corpus-scale identity check remains queued behind the pairwise sweep.**

Suite: **833 passed, 0 failed, 7 ignored.**

---

## STANDING RULE — witnesses must be mutation-tested

**Every witness test must be mutation-tested before it counts: delete or break
the exact branch or derivation it claims to guard, and demonstrate that the
test fails. A witness that cannot fail is not a witness.**

This carries to all future milestones, not just M0. It is the systematic
counter to M0's recorded failure classes below.

Two operational riders learned in cycle 3:

1. **Verify the mutation was effective.** Two of this cycle's five mutation
   attempts produced no signal for the wrong reason — one panicked before
   reaching the assertion (`conflicts.keys().next().unwrap()` on an empty map),
   one was silently overwritten by the very call it was meant to replace
   (`record_residuals` assigns, so a prepended fabrication was clobbered). Both
   *looked* like "the test passed under mutation". An ineffective mutation is
   not evidence either way; when a mutation does not fail the test, first prove
   the mutation actually took effect.
2. **Mutate the narrowest thing.** The first attempt at the D2 mutation split
   the file at a character offset and deleted all four `record_loan_identities`
   sites instead of the two on the L2 path. That would have "passed" the
   mutation test while proving nothing about the L2-specific claim. Cut on
   syntactic boundaries and confirm the sites you did not intend to touch are
   intact.

### M0's two recorded failure classes

> **1. The RED-weakening trap.** I weakened spec RED 14 from a cardinality
> equality to a non-emptiness check. That single weakening is what let D1
> through: with the recorder appending N copies of every loan, no non-emptiness
> assertion could ever see it. **A weakened assertion does not merely test less
> — it can be precisely the assertion that would have caught the defect.** When
> a spec names a cardinality, implement the cardinality.

> **2. The tautological witness.** Three times in this milestone I wrote an
> assertion that cannot fail: D3's `skips_invalidation() == (kind == Shared)`
> (true by the method's definition), D4's `!capturing() || flag` (holds
> byte-identically with the flag branch deleted), and D12's
> `residual_conflicts.len() < usize::MAX` (vacuous). Each was written in good
> faith to "cover" a spec RED item, and each converted a coverage obligation
> into a coverage *claim*. The pattern is: reaching for an assertion about the
> code's own definition rather than about an independently-known answer. The
> counter is the standing rule above; D3's fix shows the shape — supply ground
> truth the test controls (`SelectiveMut`) and require the derivation to
> reproduce it.

---

## Closed

### D1 — `export.loans` accumulated across CEGAR rounds — **CLOSED**

*Was:* the oracle runs once per validation round, each under a different
candidacy predicate, and the recorder appended. `export.loans` held the union
over all rounds, so `surviving_loans()` mixed loans from rejected intermediate
models with the accepted one.

*Fix:* `export::begin_round()` clears `loans` and `residual_conflicts` at the
top of **both** round loops (`borrow_verify.rs` Mode-A and L2). What survives
the loop is exactly the accepted round's `BorrowSet`.

*Witnesses:* `loan_identity_covers_the_complete_borrow_set` (spec RED 14's
restored cardinality equality) and `multi_round_export_holds_only_the_final_
round`.

*Cycle-3 strengthening (closes the delta review's MEDIUM caveat).* The D1
witness now runs the `CASCADE` fixture and **pins the round count** —
`stats.rounds == 3`, `commits_per_round == [1, 1, 0]`, matching the independent
pin at `bo_c1.rs:6461` — and additionally asserts `model.is_some()` and
`!export.loans.is_empty()`. Duplicates can only arise across rounds, so without
the round pin a fixture that quietly collapsed to one round would have made the
uniqueness assertion inert; without the model/non-emptiness asserts, a
first-solve decline would have passed it with zero signal. The old `MULTI`
fixture was never verified to drive more than one round.

*Mutation-tested:* deleting `begin_round()` from the Mode-A loop fails it with
"loan (DefId(0:3), 0) appears more than once — rounds are accumulating", and
fails **only** it (21 of 22 export tests still pass).

*Useful correction from the earlier review:* candidacy is **not**
model-dependent (`is_candidate` reduces to `slot_for_local_depth(local, 0).
is_some()`, constant across rounds), so loan indices are stable and cross-round
entries collide exactly on `(fn_did, loan)` — which is what the cardinality
assertion keys on.

### D2 — the L2 path captured no loans — **CLOSED**

*Was:* `borrow_conflicts_replaying_witnessed` — the L2 oracle — had no capture
on either loop exit, so `loans` was silently empty under
`CRAT_BO_L2_GUARDED_COMMITS=1`, the plan-of-record configuration.

*Fix:* `record_loan_identities` wired on both witnessed exits, with the same
Gap-B reasoning (capture before the `invalid_loans.is_empty()` early break).
Capture now exists on all four replay exits across the two paths.

*Witness:* `l2_path_records_loans`.

*Cycle-3 strengthening (closes the delta review's "non-distinguishing"
caveat).* The witness previously reached L2 by mutating the env var, so nothing
guaranteed the L2 route was taken and every assertion it made also held on
Mode-A. It now routes **directly** into `verify_l2_to_fixpoint_counting`, so
the path is a fact of the call rather than of process state, and it asserts
`stats.l2_decline.is_none()` (accepted, not controlled-declined).

*Mutation-tested:* commenting out **only the two L2-half capture sites**
(`conflicts.rs:508` and `:534`), leaving the two Mode-A sites intact, fails
`l2_path_records_loans` and **nothing else** — 21 of 22 export tests still
pass. That is the distinguishing power the env-based helper lacked.

*Adjacent gap, still open (LOW):* the L2 accept path never records
**residuals** — `record_residuals` has exactly one call site, inside the
**Mode-A** `committed == 0` accept, and `verify_to_fixpoint_counting_with_
flows` routes unconditionally to the L2 function when L2 is on. Pre-existing,
not delta-caused; now stated in the field's own doc rather than only here.

### D3 — the R-Q1a witness was a tautology — **CLOSED**

*Was:* `loan_kind_matches_engine_skip` asserted `skips_invalidation() == (kind
== Shared)` — true by the method's definition, unable to fail if the derivation
drifted. The commit message's claim that the four R-Q1a witnesses included
"kind matches the engine's skip contract" was an overclaim and was withdrawn.

*Fix:* replaced with `loan_kind_matches_ground_truth_provider` and
`loan_kind_follows_the_provider_both_ways`. Ground truth is a `SelectiveMut`
provider the test supplies: the derivation must reproduce `is_mutable(fn_did,
borrowed.local)` for a known answer. This simultaneously witnesses the
**base-local keying** of R-Q1a §0.4 — a derivation keyed on the projected place
would look up a different local and disagree.

*Mutation-tested:* keying the derivation on `Local::from_u32(0)` fails **3 of
4** kind tests with precise diagnostics. Verified, then reverted.

### D4 — `CRAT_BO_EXPORT` was a dead switch — **CLOSED by descoping**

*Was:* the flag was parsed, validated, and tested — and consulted by nothing.
Cycle 2 wired it into `capturing()`, which left it **write-only**: the lazily
installed buffer had no reader, so `CRAT_BO_EXPORT=1` made capture run and then
discarded everything. The flag gated onto nothing.

*Cycle-3 decision: DESCOPE the env switch entirely* — the authorization's
second option, chosen over building the drain API. Justification:

1. **The flag's premise is false.** The module doc justified it as "a corpus
   worker needs to request capture without a Rust-level scope". Recon against
   the sweep refutes that: `bo_c1` re-invokes the test binary as a worker
   (`bo_c1.rs:7573`) whose entry point is `bo_c1::boc1_run_one` — Rust code,
   where `with_bo_export` is directly available. Every comparable in-tree
   feature works exactly that way (`CRAT_BOC1_SELECTOR_TRACE`,
   `CRAT_BOC1_SELECTOR_CORE`, `CRAT_BOC1_YIELD_SNAPSHOT`): the env var names a
   destination and worker Rust code drives the capture. There is no path that
   reaches the analysis without a Rust frame able to open a scope.
2. **Closing it "properly" meant machinery serving nobody.** A drain API plus —
   because the flag is resolve-once from process env and the suite is parallel
   — a test-only injectable-flag seam, all in production code, for a consumer
   that does not exist until the bo_c1 integration lands. At which point the
   integration would use `with_bo_export` anyway, per (1).
3. **It removes three defects at once:** D4, its secondary unbracketed-buffer
   growth (the flag path never bracketed the buffer, so `version_sites`,
   `source_sites` and `sink_sites` grew for the process lifetime), and the
   live hazard in D11.

Removed: `export_enabled_from_value`, `export_enabled_from_env`, the `FLAG`
`OnceLock`, `flag_enabled`, and the branch in `capturing()`, which is now one
thread-local read. Env gating arrives with the bo_c1 integration; the module
doc says so and explains why.

*Witness:* `export_off_records_nothing`'s first assertion, `!capturing()` with
no scope open — which is the **stronger** property (no ambient enablement of
any kind) and the reason no replacement test was added. Spec RED 1 is gone, not
weakened: there is no flag left to reject a bad value.

*Mutation-tested:* reintroducing ambient enablement in `capturing()` — an
unconditional lazy install, as if a flag had resolved on — fails it with
"capture must be inactive by default".

### D10 — `set_var` race in `capture_solve_l2` — **CLOSED**

*Was:* the L2 test helper mutated `CRAT_BO_L2_GUARDED_COMMITS` with `set_var`
inside a parallel test binary — the same data-race class cycle 2 had just fixed
for `CRAT_BO_EXPORT`, reintroduced one helper over. Its `SAFETY` comment
claimed the suite runs single-threaded; that was **wrong** — `test_threads = 1`
is a corpus-sweep setting, not a property of `cargo test -p pointer_replacer`.

*Fix: restructured, not serialized.* `verify_l2_to_fixpoint_counting` is now
`pub(crate)` and the helper routes into the L2 loop directly. No process state
is touched. The env switch remains the production entry, resolved once in
`verify_to_fixpoint_counting_with_flows`; the helper asserts the
`RepairMode::ModeA` precondition that entry asserts.

*Witness:* the D2 mutation test above — it is what proves the direct route
reaches the L2 loop, which is the whole point of the restructuring.

### D11 — `model_accepts_with_flows` had no round reset — **CLOSED**

*Was:* it calls the loan-recording oracle **outside** either CEGAR loop, so no
`begin_round()` preceded it. A probe issued inside an open capture scope would
append its loans to the fixpoint's and reopen D1 by another route.

*Fix:* `super::export::begin_round()` at the top of `model_accepts_with_flows`.
Semantics documented at the call site: the export then holds the last oracle
run's `BorrowSet` — here, the probe's — which is the same guarantee the loops
give.

*Witness:* `probe_after_fixpoint_does_not_accumulate_loans` — runs the fixpoint
and then the audit's `model_accepts` probe inside **one** capture scope, and
requires one record per loan. Note this defect was latent under the descoped
D4, but the witness makes it non-latent: the test constructs the scope itself.

*Mutation-tested:* deleting the `begin_round()` call fails it with "D11: loan
(DefId(0:3 ~ rust_out[96a3]::id), 0) recorded twice — the probe appended to the
fixpoint's loans instead of starting a fresh round", and fails only it.

### D12 — `certificate_residuals_may_be_nonempty` was vacuous — **CLOSED**

*Was:* the core assertion was `export.residual_conflicts.len() < usize::MAX`.
Same tautology class as D3, written by me in `ad79b01a`.

*Fix:* replaced with `certificate_holds_the_accepting_rounds_residuals`, which
runs the multi-round `CASCADE` fixture (rounds 1 and 2 carry committable
residuals, round 3 accepts) and asserts the certificate is **empty** — with the
derivation for why, and a diagnostic that names both ways the property could
break.

*Mutation-tested:* replacing the accept-point `record_residuals` call with a
fabricated non-empty residual fails it with the full diagnostic, and fails only
it. (Two earlier mutation attempts were ineffective — see the standing rule's
rider 1.)

---

## Open — recorded, not fixed

Outside the authorized fix scope; recommended for M0.1.

- **D13 (MEDIUM, new)** **The E-R4 certificate is content-free at a Mode-A
  accept, and the M0.5 spec says the opposite.** The spec, and the field's own
  doc before this cycle, asserted `residual_conflicts` is "non-empty in
  general" on the reasoning that acceptance is `committed == 0` (no residual
  was *committable*) rather than "no residuals". That reasoning is sound in
  principle and false in this implementation: every conflict reaching the
  commit stage has a committable `Ref` owner — a non-`Ref` FIELD residual
  declines (`residual_nonref_field`) and a non-`Ref` LOCAL residual trips a
  release-active assert (`guard_slots_are_ref`), both **before**
  `representative` runs, whose `None` arm is documented as defensive-only. So
  `committed == 0` currently implies the conflict set was empty. Discovered
  while replacing D12's tautology — the vacuous assertion had been hiding it.
  The field's doc is corrected in place; the **spec** still needs amending, and
  a consumer relying on E-R4 carrying a tolerated-conflict set needs to know it
  carries nothing today. The emptiness is a property of the current repair
  strategy, not of the export, which is why the field is retained and
  `certificate_holds_the_accepting_rounds_residuals` fires if it changes.
- **D5 (MEDIUM)** `BorrowerKind` drops both payloads the spec requires (the
  `Assign` `ProvenanceOwner`, the `CallArg` callee `LocalDefId`). §0.5's stated
  reason for exporting `BorrowerKind` — letting a consumer reproduce the
  access-dependent self-loan skip — is not met without the owner.
- **D6 (MEDIUM)** `VERSION_ASTS` is the one capture thread-local without an
  RAII guard: a nested `with_bo_export` wipes the outer snapshot; a panic
  leaves it set.
- **D7 (MEDIUM)** Spec fields still missing: `BorrowCertificate::ref_slots` /
  `raw_slots`, `SelectorSite::local`, and the in-analysis surviving/leaked
  selector partition (which makes spec RED 12 and the "surviving" half of RED
  11 unimplementable as written).
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
  contract is unperturbed; no signature changed. Cycle 3 changed one
  visibility (`verify_l2_to_fixpoint_counting`, `fn` → `pub(crate)`) and added
  one `begin_round()` call; no other production behaviour moved.

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
with a digest check standing guard:

```
find -L benchmarks/rs-crown -type f -name '*.rs' | sort | xargs shasum -a 256 | shasum -a 256
9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621
```

Re-verified at the end of fix cycle 3: **unchanged**. This check belongs in
every future verification list that uses the symlink; if it moves, the frozen
corpus was written through the link and comparability with CROWN's published
numbers is void.

**Machine scope.** Unit scope only throughout. No corpus-scale run; those
remain queued behind the pairwise-probing sweep, which owns the corpus machine.
`cargo build` / `cargo test -p pointer_replacer` at `-j 6` only.

**Tooling note.** The RTK hook summarizes `cargo test` output (and has
previously returned canned results for `diff`). Every test result in this
ledger was obtained through `rtk proxy cargo test …`, which bypasses the
filter, so pass/fail counts and panic messages are the real ones.
