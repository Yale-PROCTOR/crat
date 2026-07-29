# M0 defect ledger

Five adversarial review lenses ran against `f9ee8fee` (read-only). 38 raw
findings; nine re-verified and accepted. Four were HIGH and blocked merge.

## M1 subject universe — ruling and census (2026-07-29)

**M1's subjects are free functions with bodies** — the C2Rust output shape.
Impl/trait items and foreign items are out of scope **by ruling**: foreign items
have no body and an ABI-fixed signature (M4 territory), impl methods are not a
C-source shape.

The exclusions are **counted, not silent**. `decision::universe::classify`
walks every item kind from the crate's item list — a different source of truth
from the collector — and the coverage gate compares against it. That is what
makes the gate falsifiable: the two previous forms both compared the decision
table against the collector's own output, and the second only *looked*
independent because it re-walked `program.functions` with the same filter.

### Collector census on frozen rs-crown — **MEASURED** (2026-07-29)

Produced by the SHIPPING collector via a committed in-tree path. Invocation,
recorded beside the numbers as the discipline requires:

```
DYLD_LIBRARY_PATH="$(rustc --print sysroot)/lib" \
CRAT_BOC1_INPUT=benchmarks/rs-crown/<prog>/<lib.rs|c2rust-lib.rs> \
CRAT_BOC1_MODE=m1-census CRAT_BOC1_NAME=<prog> DIR=<worktree> \
  <test-bin> bo_c1::boc1_run_one --exact --ignored --nocapture
```

19 of 20 programs. **tulipindicators is resource-deferred** by the standing
benchmark-scope ruling (SLOC > brotli), so it is absent from these totals.

| quantity | count |
|---|---|
| subjects, resolved predicate (`ptr_chain_depth > 0`) | **3872** |
| of which the retired SYNTACTIC `TyKind::Ptr` predicate saw | 3737 |
| **resolved-only — invisible to the retired predicate** | **135** |
| …declared through a path (the C2Rust alias class) | 135 |
| …already a reference in source | 0 |
| …some other declaration form | 0 |

**The alias population is 135, concentrated in two programs** — lil 117,
brotli 18; every other program is 0. This is the delta §1.3 called an
obligation: it is the population that was collected, decided and attributed for
the first time this round, and that the syntactic collector dropped with no
`Decision`, no `Degradation`, no site and no reason.

The prior figure of **154** (lil 131, brotli 23) is **retired**: it came from a
balanced-paren text scan and over-counted by 19 (12%).

Corpus-neutrality note, since R-A widened the predicate's meaning: adopting
`ptr_chain_depth` brings already-reference parameters into the subject universe
(it counts `TyKind::Ref` as depth-bearing). On this corpus that widening is
**worth exactly zero** — `reference = 0` in all 19 programs. It is visible only
in fixtures with an `&self` receiver.

### CORRECTION 2026-07-29 — the `impl = 0` row is FALSIFIED

~~The `impl = 0 / trait = 0` rows stand as corroborated by direct grep (`0` impl
blocks in 290 `.rs` files under `benchmarks/rs-crown`).~~ **Struck, not erased.**

**The grep fact stands. The inference drawn from it is dead.**

- **Still true:** there are **0 source-written `impl` blocks** in 290 `.rs`
  files under `benchmarks/rs-crown`.
- **Dead:** the inference *text-zero ⇒ HIR-zero*. C2Rust emits
  `#[derive(Copy, Clone)]` on its structs; **derive-generated impls are
  macro-expanded into HIR**, where no text grep can reach them, and their
  `&self` receivers are pointer parameters under the R-A predicate —
  `ptr_chain_depth` counts `TyKind::Ref` as depth-bearing.

**Measured by the shipping `universe::classify` (Slice 0 spike, 2026-07-29).
PARTIAL — three programs only:**

| program | `impl_items` | `trait_items` | `foreign_items` |
|---|---|---|---|
| lil | **9** | 0 | 62 |
| binn | **3** | 0 | 19 |
| lodepng | **19** | 0 | 11 |

**Corpus-wide numbers are PENDING C.6's `classify` run** and are not stated
here. These three are partial measurements, not a corpus figure.

**Scope of the correction, so it is not over-read:** no real C pointer parameter
is excluded, so M1's impl/trait scope ruling still costs nothing *substantive*.
Wrong were **the number** and **the stated reason** — nothing else. What the
exclusion census counts on this corpus is largely **derive-generated
receivers**, a reporting artifact of the R-A predicate widening; it does not
measure excluded C pointer parameters, and must not be read as doing so.

Same root cause as the 892-checkpoint's seventh failure (`&self` is a pointer
parameter by the shared predicate's definition). That was recorded for fixtures;
its corpus-scale consequence went unmeasured because nothing had run `classify`
over the corpus until the Slice 0 spike.

**On the record:** the dead inference also passed the review gate uncontested —
a shared miss, carried on the reviewer's ledger as well as this one.

### Exclusion census — DISCHARGED at S2a-H/C.6 (2026-07-29)

The owed numbers, measured by the shipping `universe::classify` from the same
invocation as the reconciliation. **All 20 programs — tulipindicators did NOT
resource-defer** (150 s; the recon path is analysis-free, so the standing
deferral does not apply to it):

```
DYLD_LIBRARY_PATH="$(rustc --print sysroot)/lib" \
CRAT_BOC1_INPUT=benchmarks/rs-crown/<prog>/<lib.rs|c2rust-lib.rs> \
CRAT_BOC1_MODE=m1-recon CRAT_BOC1_NAME=<prog> \
CRAT_BOC1_ARTIFACT_DIR=<dir> DIR=<worktree> \
  <test-bin> bo_c1::boc1_run_one --exact --ignored --nocapture
```

| class | count (20 programs) |
|---|---|
| subjects (producer A rows) | **4306** |
| producer B rows | **4306** — identical |
| excluded: impl items | **522** |
| excluded: trait items | **0** |
| excluded: foreign (`extern` decls) | **2058** |

**The retired figure was 2039 foreign**; the measured value is **2058**. The
old scan was low by 19, and it also could not see the 522 impl-item receivers
at all.

**Read `excluded: impl = 522` correctly.** It is overwhelmingly
**derive-generated receivers** — `&self` on `Clone`/`Copy` impls that C2Rust
emits and that no text grep can see — not excluded C pointer parameters. The
corpus still has **0 source-written `impl` blocks**. This row measures what the
R-A predicate counts, and the predicate counts `TyKind::Ref`.

**Reconciliation result, same run: 20/20 PASS.** Zero violations, zero
findings, all three finding-class aggregates zero, and producer A's and
producer B's row counts identical on every program.

### Why the previous census was retired

**Why it was unverified.** These came from a scratchpad `syn` walk, not from the
shipping `universe::classify`. The walk applied the same syntactic
`*mut`/`*const` test as the classifier, so it **inherited the classifier's blind
spot** and could not have detected it — and the alias-typed population
(`pub type lil_value_t = *mut _lil_value_t`) is exactly what that blind spot
hides. A census that shares the classifier's blind spot cannot validate the
classifier. The script was also never committed, so the numbers are not
reproducible from the repository.

**Census discipline, now standing:** a recorded number comes from a committed,
in-tree code path, with its invocation recorded beside it. Scratchpad
reimplementations are banned as a source for ledger figures.

~~The `0 impl / 0 trait` rows survive as corroborated, because they rest on a
direct grep (`0` impl blocks in 290 `.rs` files under `benchmarks/rs-crown`)
rather than on a reimplementation.~~

~~**The impl/trait exclusion is stated-and-vacuous on this corpus** — zero across
all 20 programs — so the ruling costs nothing measurable here.~~

**Both struck 2026-07-29 — see the CORRECTION above.** `impl_items` is non-zero
(lil 9, binn 3, lodepng 19, partial); the exclusion is **not** vacuous, and the
grep could not have detected that because derive-generated impls never appear in
source text. `trait_items = 0` survives, measured rather than inferred.

A second lesson for the census discipline, since this row satisfied it and was
still wrong: *"a recorded number comes from a committed, in-tree code path"* is
necessary, not sufficient. **A number may not be inferred from a different
instrument than the one that will report it** — the grep measured source text
while the classifier measures HIR, and the gap between them is exactly where
macro expansion lives.

The foreign population is the M4 boundary and is correctly excluded; its count
is **owed**, to be discharged at C.6 from the same `classify` invocation with
the invocation recorded beside it. No interim scratch figure enters this ledger.

**Exclusions now reach a consumer.** They ride out on `RewriteOutcome`, which is
what makes the "visible as a number rather than as an absence" claim true of a
code path — it previously was not: the buckets were written and read by nothing
outside one test. `excluded_other` was **deleted, not fixed**: no `OwnerNode`
could increment it, so asserting it was zero passed vacuously — the same
unfailable-check class, sitting in the field documented as the blind-spot
detector. Blind-spot detection is now `coverage::reconcile`'s set comparison,
which can fail and is mutation-tested in all four directions.

### Proportionality call: `RAW_ONLY_METHODS` fixtures

The list is **data, not arms**. One `contains` check consumes every entry, so a
per-entry fixture would exercise `slice::contains` sixteen times without adding
coverage. One mechanism fixture over representative entries (`offset`,
`wrapping_add`) is the proportionate test; a new entry is a data edit whose real
risk is a wrong *name*, which a per-entry fixture would not catch either.
Recorded so the thin coverage is a decision rather than an oversight.

### ADV-R3 — dialect-scoped limitation

A1's fact collection sees only **syntactic operands**: one local copy of a
parameter (`let x = p; x == y`) defeats both `ptr_comparisons` and
`raw_only_uses`. On C2Rust input this is degradation-safe rather than silent,
because C2Rust annotates its locals (`let mut cur: *mut u8 = p;`) and the
annotation turns the alias into a type error. That is a property of the input
dialect, not of the guard. **Revisit only if the input dialect widens** beyond
C2Rust output.

## M1 open items with a ruled home

Recorded so a future reviewer does not re-file them, and so each has a slice
rather than sitting as an unowned "known weakness".

### F6, split by ruling (2026-07-29)

**(a) `emitted_count` has no non-zero witness — S2b.** `emitted_count` is the
field whose documented job is telling a real rewrite from a no-op, and today
`fn emitted_count(&self) -> usize { 0 }` passes the entire suite: the only
assertion on it is `== 0`, on a fixture with no pointer parameters. The fix is
cheap and lands in S2b — an emitting golden (g01) asserts its exact count, with
the deletion mutation being to hardcode `0`.

**(b) g09's companion strengthening — S3, deliberately not sooner.** g09's
input and expected are byte-identical and its fixture has **zero pointer
parameters**, so `emitted_count == 0` holds regardless of anything in
`decide_one`, and the mutation its own doc prescribes is ineffective. The
honest strengthening needs a *subject-bearing* suppression fixture, which
requires P-drop to exist. Strengthening it now would witness a mechanism that
has not been built — a witness for absent behaviour is the tautology class in
another costume, so it waits.

### Carried from the S2a delta, ruled into later slices

- **`CallSiteNotAdapted` saturation (S2b label, S3 fix).** ≥69.4% of rs-crown
  pointer parameters sit in functions with an in-crate call site, so every
  counter emitted before S3 is dominated by a reason with no analytic content.
  S2b's counter output carries the label "pre-S3 — measures S3's absence"; the
  M1-final report after S3 is the only data that feeds the
  emission-guided-refinement decision.
- **A1 models no borrowck precondition.** `tcx.analysis(())` includes
  borrowck, so the anonymous whole-crate gate failure remains reachable for
  that class. Not in A1's scope; the per-function gate in S2b bounds the blast
  radius to one function rather than the crate.
- **`plan`'s `continue` arms (F7) — S2b.** Two silent `continue`s drop an edit
  for a subject already decided `Ref`, producing no edit, no rollback and no
  record, while `emitted_count` still counts it as emitted.
- **Closures and impl/trait methods are not visited (F9).** C2Rust emits
  neither, so reachability against the target corpus is low; recorded rather
  than fixed.

## SUPPORTED SUITE MATRIX — read before filing a phantom finding

**The supported matrix is `CRAT_BO_MUT_FACTS` on/off** (plus unset = default).
All three are green: **841 passed, 0 failed, 7 ignored.**

**A suite-wide `CRAT_BO_L2_GUARDED_COMMITS=1` run is NOT a supported
configuration.** Under it, a set of `bo_c1` tests fails **by design**, not as
defects: Mode-A-only tests (`nb5l2_capture_is_mode_a_only`, `nb5l_*`) and the
feature-off golden (`l2_red_feature_off_matches_base_ae6f334`) each exclude the
global env they are being handed. Recorded here so they are never registered as
findings by a future reviewer or by a broad-sweep run.

*What the L2 profile IS good for:* targeted runs of the code under test. The
export suite is green under it — `cargo test … -- export::` → **30 passed** with
`CRAT_BO_L2_GUARDED_COMMITS=1` — and that targeted run is what surfaced the real
witness gap below.

*The gap it surfaced (fixed):* `probes_outside_the_armed_region_record_nothing`
asserted `residual_conflicts.is_some()` unconditionally, which is false under
L2 because the L2 accept never calls `record_residuals` (the documented
D2-adjacent gap). Now branches on `l2::enabled_from_env()` and asserts
`is_none()` explicitly on that path — the F3 pattern its two sibling
certificate tests already carried, which I had failed to apply to this witness
when I wrote it. The env-sensitivity is a tested property of both paths rather
than a failure blaming the accepted run.

---

## FINAL CYCLE + CORPUS GATES (2026-07-28)

**Both corpus-scale gates PASS, and the guardrail FIRED on a new HIGH.**

### R4 differential — ANCHOR-EXACT

Sorted vs unsorted Mode-A commit emission, all 20 rs-crown programs, two fresh
complete sweeps (`CRAT_BOC1_PROD=0`, dev machine, ~15 min each):

**Zero non-timing differences.** `rounds`, `commits_conflict`,
`commits_per_round`, `check_sat_count`, `n_ref`/`n_raw`/`n_own` (+ d0),
`sinks_leaked`, `sources_leaked`, `selectors` — identical program for program;
status `ok` on all 20 both sides. Timing columns excluded as non-semantic, and
that exclusion is stated rather than silent.

The measurement's risk basis held: **order varied, models did not.** The sort
ships. No previously reported row is byte-comparable to a post-sort row, but
that was already true — the pre-sort order was itself unstable across processes.

### Export-on/off identity — PASSES

`with_bo_export` has no non-test caller (D4 removed ambient enablement), so
"export-on" was produced by **temporarily** reinstating the ambient path in
`capturing()` — three lines, uncommitted, reverted after the run — rather than
wrapping the sweep's solve region, which is large and full of early returns.
That makes every capture point genuinely record at corpus scale.

**Zero non-timing differences** vs the capture-off baseline across all 20
programs; all `ok`; no OOM and no timeout despite the ambient path never
bracketing its buffers. Recording-only holds at corpus scale.

### Guardrail: TRIGGERED (second time)

**ADV-1 (HIGH, confirmed by reading source):** §2's "all four corrupting probe
surfaces" is **false**. `solve_with_demotion` does a full `KindSolver::new` →
`emit_crate_ownership_constraints` → `add_coherence` →
`verify_to_fixpoint_with_flows`, and is reached from `measure_collateral`
(`CRAT_BOC1_COLLATERAL=1`) **43 lines above** the `CHECK_REAL` block that WAS
wrapped — plus a sixth surface via `explain_unsat`. Latent (capture has no
non-test caller), but it is the claim M1 would build on.

**Why my enumeration missed it:** I searched for solver constructions *in the
probe region*; `solve_with_demotion` builds its solver inside a helper, so it
was invisible to that search. This is the **second** enumeration-completeness
HIGH in two cycles (F1 was the first) — the pattern the guardrail exists to
catch. NOT patched. The remedy is structural, not another wrapper: a greppable
assertion that every `KindSolver::new*` reachable from `boc1_run_one` other
than the reported one is suspension-wrapped.

### Record corrections made (docs-only, not a fix cycle)

- **ADV-2:** the mutation recipe recorded for
  `loan_keys_are_stable_across_reinference` ("compare `run_local_handle` sets")
  is **weaker than the mutation actually run** and would not fail — handles are
  `0..n_f-1` per function in both runs, so bare-handle sets are equal by
  construction. The 8/8 measurement is real; it used
  `(fn_did, run_local_handle, place.local)` triples. Corrected in place, with
  the remaining gap recorded: nothing asserts a permutation *occurred*, so the
  witness dies silently if `union_find` ever becomes deterministic.
- **ADV-3:** the non-vacuity proxy (>1 loan per site) is satisfiable by a
  two-pointer-argument call, which is deterministic and has no `group()`
  involvement. Recorded as an accepted limitation at the assertion.

### Open from this cycle's verification (NOT fixed)

- **ADV-1 (HIGH)** — above.
- **ADV-4 (MEDIUM)** — the F4 decline witness is vacuous under
  `CRAT_BO_L2_GUARDED_COMMITS=1` (the L2 loop never records residuals, so
  `is_none()` holds for an unrelated reason) and carries no liveness marker on
  the Mode-A arm. Its two sibling certificate tests already branch on the
  profile; this one does not.
- **ADV-5 (LOW)** — `loans` and the certificate are emitted in the very
  iteration order §3 declared unstable, while the new derived `PartialEq`
  compares those `Vec`s order-sensitively. Forward-looking only.
- **ADV-6 (LOW)** — the handle guard covers a 177-line skeleton and only that
  directory, while the field is `pub` on a `pub(crate)` struct.
- Testing gaps recorded: no test exercises any of the bo_c1 suspension sites
  (deleting any of the four wrappers leaves the suite green — which is why
  ADV-1 was undetectable by test); nothing pins Mode-A's emission order.

### Confirmed clean by this verification

`PlaceKey::from_place` is total **and compiler-enforced** (no wildcard arm);
`LoanKey`'s manual `Ord` is consistent with its derived `Eq`;
`OwnerKey::from_owner` is lossless; the four closure wrappings preserved `?`,
`pop_scope` and borrow semantics; §3's tie argument is rigorous
(`conflict_sort_key` is injective over exactly what `representative` reads);
the necessity audit's over-pin numbers are unaffected; recording-only holds.

---

**Status after fix cycle 4: D1–D4, D10–D12, D14, D16, D17, D18 CLOSED, every
witness mutation-tested in Rider 0 order. D13 RETRACTED. D5–D9 and D15 remain
open. One NEW HIGH — D19 — was found during implementation.**

> ## CONVERGENCE GUARDRAIL: TRIGGERED
>
> Cycle 4's success condition was "close the listed items with zero new HIGH
> findings". **D19 is a new HIGH**, so per the standing instruction cycle 5 is
> NOT opened; this stops for a design review of the recorder architecture.
>
> D19 is not a defect in the recorder's code — the recorder is faithful. It is
> a defect in the recorder's **premise**: E-R4 exists to give a rewriter a
> stable per-loan identity, and `LoanIdentity.loan` is not stable across runs.
> That is an architecture question (what is a loan's identity?), not something
> another patch cycle should answer, which is exactly the condition the
> guardrail describes.

Cycle-3 delta verification: 7 findings, **all 7 confirmed** — 2 by running the
mutation, 5 by direct source reading. None refuted. Cycle 4 later **partly
refuted one of them** (D17's premise) by running its deletion mutation.

Suite after cycle 4: **834 passed, 0 failed, 7 ignored.**

> **The standing rule was violated one commit after it was written.** The rule
> says: *delete or break the exact branch the witness claims to guard*. For
> D12 I mutated the recorded **content** (a fabricated residual) instead of
> **deleting the call**, and reported the witness closed. Deleting
> `record_residuals` outright leaves all 833 tests green. Running the wrong
> mutation is the same failure as not running one — a content mutation
> witnesses content, and the obligation was existence. **Rider 4: run the
> deletion mutation first; only then consider weaker perturbations.**

---

## STANDING RULE — witnesses must be mutation-tested

**Every witness test must be mutation-tested before it counts: delete or break
the exact branch or derivation it claims to guard, and demonstrate that the
test fails. A witness that cannot fail is not a witness.**

This carries to all future milestones, not just M0. It is the systematic
counter to M0's recorded failure classes below.

Four operational riders, riders 1-3 learned in cycle 3 and rider 0 the hard
way — by violating the rule one commit after writing it:

0. **Run the DELETION mutation first.** "Delete **or** break" are not
   equivalent, and deletion is the stronger test. For D12 I broke the recorded
   *content* and declared the witness closed; deleting the recorder outright
   leaves the whole suite green. A content mutation witnesses content — if the
   obligation is "this code runs at all", only deletion tests it. Weaker
   perturbations come after, never instead.
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
3. **A good mutation fails its witness and nothing else.** Each of cycle 3's
   effective mutations failed exactly one of the 22 export tests. That
   one-to-one property is itself the evidence the witness is *distinguishing*
   — it is what closed the D2 caveat, where the prior test asserted only
   properties that also held on the path it was not testing.

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
the path is a fact of the call rather than of process state. (The added
`stats.l2_decline.is_none()` assertion was **also** claimed as strengthening;
that claim is withdrawn — it cannot fire, see D18a. The direct routing is the
whole of the strengthening.)

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

### D12 — `certificate_residuals_may_be_nonempty` was vacuous — **CLOSED in cycle 4**

Closed by the `Option` change described under D14: the obligation was "the
certificate is recorded", and it was unwitnessable while "recorded empty" and
"never recorded" were the same value. The cycle-3 history below is kept because
the *reason* it stayed open for two cycles is the more useful record.



*Was:* the core assertion was `export.residual_conflicts.len() < usize::MAX`.
Same tautology class as D3, written by me in `ad79b01a`.

*Attempted fix:* replaced with `certificate_holds_the_accepting_rounds_
residuals`, which runs the multi-round `CASCADE` fixture and asserts the
certificate is **empty**.

*Why it does not close.* `record_residuals` (`borrow_verify.rs:806`) is the
field's **only** writer, and `BoExport` derives `Default`, so with the call
deleted the field is empty and `is_empty()` still holds. **Verified by running
it: the entire suite stays green — 833 passed, 0 failed — with
`record_residuals` removed.** The only other consumer,
`certificate_candidacy_matches_model`, is a loop over the same collection and
is likewise vacuous when empty. So D12's actual obligation — *the certificate
is recorded at the accept point* — remains unwitnessed, and the test's own
failure message ("either `record_residuals` moved off the accept point …")
names a mutation it cannot detect.

The mutation I did run (fabricating a non-empty residual) fails the test, so it
is not a tautology in D3's sense — it is falsifiable but guards the wrong
thing. Closing it needs a shape that distinguishes "recorded empty" from "never
recorded": an `Option<Vec<_>>`, or a recorded round index, or a fixture that
genuinely yields a residual at accept (see D13).

Two earlier mutation attempts in this cycle were also ineffective for
mechanical reasons — see the standing rule's rider 1.

### D13 — "the certificate is always empty at a Mode-A accept" — **RETRACTED**

Recorded in cycle 3 as a new finding. **The derivation is invalid and the
claim is withdrawn.**

*What I argued:* every conflict reaching the commit stage has a committable
`Ref` owner, because a non-`Ref` FIELD residual declines
(`residual_nonref_field`) and a non-`Ref` LOCAL residual trips
`guard_slots_are_ref`; therefore `committed == 0` implies an empty conflict
set.

*Why it fails.* **Both guards are vacuous on an edge with no owners at all.**
`residual_nonref_field` is a `.find()` over `issuer.into_iter().chain(
requirers)` — `None` on an empty iterator, so no decline. `guard_slots_are_ref`
is an `.all()` over the same iterator — `true` on an empty iterator, so no
trip. Neither guard intercepts such an edge; both wave it through,
`representative` returns `None`, and it contributes 0 to `committed`. The
conclusion does not follow from the premises.

*And owner-less edges are producible by construction.* A `Borrower::CallArg`
loan takes the `Borrower::CallArg(..) => None` arm for its issuer in
`extract_conflict_edges`, and `origin_replay.rs`'s membership loop opens with
`let Borrower::Assign(owner) = data.assigned else { continue; }` — so a CallArg
loan never acquires a membership constraint, no provenance can ever `require`
it, and the requirer walk (gated on `requires.contains(provenance, loan)`) can
never fire. Its edge is necessarily `{ issuer: None, requirers: [] }`.
`map_edges_to_slots` `.map()`s rather than filters, so it survives into the
conflict set intact. All four steps re-read and confirmed in source.

*I also misquoted my own authority.* I cited `representative`'s doc as saying
the `None` arm is "defensive-only". It reads: "The `None` arm is kept defensive
**(e.g. an empty edge)**" — the clause I dropped names the exact
counterexample. Corroborating: the L2 loop's `representative == None` arm is
written to `continue`, which would be dead code if the claim held.

*What is actually established:* the certificate is empty on every fixture
measured, and **not proven empty in general**. Whether an owner-less edge can
survive to an *accepting* round is open — no fixture exhibits one, and
constructing one is now the concrete task (D15). The field doc is corrected to
say exactly this; the spec deviation note is corrected likewise.

---

## Open — recorded, not fixed

Outside the authorized fix scope; recommended for M0.1.

### REVIEWER ERRATUM (recorded as the reviewer's, at their instruction)

> The cycle-3 prescription for D11 — give `model_accepts_with_flows` "the same
> per-round reset discipline" as the CEGAR loops — **was the wrong contract for
> a probe path.** A reset converts a loud defect into a silent one, exactly as
> the delta verification argued in D16. The correct contract is **suspension**:
> the export represents the accepted CEGAR run only, and capture is inactive
> during probe entry points.
>
> This erratum is the reviewer's, not the implementer's. Recorded here at their
> instruction, and implemented in cycle 4 as D16.

Worth keeping alongside it: cycle 3 implemented the prescription as given
rather than raising the objection, even though the concern was visible at
implementation time. Both the erratum and the silent compliance are on the
record.

### From the cycle-3 delta verification (all confirmed)

- **D14 (HIGH) — CLOSED in cycle 4.** The E-R4 certificate had no recording
  witness: deleting `record_residuals` left the suite green.

  *Fix:* `residual_conflicts` is now `Option<Vec<ResidualConflict>>`. `None`
  means the accept point never ran; `Some(vec![])` means it ran and tolerated
  nothing. **That type change is the whole fix** — as a bare `Vec` the default
  value and the recorded value were the same value, so no assertion could
  distinguish them, and every attempt to witness "it was recorded" was doomed
  before it was written. `begin_round()` resets to `None`, not to an empty vec.

  *Witness:* `certificate_is_recorded_at_the_accept_point`, asserting
  `is_some()`. **Mutation-tested, deletion first (Rider 0):** removing the
  `record_residuals` call fails it with the D14 message — the same mutation
  that previously left all 833 tests green.

  *What was NOT achieved.* The authorization asked for the witness to be built
  on a fixture producing an owner-less edge that survives to a Mode-A accept
  with a non-empty residual set. **No such fixture was found**, so the content
  assertion is emptiness, not non-emptiness. See D15 — the search is recorded
  there rather than being quietly dropped.
- **D15 (MEDIUM, open — searched, not found)** No fixture constructs an
  owner-less residual edge, the shape that would decide D13 either way.

  *Cycle-4 search, recorded so the next attempt does not repeat it.* 14 shapes
  probed (write-after-call, aliased two-arg, call-then-call, struct field
  aliasing, nested fields, array locals, cast chains, read-only callees).
  **Zero produced an invalid `CallArg` loan**, at any round.

  *Why, from source.* A `CallArg` loan gets no membership constraint, so no
  provenance `requires` it; `LoanLiveAt::apply_location_effect` begins with
  `state.intersect(&required)`, which therefore drops it at the very next
  location. Combined with `seek_before_primary_effect`, the loan is live at
  **exactly one point** — the location following its call. To be invalid it
  needs an invalidating access at that one location, which source-level
  fixtures cannot reliably place (MIR bookkeeping intervenes). The self-loan
  skip is NOT the blocker: it matches only `Borrower::Assign(Local(l))`, so
  `CallArg` loans are not skipped. `local_map` includes every loan, so that is
  not the blocker either. Both were checked and ruled out.

  *Status:* the D13-retraction mechanism (guards are vacuous on an owner-less
  edge) still stands as source-level fact. Its **reachability** is unresolved,
  and neither "reachable" nor "unreachable" is claimed. The remaining untried
  route is an `Assign` loan whose owners all fail `owner_to_slot` (a Local or
  Field with no depth-0 slot).

  Related and still uncovered: `representative`'s `None` arm on either loop.
- **D16 (MEDIUM) — CLOSED in cycle 4** by replacing the reset with
  **suspension**, per the reviewer's erratum above. `model_accepts_with_flows`
  now wraps its oracle call in `export::with_capture_suspended`, so a probe
  neither appends to the recording nor resets it, and the export continues to
  describe the accepted run.

  *Witness:* `probe_after_accept_leaves_the_export_unchanged`. It snapshots the
  export before and after a **counterfactual** probe (every slot forced `Ref`,
  mirroring the necessity audit's leave-one-out direction) — a probe on the
  accepted model would re-record identical loans and hide the difference.

  *Single-run by construction, and that detail is load-bearing.* The first
  draft compared two separate compiler runs and failed — not because the probe
  changed anything, but because of D19. Snapshotting inside one run removes
  that variable while keeping the comparison **order-sensitive**; sorting or
  set-comparison would have accommodated D19 by weakening the assertion, which
  is the RED-weakening trap wearing a different hat.

  *Mutation-tested, both directions:* deleting `with_capture_suspended` fails
  it, and **restoring cycle 3's `begin_round()` in its place fails it too** —
  the erratum made executable.

  The original finding, for the record: `run_necessity_audit` calls `model_accepts_with_flows`
  on the anchor model and then once per leave-one-out **counterfactual** model
  (`probe_accepts_with_ref`). Each now clears and re-records, so after such a
  run `export.loans` describes the last counterfactual — a model that was
  never accepted — and `surviving_loans()` would hand a rewriter loans from
  the wrong model. `residual_conflicts` is wiped by the first probe and never
  re-recorded. `begin_round()`'s own doc ("leaves exactly the accepted round's
  `BorrowSet` behind") is false in the presence of any post-loop probe.
  **Latent, not live** — `with_bo_export` has no non-test caller and `mod
  bo_c1` is `#[cfg(test)]`, so `capturing()` is false on every audit path
  today. Severity direction matters: before the fix this scenario produced
  *duplicate* loans, which the uniqueness assertions catch loudly; after it,
  the corruption is a unique, plausible loan set from the wrong model —
  silent. The reviewer's alternative is better than what I shipped:
  **suspend** capture for the duration of a probe rather than reset it, since
  a probe is not the analysis. That preserves the fixpoint's E-R4 data and
  still prevents D1-style accumulation. I did not make that change: the
  authorization specified "the same per-round reset discipline as the CEGAR
  loops", and switching to suspension is a contract change, not a fix.
- **D17 (LOW) — CLOSED in cycle 4, with the finding itself partly REFUTED.**

  *The finding said:* the new `pub(crate)` door bypasses the release-active
  tracked-solver guard, and my doc named only the inert precondition
  (`RepairMode`, which the L2 loop hardcodes and never re-reads — that part is
  correct).

  *What checking it showed:* **the hazard was never unguarded.**
  `KindSolver::check`, `model_kinds`, and `model_kinds_relaxing` each carry
  their own release-active guard with the same message prefix, and the loop
  cannot extract a model without passing one. So the door bypasses a
  *wrapper-level* tripwire, not the protection.

  *How that surfaced — Rider 1 earning its place.* My first witness was
  `should_panic(expected = "tracked KindSolver must not enter")`, and the
  deletion mutation **did not fail it**: the panic came from
  `model_kinds_relaxing`'s own guard, whose message shares that prefix. Had I
  not run the deletion mutation, I would have shipped a false witness AND kept
  the false claim. The `expected` string is now door-specific, and the deletion
  mutation fails the test.

  *Shipped:* a `debug_assert!` at the door, documented for what it is — a
  fail-earlier tripwire naming the door, not the thing preventing a meaningless
  model. `debug_assert!` rather than `assert!` so release behaviour at the
  existing choke points is untouched.
- **D18 (LOW) — CLOSED in cycle 4.**
  (a) The cannot-fire `stats.l2_decline.is_none()` assertion is **removed**
  rather than left as decoration.
  (b) The "well-formedness" loop is **deleted, not repaired**. It was shadowed
  (it iterated a collection the preceding assert had just required to be
  empty), and repairing the shadowing would have made it worse: an owner-less
  residual is not malformed, it is precisely the shape D15 hunts, so on the one
  day it could have run it would have reported the wrong diagnosis. A missing
  check is honest; a check that misclassifies what it fires on is not.
  (c) `export_off_records_nothing`'s doc no longer claims to show capture
  "allocates nothing when off" — the body asserts only `!capturing()` and that
  recording is a no-op. The zero-allocation property rests on `record`'s early
  return, which is an argument, not a measurement.

### From the cycle-4 delta verification

6 findings. **F3 and the D19 mechanism were confirmed by running or reading
them myself; the rest are accepted on the reviewer's evidence.** F3 and F2 were
regressions in cycle 4's own deliverable and are FIXED here — a test that fails
in a supported configuration is an incomplete D14, not a new work item. The
rest are recorded for the design review.

- **F3 (MEDIUM) — FIXED.** My `Option` change made the certificate tests fail
  under `CRAT_BO_L2_GUARDED_COMMITS=1`, the plan-of-record profile, where they
  had passed. `verify_to_fixpoint*` dispatches on that env var and the L2
  accept never calls `record_residuals` — so `None` there is **correct**, and
  the test blamed the accept point for it. **Verified by running:** 3 failures
  under that profile before the fix, 23/23 after. The tests now assert what
  each path actually does, converting an env-sensitivity that was invisible
  under `Vec` into a tested property of both paths. The D14 deletion mutation
  was re-run afterwards to confirm the added early return did not make the
  witness inert — it still fails.
- **F2 (MEDIUM) — FIXED.** `l2_door_rejects_a_tracked_solver` would fail under
  `cargo test --release`: `debug_assert!` is compiled out, the panic then comes
  from `model_kinds_relaxing`'s release-active guard with a different message,
  and `should_panic(expected = …)` no longer matches. Now
  `#[cfg(debug_assertions)]`. The corollary is worth stating plainly: in the
  release binaries the sweep actually runs, the door assert does not exist at
  all — D17 buys no release protection, consistent with it being a fail-earlier
  tripwire rather than the guard.
- **F1 (MEDIUM; HIGH once the bo_c1 integration lands) — OPEN.** D16's
  suspension sits inside `model_accepts_with_flows`, but the real probe
  (`bo_c1::probe_accepts_with_ref`) extracts a model **before** calling it, and
  `build_probe_base` re-runs `emit_crate_ownership_constraints` in the same
  scope. So `version_owns` would be overwritten with the counterfactual's
  ownership and `source_sites`/`sink_sites`/`version_sites` doubled — breaking
  `SelectorSite`'s documented index-alignment. Loans and certificate are
  protected; **E-R2 and E-R3 are not.** The suspension belongs at the probe
  boundary, not inside the oracle adapter. Latent today, but D16's own hazard
  was equally latent and was fixed anyway, and my doc claimed to cover
  "anything else that runs the oracle on a model the loop did not accept" — it
  does not. Same family: a second `verify_to_fixpoint` in one scope
  (`CRAT_BOC1_CHECK_REAL=1`) wipes the first run's certificate via
  `begin_round()`.
- **F4 (MEDIUM) — OPEN.** D14's witness detects **deletion** but not
  **relocation**, and its docstring claims round-distinguishing power it does
  not have: `begin_round()` resets the field every round, so the terminal value
  depends only on the last round and "record every round" is indistinguishable
  from "record at accept" *for this field* — the pinned `rounds == 3` /
  `commits_per_round == [1,1,0]` buy nothing here. The semantically dangerous
  relocation is the same one: recording above the `residual_nonref_field`
  decline would leave a **declining** run holding `Some(...)`, destroying the
  very invariant the `Option` exists to carry. **Nothing asserts `is_none()` on
  a declining run.**
- **F5 (LOW) — OPEN.** The D16 witness calls itself "byte-identical" but
  compares 3 of 6 fields (`version_sites` by `.len()`, and not
  `source_sites` / `sink_sites` / `version_owns` — exactly the fields F1
  corrupts), and never pins its counterfactual as genuinely differing from the
  accepted model. Not vacuous today, but the guarantee its doc names is held up
  by sibling tests rather than by itself.

### New in cycle 4

- **D19 (HIGH, open — pre-existing, production-side) — loan numbering is not
  stable across runs.** Identical source, identical binary, same process: some
  runs record loan 2 → `_2` and loan 3 → `_3`, others the reverse. Observed
  directly, four consecutive runs of one fixture (runs 0–1 one order, runs 2–3
  the other).

  *Not an export defect.* `record_loan_identities` iterates
  `borrow_set.loans.iter_enumerated()` — an `IndexVec`, iterated by index, so
  the recorder is faithful to whatever numbering it is given.

  *Root cause, located by the cycle-4 review and confirmed here:*
  `utils/dsa/union_find.rs` opens with `use std::collections::HashSet` — the
  **default `RandomState`** hasher (verified: no `rustc_hash`/`FxHash` import in
  that file). `UnionFind::group()` returns a clone of one of those sets, and
  `analyses/borrow/mod.rs` pushes sibling loans into the `IndexVec<Loan,
  BorrowData>` **in `group()` iteration order**. `RandomState` is seeded per
  process and bumped per instance, so the order varies both run to run and
  between `UnionFind` instances.

  *Worse than first recorded, in two ways.* (1) `NativeBorrowContext::new`
  rebuilds each function's `ProvenanceSet` — and therefore a fresh `UnionFind`
  — on **every CEGAR round**, so loan numbering can permute *within a single
  run*, not only across runs. That falsifies `snapshot()`'s justifying doc
  ("within a single run the order is fixed"); the D16 witness is still sound,
  but for a different reason — with suspension active, nothing is recorded
  between the two snapshots. (2) `extract_conflict_edges` walks
  `invalid_loans.iter()` in loan-index order, so the per-function
  `Vec<ConflictEdge>` follows the permuted numbering and **Mode-A issues
  `add_borrow_exclusion` in that order**. The comment there — "Iteration order
  left on FxHash — Mode-A's z3 assertion order (hence its corpus numbers) stays
  byte-comparable to every prior row" — rests on a false premise: `FxHashMap`
  order is deterministic, but the inner `Vec` order is not. (The Lemmas arm
  sorts explicitly for exactly this reason; Mode-A deliberately does not.)
  Whether a permuted assertion order actually moves an accepted model is
  **unmeasured exposure**, not demonstrated divergence — z3 `Optimize`
  tie-breaking makes it possible.

  *Why HIGH.* E-R4's purpose, per ruling Q11, is a stable per-loan identity a
  re-route can match against. `LoanIdentity.loan` is a `usize` index into that
  numbering, so **it is not a valid cross-run key** — which is the property the
  export was built to provide. `surviving_loans()` hands a consumer indices
  that mean different loans on different runs.

  *Blast radius* is therefore not confined to the export: the Mode-A z3
  assertion-order claim above is the load-bearing one, and it should be
  measured before any corpus number is cited as byte-comparable.

  *Discovered* by D16's first draft, which compared two runs and failed for
  this reason rather than the one it was testing. The failure was investigated
  rather than accommodated — sorting the comparison would have hidden it.

### Carried from earlier cycles

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

**RTK hook — observation distortion (STANDING, 2026-07-28).** The hook
filters and sometimes fabricates command output. Two confirmed incidents, now
three:

1. A canned `[ok] Files are identical` returned for `diff` on files that
   **differ** — first seen re-verifying golden pairs (caught by SHA-256), and
   seen AGAIN in M1/S1 on `g01`/`g03`/`g10`, where it contradicted a hash check
   performed moments earlier.
2. `cargo test` summary counts differ from raw: the M0 merge report published
   "848 passed, 7 ignored" from the filtered summary; raw is **854/0/9**.

**Rules, binding on all future reports:** cite RAW `cargo test` output only
(`rtk proxy cargo test …`), never the filtered summary; never use `diff` to
establish file equality — hash, or compare in a language runtime. Two
observation-distortion incidents from one hook is a pattern, not bad luck: a
tool that answers questions it was not asked will eventually answer one that
matters.

**Machine scope.** Unit scope only throughout. No corpus-scale run; those
remain queued behind the pairwise-probing sweep, which owns the corpus machine.
`cargo build` / `cargo test -p pointer_replacer` at `-j 6` only.

**Tooling note.** The RTK hook summarizes `cargo test` output (and has
previously returned canned results for `diff`). Every test result in this
ledger was obtained through `rtk proxy cargo test …`, which bypasses the
filter, so pass/fail counts and panic messages are the real ones.
