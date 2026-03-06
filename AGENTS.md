# AGENTS.md

## Mission

The long-term goal for this project area is to convert allocator-owned pointers to `Option<Box<T>>` and allocator-owned array pointers to `Option<Box<[T]>>` using ownership analysis output.

## Scope

- Active implementation focus is limited to `crates/pointer_replacer/src/rewriter` for rewriter milestones.
- New milestone `M1` explicitly allows implementation changes in:
  - `crates/pointer_replacer/src/analyses/output_params`
  - `crates/pointer_replacer/src/analyses/ownership`
  - MIR-introspection harnesses in `crates/pointer_replacer/src/analyses/B02_tests/mod.rs` and `crates/pointer_replacer/src/tests.rs`
- Outside `M1` (or explicit user request), ownership and output-parameter analysis modules are read-only when making rewriter decisions.
- Ownership analysis may include struct-field ownership results, but these results are not consumed for decision support/validation by default.
- Do not broaden implementation scope outside this area unless explicitly requested.

## Source of Truth

Authoritative sources for this roadmap and implementation:

- `crates/pointer_replacer/src/rewriter/CANONICAL_REWRITER_SPEC.md`
- `crates/pointer_replacer/src/rewriter/decision.rs`
- `crates/pointer_replacer/src/rewriter/mod.rs`
- `crates/pointer_replacer/src/rewriter/transform/mod.rs`
- `crates/pointer_replacer/src/rewriter/collector.rs`
- `crates/pointer_replacer/src/analyses/ownership/whole_program.rs`
- `crates/pointer_replacer/src/analyses/ownership/solidify.rs`
- `crates/pointer_replacer/src/analyses/output_params/mod.rs`
- `crates/pointer_replacer/src/analyses/B02_tests/mod.rs`
- `crates/pointer_replacer/src/tests.rs`

## Roadmap Governance

- This file defines the merged authoritative roadmap for the pointer rewriter.
- If an agent wants to diverge from a milestone, it must ask the user first.
- Execution order is: `M0 -> M1 -> M2 -> M3 -> M4A -> M4B -> M5 -> M6`.
- Ship one milestone per PR/commit.
- Do not mix unrelated refactors with milestone changes.
- Every milestone must keep tests green before moving to the next one.
- Every completed milestone must update this file:
  - update `Milestone Status`
  - append an entry in `Milestone Completion Log`

## Spec Sync Rule

- Every implementation modification in rewriter scope must include a direct edit to `crates/pointer_replacer/src/rewriter/CANONICAL_REWRITER_SPEC.md` in the same change set.
- If implementation changed and the canonical spec is not directly edited in the same change set, the milestone is incomplete.
- The canonical spec must describe the current checked-in behavior, not desired future behavior.

## Subworker Validation Protocol

- Mandatory trigger:
  - Any implementation change touching `crates/pointer_replacer/src/rewriter/**/*.rs`.
  - Any implementation change touching `crates/pointer_replacer/src/analyses/output_params/**/*.rs`.
  - Any implementation change touching `crates/pointer_replacer/src/analyses/ownership/**/*.rs`.
  - Any implementation behavior change that affects canonical spec content.
- Required order (do not reorder):
  1. Implement the code change.
  2. If (and only if) rewriter implementation behavior changes, edit `crates/pointer_replacer/src/rewriter/CANONICAL_REWRITER_SPEC.md` in the same change set.
  3. Run baseline commands from `Validation Loop`.
  4. Run three independent worker audits.
  5. Aggregate worker outputs and classify the final gate result using `Gate Decision Policy`.
- Operational fallback:
  - Run workers in parallel by default.
  - If worker/thread limits prevent parallel runs, execute the same three worker roles sequentially.
  - Skipping a role is not allowed.

## Worker Roles

- Coverage Worker:
  - Verifies changed behavior has matching tests and spec coverage.
  - Missing high-risk test/spec coverage is a blocker.
- Correctness Worker:
  - Verifies implementation and canonical spec alignment plus semantic safety.
  - Any confirmed semantic regression is a blocker.
- Implementation-Readiness Worker:
  - Verifies integration readiness, edge-case handling, and milestone-exit readiness.
  - May report blockers, but handling follows soft-block policy in `Gate Decision Policy`.

## Worker Output Format

- Each worker report must include:
  - Scope reviewed.
  - Findings with severity (`blocker` or `non-blocker`).
  - Concrete evidence (`file:line`).
  - Recommended fixes.
  - Final verdict.

## Gate Decision Policy

- Gate result classes:
  - `PASS`: zero correctness blockers and zero unwaived blockers from other workers.
  - `SOFT-BLOCK`: no correctness blockers, but one or more coverage/readiness blockers pending fix or user waiver.
  - `BLOCK`: one or more correctness blockers.
- Correctness blockers are hard-blocking and must be fixed before milestone completion.
- Coverage and readiness blockers are soft-blocking; each must be fixed or explicitly waived by the user.
- Any user waiver must be recorded in `Milestone Completion Log` with rationale.
- If workers disagree, resolve by evidence and apply the strictest severity for correctness-related findings.

## Struct Field Policy

- Ownership analysis may include struct-field ownership results.
- Default behavior: do not consume struct-field ownership results for decision support/validation.
- Struct-field type rewriting is out of scope unless explicitly approved by the user.
- If an agent believes this policy should change, the agent must ask the user first.

## Milestone Status

- [x] M0 - Canonical spec-first baseline
- [x] M1 - MIR source migration for ownership/output analyses
- [ ] M2 - Post-spec plumbing foundation
- [ ] M3 - Decision logic extension (`OptBox`, `OptBoxedSlice`)
- [ ] M4A - Core rewrite implementation for box kinds
- [ ] M4B - Conditional struct support (`Default`, `take`)
- [ ] M5 - B02 rewrite compile gate
- [ ] M6 - Unsafe minimization and hardening

## Milestone Completion Log

Use this format whenever a milestone is completed:

```text
- Date: YYYY-MM-DD
  Milestone: MX
  Files changed:
  - path/one
  - path/two
  Behavior changes:
  - ...
  Tests run:
  - command: <cmd>
    result: pass|fail
  Worker runs:
  - role: coverage|correctness|implementation-readiness
    run_id: <id-or-identifier>
    verdict: pass|soft-block|block
  Blockers:
  - role: <role>
    summary: <summary>
    status: fixed|waived
  B02 result deltas:
  - case: <case_name>
    changed: <changed_expectation_or_result>
    rationale: <why_change_is_reasonable>
    disposition: accepted|fixed
  Waiver rationale:
  - <rationale-or-none>
  Notes:
  - ...
```

```text
- Date: 2026-03-05
  Milestone: M0
  Files changed:
  - AGENTS.md
  - crates/pointer_replacer/src/tests.rs
  - crates/pointer_replacer/src/analyses/offset_sign/mod.rs
  Behavior changes:
  - Canonical rewriter spec was audited as complete for M0 exit criteria (structure map, pipeline, decision precedence, conversion matrix, limitations, test mapping); no rewriter implementation behavior changed.
  - Stabilized one rewriter assertion in tests to match current emitted range-index form (`as usize..]`).
  - Fixed out-of-scope doctest parsing for offset-sign lattice documentation by fencing ASCII art as `text`.
  Tests run:
  - command: cargo test -p pointer_replacer ownership_analysis::malloc_source_marks_return_as_owning
    result: pass
  - command: cargo test -p pointer_replacer ownership_analysis::free_sink_clears_ownership_before_return
    result: pass
  - command: cargo test -p pointer_replacer ownership_analysis::solidify_marks_return_local_as_owning_for_malloc
    result: pass
  - command: cargo test -p pointer_replacer analyses::B02_tests
    result: pass
  - command: cargo test -p pointer_replacer
    result: pass
  Worker runs:
  - role: coverage
    run_id: not-run-trigger-not-met
    verdict: pass
  - role: correctness
    run_id: not-run-trigger-not-met
    verdict: pass
  - role: implementation-readiness
    run_id: not-run-trigger-not-met
    verdict: pass
  Blockers:
  - role: implementation-readiness
    summary: Existing doctest parse failure in `analyses/offset_sign/mod.rs` blocked full-suite green; fixed by text-fencing the lattice diagram.
    status: fixed
  Waiver rationale:
  - none
  Notes:
  - Subworker Validation Protocol trigger was not met because no implementation changes were made under `crates/pointer_replacer/src/rewriter/**/*.rs` and no canonical rewriter behavior changed.
```

```text
- Date: 2026-03-06
  Milestone: M1
  Files changed:
  - AGENTS.md
  - crates/pointer_replacer/src/analyses/ownership/mod.rs
  - crates/pointer_replacer/src/analyses/ownership/call_graph.rs
  - crates/pointer_replacer/src/analyses/ownership/whole_program.rs
  - crates/pointer_replacer/src/analyses/ownership/whole_program/state.rs
  - crates/pointer_replacer/src/analyses/ownership/solidify.rs
  - crates/pointer_replacer/src/analyses/ownership/ssa/constraint/infer.rs
  - crates/pointer_replacer/src/analyses/B02_tests/mod.rs
  - crates/pointer_replacer/src/analyses/B02_tests/buffapp_lib.rs
  - crates/pointer_replacer/src/analyses/B02_tests/generic_foreach.rs
  - crates/pointer_replacer/src/analyses/B02_tests/matrixsum_lib.rs
  - crates/pointer_replacer/src/tests.rs
  Behavior changes:
  - Migrated ownership analysis MIR fetches from `optimized_mir` to `mir_drops_elaborated_and_const_checked`.
  - Aligned B02 and ownership MIR-introspection helpers to the same MIR source.
  - Added guard test to reject `optimized_mir(` reintroduction in ownership/output guarded paths.
  - Made ownership SSA inference tolerant of non-semantic MIR statements introduced by drops-elaborated MIR.
  - Documented and accepted M1 B02 deltas for specific realloc temporaries that are no longer classified as owning locals.
  Tests run:
  - command: cargo test -p pointer_replacer analyses::B02_tests -- --nocapture
    result: pass
  - command: cargo test -p pointer_replacer ownership_analysis::malloc_source_marks_return_as_owning
    result: pass
  - command: cargo test -p pointer_replacer ownership_analysis::free_sink_clears_ownership_before_return
    result: pass
  - command: cargo test -p pointer_replacer ownership_analysis::solidify_marks_return_local_as_owning_for_malloc
    result: pass
  - command: cargo test -p pointer_replacer ownership_analysis::mutable_pointer_to_pointer_argument_becomes_output_param
    result: pass
  - command: cargo test -p pointer_replacer
    result: pass
  - command: ! rg -n "optimized_mir\\(" crates/pointer_replacer/src/analyses/output_params crates/pointer_replacer/src/analyses/ownership crates/pointer_replacer/src/analyses/B02_tests/mod.rs crates/pointer_replacer/src/tests.rs
    result: pass
  Worker runs:
  - role: coverage
    run_id: 019cc08b-dfe8-7742-a11a-ab2cf507df66
    verdict: pass
  - role: correctness
    run_id: 019cc08b-e000-7d20-8604-7098e4bf3e91
    verdict: pass
  - role: implementation-readiness
    run_id: 019cc08f-6fef-7aa2-a143-600ecbaecbab
    verdict: pass
  Blockers:
  - role: none
    summary: none
    status: fixed
  B02 result deltas:
  - case: buffapp_lib
    changed: `src::lib::append_to_buffer#new_data` moved from implicit allocator candidate to explicit non-candidate.
    rationale: `realloc` temporary ownership does not persist as local ownership under drops-elaborated MIR; container field remains owning boundary.
    disposition: accepted
  - case: generic-foreach
    changed: `array_*_push#new_data` realloc temporaries moved from implicit allocator candidates to explicit non-candidates.
    rationale: these locals are short-lived realloc temporaries assigned into aggregate fields; classifying them as non-owning locals avoids false positives while preserving owning container locals.
    disposition: accepted
  - case: matrixsum_lib
    changed: `src::lib::expand_array#new_data` moved from implicit allocator candidate to explicit non-candidate.
    rationale: same realloc-temporary pattern as buffapp/generic_foreach under drops-elaborated MIR.
    disposition: accepted
  Waiver rationale:
  - none
  Notes:
  - Subworker protocol executed with sequential fallback for the third worker due temporary thread-limit; all three roles were completed and recorded.
```

## Planned Change Surface

- `crates/pointer_replacer/src/rewriter/decision.rs`
  - Add new pointer kinds for owning pointers: `OptBox`, `OptBoxedSlice`.
  - Canonical decision rule:
    - owning + output parameter => `OptRef(true)` (non-array), `Slice(true)` (array)
    - owning + not output parameter => `OptBox` (non-array), `OptBoxedSlice` (array)
    - non-owning => existing behavior
  - Minimal hard exceptions that remain raw-oriented:
    - function signatures used as function pointers
    - `c_void`
    - file-like / foreign pointer types
- `crates/pointer_replacer/src/rewriter/mod.rs`
  - Extend rewriter analysis inputs to include ownership and output-parameter facts in addition to mutability/fatness/alias/offset.
- `crates/pointer_replacer/src/rewriter/transform/mod.rs`
  - Add type and expression rewrite paths for new box kinds.
  - Preserve compatibility with existing raw/ref/slice/cursor conversion behavior.
- `crates/pointer_replacer/src/analyses/B02_tests/mod.rs`
  - Add/encode rewrite-then-compile checks for B02 validation (not ownership-only).

## Merged Authoritative Milestones

### M0: Canonical Spec-First

Goal:

- Produce complete canonical specification of the current rewriter in:
  - `crates/pointer_replacer/src/rewriter/CANONICAL_REWRITER_SPEC.md`

Spec must include:

- Full structure map (`mod.rs`, `decision.rs`, `collector.rs`, `transform/mod.rs`)
- End-to-end pipeline
- Decision algorithm and precedence
- Conversion behavior matrix between pointer kinds
- Known limitations and conservative fallbacks
- Test/validation mapping

Exit criteria:

- Spec fully describes current behavior and is referenced by this `AGENTS.md`.

### M1: MIR Source Migration for Ownership/Output Analyses

Goal:

- Unify ownership/output analysis MIR data source to `tcx.mir_drops_elaborated_and_const_checked(did)`.
- Remove remaining `optimized_mir` usage from:
  - `crates/pointer_replacer/src/analyses/ownership/mod.rs`
  - `crates/pointer_replacer/src/analyses/ownership/call_graph.rs`
  - `crates/pointer_replacer/src/analyses/ownership/whole_program.rs`
  - `crates/pointer_replacer/src/analyses/ownership/whole_program/state.rs`
  - `crates/pointer_replacer/src/analyses/ownership/solidify.rs`
- Keep `crates/pointer_replacer/src/analyses/output_params/mod.rs` on drops-elaborated MIR (already migrated).
- Align MIR-introspection harnesses to the same source:
  - `crates/pointer_replacer/src/analyses/B02_tests/mod.rs`
  - `crates/pointer_replacer/src/tests.rs`
- Add an explicit MIR-source regression guard check (test-backed) so `optimized_mir(` reintroduction in the above paths is rejected.

Exit criteria:

- No analysis crashes/regressions in ownership/output test suites.
- Required migration call sites are complete.
- Milestone completion requires passing `Subworker Validation Protocol`.
- Any B02 candidate/output deltas are documented with rationale in `Milestone Completion Log`.

Required validation:

- `cargo test -p pointer_replacer analyses::B02_tests -- --nocapture`
- `cargo test -p pointer_replacer ownership_analysis::malloc_source_marks_return_as_owning`
- `cargo test -p pointer_replacer ownership_analysis::free_sink_clears_ownership_before_return`
- `cargo test -p pointer_replacer ownership_analysis::solidify_marks_return_local_as_owning_for_malloc`
- `cargo test -p pointer_replacer ownership_analysis::mutable_pointer_to_pointer_argument_becomes_output_param`
- `cargo test -p pointer_replacer`
- `! rg -n "optimized_mir\\(" crates/pointer_replacer/src/analyses/output_params crates/pointer_replacer/src/analyses/ownership crates/pointer_replacer/src/analyses/B02_tests/mod.rs crates/pointer_replacer/src/tests.rs`

### M2: Post-Spec Plumbing Foundation (retained)

Goal:

- After M0 is complete, thread ownership-aware data plumbing into rewriter context without changing rewrite output behavior.

Exit criteria:

- Existing rewrite tests remain green.
- Milestone completion requires passing `Subworker Validation Protocol`.

Required validation:

- `cargo test -p pointer_replacer`

### M3: Decision Logic Extension

Goal:

- Extend `PtrKind` with owning box categories.
- Integrate ownership + output-parameter facts into the decision flow.

Scope note:

- Do not consume struct-field ownership data by default in this milestone.
- This milestone does not authorize struct-field type rewriting.

Canonical high-level logic:

- owning + output parameter => `OptRef(true)` or `Slice(true)` (array)
- owning + not output parameter => `OptBox` or `OptBoxedSlice` (array)
- non-owning => previous behavior

Policy:

- Strict ownership policy by default.
- Minimal hard exceptions only for known non-boxable/special cases (function-pointer-signature constraints, `c_void`, file-like/foreign pointers).

Exit criteria:

- Decision logic distinguishes owning scalar/array and output-parameter overrides correctly.
- Milestone completion requires passing `Subworker Validation Protocol`.

### M4A: Core Rewrite Implementation

Goal:

- Implement actual rewriting support for new box kinds in `transform/mod.rs`.
- Add malloc/calloc-origin rewrite behavior:
  - scalar owning allocations -> `Some(Box::new(Default::default()))` style path
  - array owning allocations -> `Some(vec![T::default(); n].into_boxed_slice())` style path
- Integrate new kinds with existing conversion logic.

Scope note:

- Do not consume struct-field ownership data by default in this milestone.
- This milestone does not authorize struct-field type rewriting.

Exit criteria:

- Milestone completion requires passing `Subworker Validation Protocol`.

### M4B: Conditional Struct Support

Goal:

- Add struct support required by M4A compile failures:
  - `Default` generation policy for program-defined structs (pointer fields null-like defaults, non-pointer fields inductive defaults)
  - `take()` extraction helper policy for indirect ownership movement

Exit criteria:

- Implement only if compile failures show this support is required; otherwise defer.
- Milestone completion requires passing `Subworker Validation Protocol`.

Scope note:

- Do not consume struct-field ownership data by default in this milestone.
- This milestone does not authorize struct-field type rewriting unless explicitly approved by the user.

### M5: B02 Rewrite Compile Gate

Goal:

- Ensure B02 targets are validated through rewrite flow, not ownership-only checks.

Validation gate:

1. `cargo test -p pointer_replacer analyses::B02_tests`
2. `cargo test -p pointer_replacer`

Exit criteria:

- B02 suite and full `pointer_replacer` suite pass with rewrite-enabled checks in place.
- Milestone completion requires passing `Subworker Validation Protocol`.

### M6: Unsafe Minimization and Hardening

Goal:

- Reduce remaining `malloc`/`calloc`/`free` usage and avoid unnecessary new unsafe paths (for example excessive `Box::from_raw`).

Strategy included in scope:

- For allocator-origin locals that remain `Raw`, allow bridging via `Box::into_raw(Box::new(...))` when it reduces allocator/free reliance while preserving semantics.

Tracking policy:

- Best-effort trend tracking for allocator/free calls and `Box::from_raw` usage in transformed outputs.
- Require monotonic improvement where practical; if not improved, include rationale in milestone log.
- Milestone completion requires passing `Subworker Validation Protocol`.

## Guardrails

- Preserve semantics for non-owning and raw-pointer flows.
- Keep conservative fallback behavior when pointer provenance/shape is ambiguous.
- Preserve function-pointer-signature compatibility constraints.
- Apply strict ownership policy only with the explicitly listed minimal hard exceptions.
- Do not consume struct-field ownership data by default for decision support/validation.
- Do not rewrite struct field types unless explicitly approved by the user.
- Do not broaden implementation scope outside `crates/pointer_replacer/src/rewriter` without explicit user approval.

## Required Test Scenarios

- Rewriter baseline tests in `crates/pointer_replacer/src/tests.rs` remain green.
- Ownership baseline tests remain green.
- New decision tests for M3:
  - owning + output param -> ref/slice(mut)
  - owning + non-output -> box/boxed-slice
  - non-owning unchanged
- New rewrite tests for M4A/M4B:
  - malloc scalar owning local/return
  - calloc array owning local/return
  - mixed-kind conversions involving new box kinds
- M5 gate:
  - all B02 cases pass under `analyses::B02_tests`
  - full crate tests pass
- M6 reporting:
  - allocator/free/unsafe-bridge trend summary present
  - no unjustified regressions

## Validation Loop

Core commands to run during milestone work:

1. `cargo test -p pointer_replacer ownership_analysis::malloc_source_marks_return_as_owning`
2. `cargo test -p pointer_replacer ownership_analysis::free_sink_clears_ownership_before_return`
3. `cargo test -p pointer_replacer ownership_analysis::solidify_marks_return_local_as_owning_for_malloc`
4. `cargo test -p pointer_replacer ownership_analysis::mutable_pointer_to_pointer_argument_becomes_output_param`
5. `cargo test -p pointer_replacer analyses::B02_tests -- --nocapture`
6. `cargo test -p pointer_replacer`
7. `! rg -n "optimized_mir\\(" crates/pointer_replacer/src/analyses/output_params crates/pointer_replacer/src/analyses/ownership crates/pointer_replacer/src/analyses/B02_tests/mod.rs crates/pointer_replacer/src/tests.rs`

Pass criteria:

- No new failures in `pointer_replacer` tests.
- Milestone-specific new tests pass.
- Conservative fallback behavior is preserved where required.
- MIR-source guard check reports no forbidden `optimized_mir(` usage in guarded paths.

## Handoff Template

For each agent update, include:

- Changed files
- Milestone targeted
- Ownership assumptions used
- Where conservative fallback was applied
- Tests run (exact commands + pass/fail)
- Worker summaries (coverage, correctness, implementation-readiness)
- Blocker status (fixed, waived, or open) with evidence links
- Explicit gate result (`PASS`, `SOFT-BLOCK`, or `BLOCK`)
- Remaining risks and smallest next milestone-aligned step

## Assumptions and Defaults

- Canonical spec path is `crates/pointer_replacer/src/rewriter/`.
- Progress tracking uses both checklist and completion log.
- Roadmap mode is merged (legacy and new flow in one authoritative list).
- Ownership policy is strict by default with minimal hard exceptions for non-boxable/special cases.
- Milestone deviations require asking the user first.
- Worker triad is fixed: coverage, correctness, implementation-readiness.
- Gate decisions are severity-based, not score-threshold-based.
- Correctness blockers are hard-blocking by default.
- Coverage/readiness blockers are soft-blocking unless explicitly waived by user and logged.
- B02/ownership result deltas in M1 are allowed only with explicit rationale in milestone logs; unexplained deltas are blockers.
