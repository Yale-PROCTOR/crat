# Cursor-Aware ArrayPtr for Memcpy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Replace the 360 measured SPHINCS cursor-source memcpy calls with bounded `copy_from_slice` operations, without changing cursor owners.

**Architecture:** Extend `ArrayPtr` with cursor backing and representation-aware slice projection. A memcpy-only recognizer admits byte cursors into the existing numeric byte-copy arm; a narrow local exception admits full-array offsets previously blocked by the whole-function raw-dereference guard. Reuse the existing emitters, trust promoted borrows, and keep original scalar expressions inline.

**Tech Stack:** Rust, rustc-private AST/HIR/type APIs, existing bytemuck support, `nightly-2025-06-23`, Cargo, Python corpus harness.

**Spec:** [Simpler ArrayPtr design, revised 2026-10-14](../specs/2026-10-13-memcpy-cursor-byte-views-design.md)

**Plan revised:** 2026-10-16. All five tasks implemented and validated using native execution. Final review completed; its source-reborrow count finding was fixed and verified.

**Validation:** [Revision-pinned report](/home/ubuntu/crat-workspace/memcpy-cursor-validation-de8934c7/REPORT.md). Product revision `d4b91111`: 360 cursor adapters removed, unchanged owners, 128 SPHINCS runtime cases passed, and 2,753 wider corpus vectors passed. The strict result gate also retains 512 legacy block-tail calls; the report records this tradeoff.

## Global Constraints

- Worktree: `/home/ubuntu/.config/superpowers/worktrees/crat/representation-aware-cursor-resolution`; implementation started at `475fe55a`, with product baseline `cecfed7b3554ed016b1613c6ec8b5da4dacf4531`.
- Do not restore or assume changes from `blake-mask-cursor-proof`.
- Treat the original C program as UB-free. Trust existing promoted Rust references and generated cursor backing slices.
- Do not repeat borrow-promotion or whole-array alias analysis in the libc pass.
- Do not infer that unsigned arithmetic cannot wrap, or that unsigned-to-signed casts preserve nonnegativity.
- Do not introduce unconditional offset/count temporaries.
- No changes to pointer representations, ABI wrappers, field/return/function-pointer demotion, `memmove`/`memset` policy, or general sign/alias analysis.
- Support initialized `u8`/`i8` operands on both sides of newly admitted calls. Preserve existing array-only typed/object behavior; guard exceptions apply only to eligible byte copies.
- Extend `ArrayPtr`; do not add `MemcpyByteView`, `transform_memcpy_bytes`, or another copy emitter.
- Target all 360 candidates: 120 plain/sliced destinations and 240 offset destinations; expected cursor-owner change is zero.
- Never access `aws-translate` or `bundles`; never run `scripts/translate.py` or `scripts/translate_all.py`.
- Preserve `/home/ubuntu/crat-workspace/sphincs-diagnosis-cecfed7b-20260928` and `/home/ubuntu/crat-workspace/transformed` as immutable baselines.
- Implementation is not authorized by creating this plan. Execute only after the user requests implementation.

## Review Focus

- A used memcpy return value must not fall through to a legacy unit-valued replacement (Task 1).
- Shared helper changes must not enable cursor `memmove`/`memset`, object-to-cursor copies, non-byte cursor copies, or lookalike cursor types (Task 2).
- A pure count that reads the destination may still conflict with the generated borrow; use conservative fallback (Task 2).
- Mutable cursor offset temporaries must remain alive without extending a reborrow into the next statement (Tasks 2 and 4).
- Empty one-past copies and exact-end copies must preserve bytes and cursor positions (Task 4).

---

## File and Responsibility Map

| File | Change |
| --- | --- |
| `crates/passes/src/libc_replacer/mod.rs` | Discarded-result gate at memcpy dispatch |
| `crates/passes/src/libc_replacer/mem_utils.rs` | Extend `ArrayPtr` and its projection, add memcpy-only recognition and local eligibility, reuse existing copy arms |
| `crates/passes/src/libc_replacer/str_utils.rs` | Expose existing pure cursor projection helper to its sibling module |
| `crates/passes/src/libc_replacer/tests.rs` | Typechecked rewrite tests and one small runtime-test helper |
| `crates/passes/src/libc_replacer/fixtures/memcpy_cursor.rs` | Self-contained u8 runtime fixture transformed by the real libc pass |
| Fresh directory under `/home/ubuntu/crat-workspace/` | Validation runner, frozen binary, manifests, logs, inventories, and report |

Do not modify the shared `utils::ir::array_of_as_ptr`, pointer analysis, CLI wiring,
or Cargo dependencies. Read `src/bin/crat.rs` for pass integration, not to edit it.

## Task 1: Preserve memcpy return values

**Files:** Modify `libc_replacer/mod.rs`; test in `libc_replacer/tests.rs` (paths above).

**Interfaces:** Retain `transform_memcpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr>`. Its caller invokes it only for a HIR semicolon statement, using the existing `strncpy` dispatch pattern.

- [x] Add `test_memcpy_used_results_are_preserved`: valid array operands whose memcpy return is assigned, returned as a tail expression, or passed to another function. For each fixture, use `run_test(code, &["memcpy("], &["copy_from_slice"])`; the harness must still typecheck the transformed result. Include both numeric-array and object-to-byte legacy routes.
- [x] Run `cargo test -p passes libc_replacer::tests::test_memcpy_used_results -- --nocapture`. Expect failure before the fix because a legacy replacement loses the pointer result.
- [x] Gate the entire memcpy dispatch on `parent_hir_node` being `StmtKind::Semi`. Preserve the existing three-argument check. Do not add result reconstruction or change other libc calls.
- [x] Run the new test and `cargo test -p passes libc_replacer::tests::test_memcpy -- --nocapture`. Existing semicolon-statement replacements must continue to pass.
- [x] Commit only this change: `fix(libc): preserve consumed memcpy return values`.

## Task 2: Extend ArrayPtr for cursor operands in existing memcpy emission

**Files:** Modify `mem_utils.rs`, minimally expose helpers in `str_utils.rs`, add tests in `tests.rs`.

**Interfaces:** Retain `ArrayPtr` and its current element type, original receiver,
and optional outer raw offset. Add a small array/cursor backing distinction and
the cursor projection information needed by `slice`; the exact enum layout is
left to the builder. Keep these existing methods and meanings:

```rust
// ArrayPtr methods; cursor destination mutability is checked at recognition.
fn slice(&self, mutable: bool) -> String;
fn byte_slice(&self, mutable: bool) -> String;
fn same_array(&self, other: &Self) -> bool;
fn is_plain(&self) -> bool; // No outer raw offset; not a safety classification.
fn is_cursor(&self) -> bool; // New backing-kind query.

// TransformVisitor methods; these do not emit copies or mutate dependencies.
fn memcpy_ptr_or_offset<'e>(&self, expr: &'e Expr, mutable: bool)
    -> Option<ArrayPtr<'e, 'tcx>>;
fn memcpy_byte_copy_is_eligible(
    &self, dst: &ArrayPtr<'_, 'tcx>, src: &ArrayPtr<'_, 'tcx>, n: &Expr,
) -> bool;
fn memcpy_scalar_is_repeatable(&self, expr: &Expr, dst: &Expr) -> bool;
```

`array_of_ptr_or_offset` remains array-only and keeps its current signature for
`memmove`/`memset`. The memcpy recognizer tries it before adding cursor recognition;
it does not restrict previously recognized arrays. The eligibility predicate
validates both operands together before admitting a cursor-containing copy.
Task 2 conservatively rejects outer raw offsets for these new calls; Task 3
extends this same predicate to full-array offsets and uses it for guard exceptions.

Expose the existing `slice_cursor_of_as_ptr(&self, s: &Expr, mutable: bool,
method_names: &[&str]) -> Option<(String, ty::Ty<'tcx>)>` as `pub(super)` without
changing its behavior for string callers. Other helpers remain private unless
the implementation actually needs their existing logic.

- [x] Add `test_memcpy_cursor_byte_views`: array/slice and generated cursor source/destination combinations, including already-sliced arrays, immutable cursors, mutable cursors, and mixed `i8`/`u8`. Follow the existing `test_slice_cursor_offset_by_as_ptr_uses_safe_byte_slice` fixture convention. Assert `copy_from_slice` and the appropriate `as_slice`/`as_slice_mut` projections; exclude the original memcpy call and source cursor `.as_ptr()` adapter. Assert selected i8 rewrites use the existing bytemuck casts; do not independently redesign the existing emitter's dependency flags.
- [x] Add `test_memcpy_cursor_inline_scalars`: `fill as usize`, `(datalen >> 3) as usize`, disjoint field counts, and typed primitive wrapping expressions. Assert the original expression remains in both bounds and no scalar `let` was added. Include narrow unsigned-to-signed casts in expressions without simplifying them.
- [x] Add `test_memcpy_cursor_fallbacks`: arbitrary calls/assignments in operands or count, borrow-wrapper calls, raw destinations, mutable statics, pointer/integer round trips, a foreign `other::SliceCursor`, conflicting projections of the same mutable cursor, and counts reading the destination (`dst.len()` and `dst[0]`). Use a cursor operand so rejection cannot accidentally succeed through an unrelated legacy array route. Assert the call is retained, the result typechecks, and rejected i8 candidates do not alone set `res.bytemuck`.
- [x] Add `test_memcpy_cursor_scope_is_local`: cursor `memmove` and `memset`, a `SliceCursor<u32>` memcpy, an object copied into a mutable cursor, and a cursor paired with a non-byte array all stay unchanged. Existing array-to-array typed copies and same-array temporary copies still transform. Include a nontrivial wrapping byte-count expression in a byte-cursor copy and assert it survives verbatim rather than being converted to an element count.
- [x] Run `cargo test -p passes libc_replacer::tests::test_memcpy_cursor -- --nocapture`. Confirm the positive cases fail because current memcpy recognition excludes cursors. Negative characterization cases may already pass.
- [x] Extend `ArrayPtr` backing and make `slice` select the original array borrow or a cursor projection supplied by the existing cursor helper. Keep `byte_slice` wrapping `slice`; keep array-to-array `same_array` behavior and `is_plain` semantics. Reject conflicting same-cursor projections separately instead of treating receiver text as backing-allocation identity. Preserve `as_deref()` for mutable cursor offset temporaries and mutable reference reborrows where needed. Existing non-memcpy callers must continue to construct only array-backed operands.
- [x] Implement `memcpy_ptr_or_offset` and `memcpy_byte_copy_is_eligible` for ordinary cursor copies. Validate byte element types on both sides, pointer-only cast chains, stable places through references (no new raw dereference), and known cursor identity in `crate::slice_cursor`. Check actual destination writability; a const pointer cast to mutable does not establish a mutable view. Keep extra eligibility and identity checks local to memcpy; do not alter existing string recognition semantics or previously accepted array-only inputs.
- [x] Implement the scalar whitelist using resolved primitive types and stable local/constant reads, safe field projections, casts, arithmetic/bitwise operators, explicitly recognized primitive wrapping methods, and the resolved zero-argument `size_of::<T>()` constant query. Preserve that query and any wrapping multiplication verbatim; it is not permission to cancel element sizes. Reject arbitrary calls, static/raw reads, or accesses conflicting with the destination place. A read of `state.count` is allowed beside a borrow of `state.buf`; a read of `dst` itself is not. This is a local syntactic/type eligibility check, not new alias analysis. Choose fallback for destination-dependent counts; no scalar hoisting machinery is needed.
- [x] Change only memcpy's operand lookups to `memcpy_ptr_or_offset`. If either operand is a cursor, require the combined eligibility check and skip the typed-length arm so the existing numeric byte-copy arm uses the original byte count. Reuse that arm's `slice`, `byte_slice`, and copy emission without adding another emitter. Finish new-call eligibility before dependency flags change. Preserve the existing branch selection for array-only calls and restrict object-copy fallback to array-backed destinations with no cursor operand; unsupported cursor-containing calls return `None`.
- [x] Run `cargo test -p passes libc_replacer::tests -- --nocapture`. This verifies generated Rust typechecking, existing string projection tests, same-array behavior, and padded-object exclusions. Commit: `feat(libc): copy through existing cursor byte views`.

## Task 3: Support full-array offsets at the call site

**Files:** Extend `mem_utils.rs`; add tests in `tests.rs`.

**Interfaces:** Extend Task 2's `memcpy_byte_copy_is_eligible` to validate the
existing `ArrayPtr::offset` and its original pointer expression. Retain original
cast-chain provenance as a small field if the eligibility check needs it; do not
attempt to infer offset units from the final byte element type alone. The
recognizer and slice-emitter signatures remain unchanged.

- [x] Add `test_memcpy_cursor_full_array_offsets`: a state with `[u8; 64]` and `[u8; 128]` fields, existing mutable state references, and an unrelated raw dereference in the same function. Exercise both destination and source full-array offsets with cursor counterparts. Assert the replacements survive the enclosing raw dereference, retain `(left as isize) as usize`, use suffix-then-prefix indexing, and introduce no offset/count bindings.
- [x] Add `test_memcpy_cursor_offset_fallbacks`: raw offsets from an interior slice/cursor suffix that can validly be negative, offsets through a `u32` cast, effectful offsets, and fields reached by a newly introduced raw dereference. Assert memcpy remains for these new cursor combinations. Also exercise a cursor's own valid negative `offset_by` from a positive position: retain the cursor operation rather than converting it to suffix indexing.
- [x] Add `test_memcpy_array_offset_guard_exception`: array-only byte copies through existing references qualify under the same local rule even with an unrelated raw dereference. Non-byte offset copies and byte copies through raw-derived places retain their previous rejection under that guard. Include an eligible array-only call whose count matches the old typed-length pattern: it must reach the existing byte arm rather than return early from the old typed arm's guard.
- [x] Run `cargo test -p passes libc_replacer::tests::test_memcpy_ -- --nocapture`. The newly supported cursor and array-only guard-exception cases should fail before this task's code change.
- [x] Extend eligibility to exactly an outer raw `.offset(k)` on a full byte-array base pointer with unchanged offset units. Use receiver HIR type to distinguish a full array from a slice; peel reference types without accepting raw-pointer dereferences. Apply the scalar rule to each offset as well as the count, retain original signed casts, and use existing `ArrayPtr::slice` suffix indexing. Do not reinterpret a cursor's own `offset_by` as an outer raw offset.
- [x] Compute the narrow exception when the original memcpy guard would reject and the combined byte eligibility predicate succeeds. A newly admitted offset call skips the typed-length arm and uses the existing numeric byte-copy arm. Suppress that arm's raw-dereference rejection only for the eligible exception. Preserve original rejection for every other call and leave object-copy, `memmove`, and `memset` guards untouched. Do not redefine `is_plain` or delete `current_fn_has_raw_deref`.
- [x] Run `cargo test -p passes libc_replacer::tests -- --nocapture`, including `test_offset_memory_calls_use_slice_replacements` and `test_memcpy_autoref`. The latter remains supported through its existing legacy route. Commit: `feat(libc): copy cursor bytes into offset array fields`.

## Task 4: Execute transformed copies at boundaries

**Files:** Add `fixtures/memcpy_cursor.rs`; modify `tests.rs` only.

**Interfaces:** Add test-local `fn run_memcpy_runtime(code: &str)` and `test_memcpy_cursor_runtime`. It invokes the real libc replacement, verifies the eligible calls were replaced, typechecks the result, compiles that emitted u8-only fixture with the repository toolchain, then executes it. Use `std::process::Command` and a unique temporary directory; no dependency or general testing framework changes. Fail with compiler/runtime diagnostics and remove the temporary files after success.

- [x] Create a self-contained fixture with faithful generated cursor operations, existing reference-backed state, and an assertion-driven `main`. Use data `[10, 20, 30, 40, 50]` with cursor position 1 and destination `[99; 6]`. A three-byte copy at destination offset 2 must yield `[99, 99, 20, 30, 40, 99]`; assert the cursor's current pointer/position is unchanged.
- [x] Add empty copies with the source cursor at `base.len()` and the destination offset at its array length, plus a three-byte copy at destination offset 3 yielding `[99, 99, 99, 20, 30, 40]`. Cover mutable cursor destinations and a temporary mutable cursor reborrow, then use the original cursor again in the following statement. These cases must not panic or extend the borrow.
- [x] Run `cargo test -p passes libc_replacer::tests::test_memcpy_cursor_runtime -- --nocapture`. Require both actual rewrite assertions and successful execution; merely executing the remaining libc memcpy is not sufficient. i8 behavior is covered by Task 2's typechecked bytemuck route and corpus tests rather than adding runtime dependency discovery here.
- [x] Run the full libc test module once after the fixture/helper is complete. Commit: `test(libc): execute cursor memcpy boundary cases`.

## Task 5: Verify the measured opportunity and regressions

**Files:** No planned production changes. Create validation artifacts under a fresh `/home/ubuntu/crat-workspace/memcpy-cursor-validation-<implementation-revision>/` directory. Read the archived diagnosis but never edit or rerun its scripts in place.

**Interfaces:** Consume the implementation revision and frozen `crat` binary. Produce `manifest.json`, `results.json`, per-case adapter/owner inventories, runtime logs, and `REPORT.md`. Keep measured outcomes distinct from the 360-site target.

- [x] Run from the implementation worktree, in order: `cargo fmt`, `cargo clippy --workspace --all-targets`, `cargo test --workspace`, and `cargo build --release --bin crat`. Review formatting changes and commit only relevant fixes before freezing the validated revision. New code changes restart affected checks; passing checks do not require repeated full runs without a reason.
- [x] Create the isolated validation directory. Adapt a copy of archived `run_baseline.py` to `run_candidate.py`: use the archive manifest's exact 128 case paths, the existing pretranslated inputs, a fresh `candidate` output tree, and a frozen copy of the new release binary. Preserve the archived transform chain, including `enum`, and its pinned `transform.py`/`utils.py` for the SPHINCS comparison. Retarget the harness's `crat` link to the implementation worktree. Record full revision, binary/toolchain/script hashes, exact commands, and input hashes; compare those input hashes with the archive. Do not use an archived instrumented binary or rerun its counterfactual analyses.
- [x] First run the new harness for case `005_sphincs_PQCgenKAT_sign_blake_128f_simple` through `bin`. Verify six removed cursor-source adapters: two hash-message and four update-function copies. If rejected, inspect the generated call against the existing eligibility rules before broadening anything. Then run `python3 run_candidate.py` for all 128 manifest cases, requiring 128 successful pipelines. The harness should retain the archive's `transform_tc(output, case, 'bin', False, True)` interface and full pointer-decision diagnostics.
- [x] Adapt a copy of `inventory.py` to the new output directory. Compare every owner record/category/representation with the archive and compare pointer-stage Rust directly; it should be unchanged. Inspect libc-stage call sites and final generated application code separately. Report six removed cursor adapters in each of 60 Blake cases, zero such candidates in other families, 360 total replacements, and zero owner changes. Do not substitute textual `SliceCursor` counts or global raw-pointer counts for owner/site counts. Explain any additional legacy array replacements separately.
- [x] Prepare an isolated runner containing only the corpus directories and tooling needed by the official scripts, excluding forbidden directories. `test.py` overwrites each runner case's `translated_rust`, so do not point it at the shared corpus. Confirm the CLI with `--help`, then run `python3 scripts/test.py <candidate-output> Test-Corpus/Public-Tests/P01_sphincs_plus/005_sphincs_PQCgenKAT_sign_blake_128f_simple --verbose`. Run all 128 SPHINCS cases with the same single-case interface, including library cases. For failures, run the frozen baseline output in that same isolated runner to separate existing failures from regressions; the old report did not establish runtime success.
- [x] Follow the Crat test-workflow skill for wider public/hidden regression. In the isolated runner, confirm script CLI versions and point their `crat` resolution at the implementation checkout. Run `python3 scripts/transform_all.py <regression-output> libc --run-dependencies`, complete the remaining chain through `bin` (reuse completed predecessors where supported), then `python3 scripts/test_all.py <regression-output>`. Immediately run `python3 scripts/find_unsafe.py` and `python3 scripts/summarize_unsafe.py` before another test run replaces the measured trees. Use outside-sandbox execution for transform/test scripts. Compare any failures or unexpected unsafe-count increases against an explicitly pinned baseline.
- [x] Write the final report with exact successes/failures, 120/240 candidate breakdown, owner counts by category, cursor text counts separately, ABI/boundary observations, and links to logs. Never report 360 verified wins solely from matching source patterns. If any candidate remains or required corpus input is unavailable, identify it explicitly and leave the corresponding acceptance item incomplete. Do not broaden sign/field/return/function-pointer scope to force completion.

## Self-review and handoff

Task 1 covers result semantics. Task 2 extends the existing operand and emitter,
with cursor recognition confined to memcpy. Task 3 addresses the second measured
obstacle through an explicit local guard exception. Their tests cover byte types,
cast units, original byte counts, inline expressions, temporary lifetimes, and
legacy behavior. Task 4 checks actual boundary-copy behavior; Task 5 establishes
pinned metrics and regressions. Existing borrow promotion remains trusted.

The implementer should keep these tasks sequential because they share the
matcher/emitter and tests. The user authorized native execution. Tasks 1–5 and the final whole-branch review are complete. The review finding
was fixed with a RED/GREEN regression and a fresh passing workspace suite.
