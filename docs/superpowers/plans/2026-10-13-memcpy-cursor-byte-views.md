# Memcpy Cursor Byte Views Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the 360 measured SPHINCS cursor-source memcpy calls with bounded `copy_from_slice` operations, without changing cursor owners.

**Architecture:** Add a conservative byte-view route to the libc replacer before its existing typed/object routes. Reuse generated cursor projections and existing byte casts, trust promoted borrows, and emit original scalar expressions directly in indexing. Gate every memcpy replacement on a discarded result; preserve legacy fallback and same-array handling.

**Tech Stack:** Rust, rustc-private AST/HIR/type APIs, existing bytemuck support, `nightly-2025-06-23`, Cargo, Python corpus harness.

**Spec:** [Approved design, including inline-expression revision](../specs/2026-10-13-memcpy-cursor-byte-views-design.md)

## Global Constraints

- Worktree: `/home/ubuntu/.config/superpowers/worktrees/crat/representation-aware-cursor-resolution`; planning starts at `cbddd420`, with product baseline `cecfed7b3554ed016b1613c6ec8b5da4dacf4531`.
- Do not restore or assume changes from `blake-mask-cursor-proof`.
- Treat the original C program as UB-free. Trust existing promoted Rust references and generated cursor backing slices.
- Do not repeat borrow-promotion or whole-array alias analysis in the libc pass.
- Do not infer that unsigned arithmetic cannot wrap, or that unsigned-to-signed casts preserve nonnegativity.
- Do not introduce unconditional offset/count temporaries.
- No changes to pointer representations, ABI wrappers, field/return/function-pointer demotion, `memmove`/`memset` policy, or general sign/alias analysis.
- Support initialized `u8`/`i8` views; retain existing typed/object routes and their guards.
- Target all 360 candidates: 120 plain/sliced destinations and 240 offset destinations; expected cursor-owner change is zero.
- Never access `aws-translate` or `bundles`; never run `scripts/translate.py` or `scripts/translate_all.py`.
- Preserve `/home/ubuntu/crat-workspace/sphincs-diagnosis-cecfed7b-20260928` and `/home/ubuntu/crat-workspace/transformed` as immutable baselines.
- Implementation is not authorized by creating this plan. Execute only after the user requests implementation.

## Review Focus

- A used memcpy return value must not fall through to a legacy unit-valued replacement (Task 1).
- Pointer/integer casts, wider-pointee offsets, or an unrelated type named `SliceCursor` must not enter the new route (Tasks 2–3).
- A pure count that reads the destination may still conflict with the generated borrow; use conservative fallback (Task 2).
- Mutable cursor offset temporaries must remain alive without extending a reborrow into the next statement (Tasks 2 and 4).
- Empty one-past copies and exact-end copies must preserve bytes and cursor positions (Task 4).

---

## File and Responsibility Map

| File | Change |
| --- | --- |
| `crates/passes/src/libc_replacer/mod.rs` | Discarded-result gate at memcpy dispatch |
| `crates/passes/src/libc_replacer/mem_utils.rs` | New byte-view matcher, expression eligibility, and copy emission |
| `crates/passes/src/libc_replacer/str_utils.rs` | Expose existing pure cursor projection helper to its sibling module |
| `crates/passes/src/libc_replacer/tests.rs` | Typechecked rewrite tests and one small runtime-test helper |
| `crates/passes/src/libc_replacer/fixtures/memcpy_cursor.rs` | Self-contained u8 runtime fixture transformed by the real libc pass |
| Fresh directory under `/home/ubuntu/crat-workspace/` | Validation runner, frozen binary, manifests, logs, inventories, and report |

Do not modify the shared `utils::ir::array_of_as_ptr`, pointer analysis, CLI wiring,
or Cargo dependencies. Read `src/bin/crat.rs` for pass integration, not to edit it.

## Task 1: Preserve memcpy return values

**Files:** Modify `libc_replacer/mod.rs`; test in `libc_replacer/tests.rs` (paths above).

**Interfaces:** Retain `transform_memcpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr>`. Its caller invokes it only for a HIR semicolon statement, using the existing `strncpy` dispatch pattern.

- [ ] Add `test_memcpy_used_results_are_preserved`: valid array operands whose memcpy return is assigned, returned as a tail expression, or passed to another function. For each fixture, use `run_test(code, &["memcpy("], &["copy_from_slice"])`; the harness must still typecheck the transformed result. Include both numeric-array and object-to-byte legacy routes.
- [ ] Run `cargo test -p passes libc_replacer::tests::test_memcpy_used_results -- --nocapture`. Expect failure before the fix because a legacy replacement loses the pointer result.
- [ ] Gate the entire memcpy dispatch on `parent_hir_node` being `StmtKind::Semi`. Preserve the existing three-argument check. Do not add result reconstruction or change other libc calls.
- [ ] Run the new test and `cargo test -p passes libc_replacer::tests::test_memcpy -- --nocapture`. Existing semicolon-statement replacements must continue to pass.
- [ ] Commit only this change: `fix(libc): preserve consumed memcpy return values`.

## Task 2: Recover ordinary cursor byte views and emit inline copies

**Files:** Modify `mem_utils.rs`, minimally expose helpers in `str_utils.rs`, add tests in `tests.rs`.

**Interfaces:** Add these private interfaces in `mem_utils.rs`; they are shared with Task 3:

```rust
struct MemcpyByteView<'e, 'tcx> {
    slice: String,             // Typed slice expression before optional i8 byte cast.
    receiver: &'e Expr,         // Original place/cursor receiver for local conflict checks.
    elem_ty: ty::Ty<'tcx>,      // Only u8 or i8.
    is_cursor: bool,
}

fn transform_memcpy_bytes(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr>;
fn memcpy_byte_view<'e>(&self, s: &'e Expr, mutable: bool)
    -> Option<MemcpyByteView<'e, 'tcx>>;
fn memcpy_scalar_is_repeatable(&self, expr: &Expr, dst: &Expr) -> bool;
```

Expose the existing `slice_cursor_of_as_ptr(&self, s: &Expr, mutable: bool,
method_names: &[&str]) -> Option<(String, ty::Ty<'tcx>)>` as `pub(super)` without
changing its behavior for string callers. Other helpers remain private unless
the implementation actually needs their existing logic.

- [ ] Add `test_memcpy_cursor_byte_views`: array/slice and generated cursor source/destination combinations, including already-sliced arrays, immutable cursors, mutable cursors, and mixed `i8`/`u8`. Follow the existing `test_slice_cursor_offset_by_as_ptr_uses_safe_byte_slice` fixture convention. Assert `copy_from_slice` and the appropriate `as_slice`/`as_slice_mut` projections; exclude the original memcpy call and source cursor `.as_ptr()` adapter. Assert `res.bytemuck` only for selected i8 rewrites.
- [ ] Add `test_memcpy_cursor_inline_scalars`: `fill as usize`, `(datalen >> 3) as usize`, disjoint field counts, and typed primitive wrapping expressions. Assert the original expression remains in both bounds and no scalar `let` was added. Include narrow unsigned-to-signed casts in expressions without simplifying them.
- [ ] Add `test_memcpy_cursor_fallbacks`: arbitrary calls/assignments in operands or count, borrow-wrapper calls, raw destinations, mutable statics, pointer/integer round trips, a foreign `other::SliceCursor`, conflicting projections of the same mutable cursor, and counts reading the destination (`dst.len()` and `dst[0]`). Use a cursor operand so rejection cannot accidentally succeed through an unrelated legacy array route. Assert the call is retained, the result typechecks, and rejected i8 candidates do not alone set `res.bytemuck`.
- [ ] Run `cargo test -p passes libc_replacer::tests::test_memcpy_cursor -- --nocapture`. Confirm the positive cases fail because current memcpy recognition excludes cursors. Negative characterization cases may already pass.
- [ ] Implement the pure view matcher for non-offset array/slice pointers and generated cursor projections. Validate actual byte element types, pointer-only cast chains, stable places through references (no new raw dereference), and known cursor identity in `crate::slice_cursor`. Keep that extra identity validation local to memcpy; do not alter existing string recognition semantics. Preserve `as_deref()` for mutable cursor offset temporaries and explicit `&mut *receiver` reborrows where needed.
- [ ] Implement the scalar whitelist using resolved primitive types and stable local/constant reads, safe field projections, casts, arithmetic/bitwise operators, and explicitly recognized primitive wrapping methods. Reject arbitrary calls, static/raw reads, or accesses conflicting with the destination place. A read of `state.count` is allowed beside a borrow of `state.buf`; a read of `dst` itself is not. This is a local syntactic/type eligibility check, not new alias analysis. Choose fallback for destination-dependent counts; no scalar hoisting machinery is needed.
- [ ] Call the byte route at the start of `transform_memcpy`, before its current destination `?` can reject cursors. Complete eligibility for both operands and count before setting `self.bytemuck`. Cast i8 views to u8 only for the selected rewrite; emit equal prefixes with the original count expression repeated. Exclude conflicting same-cursor forms. Let existing recognized same-array inputs reach their legacy temporary-buffer path. Keep every legacy route and guard otherwise unchanged.
- [ ] Run `cargo test -p passes libc_replacer::tests -- --nocapture`. This verifies generated Rust typechecking, existing string projection tests, same-array behavior, and padded-object exclusions. Commit: `feat(libc): copy through existing cursor byte views`.

## Task 3: Support full-array offsets at the call site

**Files:** Extend `mem_utils.rs`; add tests in `tests.rs`.

**Interfaces:** Extend Task 2's `memcpy_byte_view` without changing its signature. Offset information is rendered into `slice`; no new general memory-view abstraction is needed.

- [ ] Add `test_memcpy_cursor_full_array_offsets`: a state with `[u8; 64]` and `[u8; 128]` fields, existing mutable state references, and an unrelated raw dereference in the same function. Exercise both destination and source full-array offsets with cursor counterparts. Assert the replacements survive the enclosing raw dereference, retain `(left as isize) as usize`, use suffix-then-prefix indexing, and introduce no offset/count bindings.
- [ ] Add `test_memcpy_cursor_offset_fallbacks`: raw offsets from an interior slice/cursor suffix that can validly be negative, offsets through a `u32` cast, effectful offsets, and fields reached by a newly introduced raw dereference. Assert memcpy remains for these new cursor combinations. Also exercise a cursor's own valid negative `offset_by` from a positive position: retain the cursor operation rather than converting it to suffix indexing.
- [ ] Run `cargo test -p passes libc_replacer::tests::test_memcpy_cursor_ -- --nocapture`. The newly supported raw-offset cases should fail before this task's code change.
- [ ] Recognize exactly an outer raw `.offset(k)` on a full byte-array base pointer with unchanged offset units. Use receiver HIR type to distinguish a full array from a slice; peel reference types without accepting raw-pointer dereferences. Apply the scalar eligibility rule to `k` and retain its original signed cast before `as usize`. Render the view with the existing slicing convention. Do not consult `current_fn_has_raw_deref` for this verified byte route; leave all old guards intact.
- [ ] Run `cargo test -p passes libc_replacer::tests -- --nocapture`, including `test_offset_memory_calls_use_slice_replacements` and `test_memcpy_autoref`. The latter remains supported through its existing legacy route. Commit: `feat(libc): copy cursor bytes into offset array fields`.

## Task 4: Execute transformed copies at boundaries

**Files:** Add `fixtures/memcpy_cursor.rs`; modify `tests.rs` only.

**Interfaces:** Add test-local `fn run_memcpy_runtime(code: &str)` and `test_memcpy_cursor_runtime`. It invokes the real libc replacement, verifies the eligible calls were replaced, typechecks the result, compiles that emitted u8-only fixture with the repository toolchain, then executes it. Use `std::process::Command` and a unique temporary directory; no dependency or general testing framework changes. Fail with compiler/runtime diagnostics and remove the temporary files after success.

- [ ] Create a self-contained fixture with faithful generated cursor operations, existing reference-backed state, and an assertion-driven `main`. Use data `[10, 20, 30, 40, 50]` with cursor position 1 and destination `[99; 6]`. A three-byte copy at destination offset 2 must yield `[99, 99, 20, 30, 40, 99]`; assert the cursor's current pointer/position is unchanged.
- [ ] Add empty copies with the source cursor at `base.len()` and the destination offset at its array length, plus a three-byte copy at destination offset 3 yielding `[99, 99, 99, 20, 30, 40]`. Cover mutable cursor destinations and a temporary mutable cursor reborrow, then use the original cursor again in the following statement. These cases must not panic or extend the borrow.
- [ ] Run `cargo test -p passes libc_replacer::tests::test_memcpy_cursor_runtime -- --nocapture`. Require both actual rewrite assertions and successful execution; merely executing the remaining libc memcpy is not sufficient. i8 behavior is covered by Task 2's typechecked bytemuck route and corpus tests rather than adding runtime dependency discovery here.
- [ ] Run the full libc test module once after the fixture/helper is complete. Commit: `test(libc): execute cursor memcpy boundary cases`.

## Task 5: Verify the measured opportunity and regressions

**Files:** No planned production changes. Create validation artifacts under a fresh `/home/ubuntu/crat-workspace/memcpy-cursor-validation-<implementation-revision>/` directory. Read the archived diagnosis but never edit or rerun its scripts in place.

**Interfaces:** Consume the implementation revision and frozen `crat` binary. Produce `manifest.json`, `results.json`, per-case adapter/owner inventories, runtime logs, and `REPORT.md`. Keep measured outcomes distinct from the 360-site target.

- [ ] Run from the implementation worktree, in order: `cargo fmt`, `cargo clippy --workspace --all-targets`, `cargo test --workspace`, and `cargo build --release --bin crat`. Review formatting changes and commit only relevant fixes before freezing the validated revision. New code changes restart affected checks; passing checks do not require repeated full runs without a reason.
- [ ] Create the isolated validation directory. Adapt a copy of archived `run_baseline.py` to `run_candidate.py`: use the archive manifest's exact 128 case paths, the existing pretranslated inputs, a fresh `candidate` output tree, and a frozen copy of the new release binary. Preserve the archived transform chain, including `enum`, and its pinned `transform.py`/`utils.py` for the SPHINCS comparison. Retarget the harness's `crat` link to the implementation worktree. Record full revision, binary/toolchain/script hashes, exact commands, and input hashes; compare those input hashes with the archive. Do not use an archived instrumented binary or rerun its counterfactual analyses.
- [ ] First run the new harness for case `005_sphincs_PQCgenKAT_sign_blake_128f_simple` through `bin`. Verify six removed cursor-source adapters: two hash-message and four update-function copies. If rejected, inspect the generated call against the existing eligibility rules before broadening anything. Then run `python3 run_candidate.py` for all 128 manifest cases, requiring 128 successful pipelines. The harness should retain the archive's `transform_tc(output, case, 'bin', False, True)` interface and full pointer-decision diagnostics.
- [ ] Adapt a copy of `inventory.py` to the new output directory. Compare every owner record/category/representation with the archive and compare pointer-stage Rust directly; it should be unchanged. Inspect libc-stage call sites and final generated application code separately. Report six removed cursor adapters in each of 60 Blake cases, zero such candidates in other families, 360 total replacements, and zero owner changes. Do not substitute textual `SliceCursor` counts or global raw-pointer counts for owner/site counts. Explain any additional legacy array replacements separately.
- [ ] Prepare an isolated runner containing only the corpus directories and tooling needed by the official scripts, excluding forbidden directories. `test.py` overwrites each runner case's `translated_rust`, so do not point it at the shared corpus. Confirm the CLI with `--help`, then run `python3 scripts/test.py <candidate-output> Test-Corpus/Public-Tests/P01_sphincs_plus/005_sphincs_PQCgenKAT_sign_blake_128f_simple --verbose`. Run all 128 SPHINCS cases with the same single-case interface, including library cases. For failures, run the frozen baseline output in that same isolated runner to separate existing failures from regressions; the old report did not establish runtime success.
- [ ] Follow the Crat test-workflow skill for wider public/hidden regression. In the isolated runner, confirm script CLI versions and point their `crat` resolution at the implementation checkout. Run `python3 scripts/transform_all.py <regression-output> libc --run-dependencies`, complete the remaining chain through `bin` (reuse completed predecessors where supported), then `python3 scripts/test_all.py <regression-output>`. Immediately run `python3 scripts/find_unsafe.py` and `python3 scripts/summarize_unsafe.py` before another test run replaces the measured trees. Use outside-sandbox execution for transform/test scripts. Compare any failures or unexpected unsafe-count increases against an explicitly pinned baseline.
- [ ] Write the final report with exact successes/failures, 120/240 candidate breakdown, owner counts by category, cursor text counts separately, ABI/boundary observations, and links to logs. Never report 360 verified wins solely from matching source patterns. If any candidate remains or required corpus input is unavailable, identify it explicitly and leave the corresponding acceptance item incomplete. Do not broaden sign/field/return/function-pointer scope to force completion.

## Self-review and handoff

Task 1 covers result semantics; Tasks 2–3 cover both measured obstacles, byte
types, casts, stable inline expressions, temporary lifetimes, and conservative
fallback; Task 4 checks actual boundary-copy behavior; Task 5 establishes pinned
metrics and regressions. Existing borrow promotion remains trusted throughout.

The implementer should keep these tasks sequential because they share the
matcher/emitter and tests. No product work or corpus runs are performed merely
by accepting this planning artifact. Ask the user to review the plan and choose
native execution or task-by-task subagents before starting implementation.
