# Shared Discarded-Result Detection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. The user previously selected native execution; preserve that preference. The user authorized execution on 2026-10-16.

**Goal:** Share discarded-result detection between memcpy and strncpy, including ordinary block tails, while preserving calls whose pointer results are consumed.

**Architecture:** Add one conservative structural query to the existing `utils::hir` module. The two libc dispatch sites consult it before their existing replacements; operand recognition, borrowing rules, and emitters stay unchanged.

**Tech Stack:** Rust, rustc-private HIR APIs, `nightly-2025-06-23`, existing compiler test harness and Python corpus scripts.

**Spec:** The design contract below records the proposed extension to the accepted [memcpy design](../specs/2026-10-13-memcpy-cursor-byte-views-design.md), specifically its direct-semicolon restriction. The conversation establishes shared HIR placement and the two callers. No separate analysis framework is proposed.

**Status:** Implementation and validation completed; records reconciled on 2026-10-19. Final independent review completed with no findings. Starting HEAD: `a5994d77da1ab593383cba878b34eee33224adae`, worktree `/home/ubuntu/.config/superpowers/worktrees/crat/representation-aware-cursor-resolution`.

## Design contract

Expose this query from `crates/utils/src/hir.rs`, following that module's expression-first conventions:

```rust
pub fn is_expr_result_discarded<'tcx>(expr: &rustc_hir::Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool;
```

`true` means this limited structural walk proves the value reaches a semicolon statement. `false` means consumed or unsupported, not necessarily used. This is a result-context query, not permission to remove evaluation, alter side effects, or change arbitrary destructor behavior.

| Context encountered while walking outward | Result |
|---|---|
| `StmtKind::Semi` containing the current expression | True |
| Current expression is exactly the tail of an ordinary or unsafe block | Continue through that block's owning expression |
| Block is labeled or `targeted_by_break` | False; break values can constrain its type |
| Assignment, local initializer (including `let _ = ...`), return, call argument, cast, or break value | False |
| Function/closure/async body boundary, if/match/loop expression, compiler wrapper, or any other unhandled node | False |

Check child IDs at each transition. Do not treat an arbitrary descendant of a discarded block as discarded. HIR parentheses need no source-text handling. Handle the actual `Node::Block` / owning `ExprKind::Block` parent structure, and stop conservatively if it does not match. Never walk from a body root into the context where its function or closure is used.

For example, permit replacing the inner call here:

```rust
{
    let borrowed = ctx.as_deref_mut().unwrap();
    memcpy(/* existing eligible operands */)
};
```

Keep it when the enclosing block is assigned or returned. Also keep a tail call in `'out: { if cond { break 'out pointer; } memcpy(...) };`: replacing only its tail with unit can conflict with the pointer-valued break.

Use the same query at the existing memcpy and strncpy gates. Do not add gates to other libc operations in this change. Preserve argument checks, AST-to-HIR failure fallback, operand evaluation, and existing transform implementations.

## Global Constraints

- Native execution is authorized; preserve the existing worktree.
- No changes to cursor recognition, byte-copy eligibility, scalar staging, pointer owners, ABI, sign analysis, or memmove/memset policy.
- Keep the helper free of libc names, cursor types, byte-copy assumptions, caches, and configuration.
- Scope the new accepted contexts to ordinary/unsafe block tails ending in a direct semicolon statement. No general value-use or control-flow analysis.
- Never access `aws-translate` or `bundles`; never run `scripts/translate.py` or `scripts/translate_all.py`.
- Preserve existing diagnosis and validation directories. Use fresh output and runner directories; test scripts overwrite runner `translated_rust` trees.

## Review Focus

- An ancestor semicolon does not discard values used inside its expression; cover assignments, casts, and call arguments (Tasks 1–2).
- Labeled/try blocks can unify tail and break types; reject break-targeted blocks (Tasks 1–2).
- If/match/loop result types constrain their children even when the outer expression is discarded; stop at those boundaries (Task 1).
- Closure/body results remain consumed by that body even when the enclosing closure or invocation is discarded (Task 1).
- Both libc callers must retain used pointer results, including legacy memcpy object-copy routes (Task 2).

## Task 1: Add the shared structural query

**Files:** Modify `crates/utils/src/hir.rs`; create `crates/utils/src/hir/tests.rs` and register it with `#[cfg(test)] mod tests;`.

**Interfaces:** Produces `utils::hir::is_expr_result_discarded` with the signature and conservative contract above. No dependency changes.

- [x] Add compiler-backed tests using `crate::compilation::run_compiler_on_str`. Locate calls to a fixture `fn marker() -> usize { 7 }` by resolved callee identity, and assert both the number of visited marker calls and their classifications. Walk nested bodies explicitly for closure tests; missing a call must fail the test rather than pass vacuously.
- [x] `test_is_expr_result_discarded_blocks`: expect true for `marker();`, `{ marker() };`, nested ordinary blocks, and an unsafe block containing a setup statement and a marker tail. Include parentheses around the call. Expect false for a function returning `usize` whose body tail is `{ marker() }`.
- [x] `test_is_expr_result_discarded_consumers`: expect false for assignment, typed/untyped initialization, `let _ = marker();`, explicit return, `consume({ marker() });`, and `({ marker() } as u64);`. Each snippet must compile before querying HIR.
- [x] `test_is_expr_result_discarded_boundaries`: expect false for a marker tail in a labeled block with a value-carrying break, if/match arms with another usize-valued arm, a loop's break value, and a closure body whose enclosing closure/invocation is discarded. A direct `marker();` inside such a body should still return true because its own statement discards it.
- [x] Run `cargo test -p utils hir::tests::test_is_expr_result_discarded`. Expected RED: missing helper before implementation; after adding its declaration/body, check that nested block cases exercise actual HIR parent transitions.
- [x] Implement the small outward walk using the existing rustc HIR APIs. Treat `targeted_by_break` as a rejection and require an unlabeled block-owning expression. Return false on unsupported parents or exhausted traversal; no panic for unknown contexts.
- [x] Run `cargo test -p utils hir::tests::test_is_expr_result_discarded`, then `cargo test -p utils`. Expected: all new classifications and existing utils tests pass.
- [x] Commit: `feat(utils): recognize discarded results through ordinary block tails`.

## Task 2: Share the query between memcpy and strncpy

**Files:** Modify `crates/passes/src/libc_replacer/mod.rs` and `crates/passes/src/libc_replacer/tests.rs`.

**Interfaces:** Consumes Task 1's helper. Retains all existing `transform_memcpy` and `transform_strncpy` signatures and argument/operand checks.

- [x] Add `test_memcpy_discarded_block_results`: eligible byte-array and cursor copies wrapped in one/nested ordinary blocks and an unsafe block; include the `let borrowed = ...; memcpy(...)` shape. Use `run_test` / existing cursor fixtures to assert replacement and typecheck emitted Rust. Assert the original call expression is absent, not merely that some `copy_from_slice` exists.
- [x] Add `test_strncpy_discarded_block_results`: wrap the existing short-slice strncpy fixture in ordinary/nested/unsafe blocks. Require the existing bounded copy and padding output and absence of the original call; typecheck the result.
- [x] Add `test_libc_block_results_are_preserved`: for both APIs, retain calls inside a block assigned to a pointer, returned as a function tail, passed to a consumer, or used as the tail of a labeled block with a pointer-valued break. For memcpy, cover numeric-array and object-to-byte routes using the existing used-result fixture. All emitted results must still typecheck.
- [x] Run `cargo test -p passes libc_replacer::tests::test_memcpy_discarded_block_results` and `cargo test -p passes libc_replacer::tests::test_strncpy_discarded_block_results`. Expected RED: eligible block-tail calls remain unreplaced under the current direct-parent gates. Negative cases should already pass.
- [x] Replace only the duplicate direct-semicolon predicates at memcpy and strncpy dispatch with the shared query, retaining the AST-to-HIR lookup and all other conditions.
- [x] Run `cargo test -p passes libc_replacer::tests`. Expected: new tests and existing cursor/borrow/used-return/string regressions pass; direct semicolon behavior remains supported.
- [x] Commit: `fix(libc): share discarded-result checks for memcpy and strncpy`.

## Task 3: Measure recovered calls and regression behavior

**Files:** Update the relevant result-handling paragraphs of the accepted memcpy spec, preserving its historical results and other constraints. Write new validation artifacts under `/home/ubuntu/crat-workspace/discarded-results-validation-<revision>/`; do not overwrite the completed memcpy report.

**Interfaces:** Consumes a frozen implementation binary. Produces a revision/toolchain/script/input manifest, per-case call differences, pointer-owner comparison, runtime logs, and `REPORT.md`.

- [x] Run `cargo fmt`, `cargo clippy --workspace --all-targets`, `cargo test --workspace`, and `cargo build --release --bin crat`. Expected: formatting clean, no new warnings, passing tests/build. Freeze the committed product revision and binary after any fixes.
- [x] Use `/home/ubuntu/crat-workspace/memcpy-cursor-validation-de8934c7` as the prior implementation baseline. Its `final-manifest.json` pins `d4b91111` and its binary; verify the starting `a5994d77` differs only in documentation. The prior report, call-deltas inventory, and frozen io inputs supply the exact 128 SPHINCS paths and 512 known block-tail calls. Copy/adapt the harness into the new directory and record hashes and commands.
- [x] Regenerate libc and all remaining stages through bin for case 005, then all 128 SPHINCS cases. Reuse frozen io predecessors because this helper is consumed only by libc dispatch. Require successful pipelines, all 512 known calls recovered, and all 360 cursor adapters still absent. Classify any additional memcpy or strncpy replacements separately; do not infer gains solely from a global count.
- [x] Compare source-owner diagnostics and the final declaration census against the prior baseline; require unchanged owners/signatures. Expected SPHINCS memcpy delta: −512 versus the completed implementation and −360 versus `cecfed7b`, subject to measured additional replacements. Report differences rather than forcing either target.
- [x] Prepare a fresh isolated runner using the corpus tooling and allowed directories. Run all 128 SPHINCS cases through the official per-case `test.py` interface. Expected: 128 pass; compare any failures against the frozen prior binary/output in the same runner.
- [x] Follow `crat-test-workflow` for the 367-case public/hidden regression: run official transformations from libc through bin using preserved predecessors, then `test_all.py`, immediately followed by `find_unsafe.py` and `summarize_unsafe.py`. Use required outside-sandbox execution. Compare against the prior 365 tested/2 skipped cases, 2,753 passed/234 skipped vectors, and 22,679 unsafe occurrences. Explain all failures, new skips, or per-feature increases; distinguish memcpy and strncpy changes.
- [x] Write the report with exact recovered call counts, unchanged cursor gains/owner decisions, test outcomes, skips, and unsafe deltas. Update the memcpy spec's gate description to the shared structural rule and link the new report without rewriting the old validation history.
- [x] Commit relevant documentation: `docs: record shared discarded-result handling and validation`.

## Handoff

The helper's structural contract is the reusable part; libc-specific replacement eligibility stays local. Task 2 depends on Task 1, and Task 3 validates their combined behavior. Native execution with one final whole-change review fits these small dependent tasks. The final reviewer should inspect parent/child identity checks and type-constraining control-flow boundaries in particular.

Self-review: the design contract maps to Task 1, both existing consumers and return preservation map to Task 2, and the measured opportunity/regression requirements map to Task 3. Every Review Focus item has a named test. Implementation and validation are complete. The final independent review found no Critical, Important, or Minor issues; no implementation work remains.

## Execution results

Product revision `624bb8e9` recovered all 512 known SPHINCS block-tail memcpy calls and eight additional copies in `memcpy_fun_buffers`. The prior 360 cursor-adapter removals and all pointer owners/final SPHINCS declarations remain unchanged. Workspace tests: 1,471 passed. Wider runtime: 365 cases tested, 2 skipped; 2,753 vectors passed, 234 skipped, no failures. Total unsafe occurrences decreased by 516; two raw-pointer count reads were duplicated by the existing legacy emitter, as explained in the [validation report](/home/ubuntu/crat-workspace/discarded-results-validation-624bb8e9/REPORT.md).

Execution adjustment: value-carrying breaks are tested directly through the HIR query. The pre-existing THIR-to-MIR mapper rejects these inputs before libc dispatch, so the libc integration fixture uses a labeled block without a value-carrying break. No mapper changes were made. A runner-overlap failure in the initial case-132 check was resolved by isolated retries of the final six cases; initial logs and clean results are both retained.

## Final review and handoff

Final independent review of `a5994d77..497393c9` completed on 2026-10-19 with no findings. [Review and scope rulings](/home/ubuntu/crat-workspace/discarded-results-validation-624bb8e9/final-review.md) record the two areas not judged: general value-carrying-break support and general correctness of unchanged emitters. Both remain outside this approved change. Direct HIR rejection coverage is retained for value-carrying breaks; no emitter redesign was introduced. Deferred minor findings: none.

All three tasks are complete. The execution ledger and native execution artifacts are archived with the validation report. The branch and worktree are retained for review; no merge or push was performed.
