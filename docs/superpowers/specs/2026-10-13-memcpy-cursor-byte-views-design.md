# Memcpy to copy_from_slice through existing byte views

Date: 2026-10-13

Status: in-chat design accepted, including the revised borrowing rule; written
specification only. Implementation has not started and requires separate approval.

## Intent and baseline

Remove unnecessary cursor-to-raw adapters at `memcpy` calls by recovering the
existing slice views and emitting `copy_from_slice`. Include offset destinations.
Keep the improvement in the libc replacer, without changing pointer owners.

The retained branch is `representation-aware-cursor-resolution`, based on
`cecfed7b3554ed016b1613c6ec8b5da4dacf4531`. Its worktree is
`/home/ubuntu/.config/superpowers/worktrees/crat/representation-aware-cursor-resolution`.
The discarded `blake-mask-cursor-proof` work must not be restored or assumed.

The revision-pinned investigation is recorded in
`/home/ubuntu/crat-workspace/sphincs-diagnosis-cecfed7b-20260928/REPORT.md`, with
the baseline manifest and outputs in the same directory. That report predates
the accepted expansion to all 360 memcpy candidates; this specification records
the current scope.

Across 128 SPHINCS cases, 60 Blake cases contain six cursor-source memcpy calls
each. The other families contain no such adapters.

| Group | Sites per Blake case | Total candidates | Current obstacle |
| --- | ---: | ---: | --- |
| `SPX_hash_message`, sources `R` and `pk` | 2 | 120 | Cursor source unrecognized |
| `blake256_update` and `blake512_update`, source `data` | 4 | 240 | Cursor source unrecognized; offset/raw-dereference guard |
| Total | 6 | 360 | Both obstacles must be addressed |

These are measured static candidates, not verified gains. The target is to
replace all 360 calls and remove their 360 cursor-source `.as_ptr()` adapters.
The expected change in cursor owner counts is zero. Cursor locals, parameters,
returns, fields, textual occurrences, and adapter occurrences remain separate
metrics. In particular, two copies from one `data` parameter are two sites, not
two owners.

## Accepted assumptions and boundaries

- Treat the original C program as UB-free. Its memcpy source and destination
  byte ranges therefore do not overlap.
- Trust existing promoted Rust references and generated cursor backing slices.
  Do not repeat borrow-promotion or whole-array alias analysis in the libc pass.
- A generated `SliceCursor` contains `&[T]`; `SliceCursorMut` contains `&mut [T]`.
  Their pointer and slice projections use the same base and current position.
  Recovering that slice view does not introduce a new backing-storage borrow
  eligibility requirement.
- Preserve evaluation, casts, cursor positions, and the lifetime of temporary
  values needed by the generated expression. Existing promotion does not remove
  expression-level reborrow and lifetime requirements.
- Do not infer that unsigned arithmetic cannot wrap, or that unsigned-to-signed
  casts preserve nonnegativity. Keep the bounded unsigned-expression improvement
  as a separate follow-up.

This change does not demote cursors, change signatures or C ABI wrappers, broaden
field/return/function-pointer demotion, reconstruct references from arbitrary
raw pointers, or modify `memmove`/`memset` policy. It does not add general sign,
range, alias, or borrow analysis.

## Recognition and eligibility

Add a memcpy-specific byte-copy route before the existing typed and object-copy
routes. Support initialized `u8` and `i8` storage. Reuse existing bytemuck support
for bit-preserving `i8` byte views; no new numeric or padded-object support is
needed.

| Input form | Recovered view |
| --- | --- |
| Array/slice `.as_ptr()` or source `.as_mut_ptr()` | Shared byte view |
| Writable array/slice `.as_mut_ptr()` | Mutable byte view |
| Generated cursor `.as_ptr()` | `.as_slice()` |
| Generated mutable cursor used as source | Shared projection, with existing temporary-lifetime handling |
| Generated mutable cursor `.as_mut_ptr()` used as destination | `.as_slice_mut()` |
| Full byte-array base pointer followed by `.offset(k)` | View starting at the evaluated offset |
| Already-sliced array/slice followed directly by `.as_ptr()`/`.as_mut_ptr()` | That existing view |

Reuse the typed cursor recognition and projection logic in
`crates/passes/src/libc_replacer/str_utils.rs`. Preserve its handling of mutable
cursor `offset_by` temporaries, including `as_deref()` where needed. Do not
recognize arbitrary user methods solely by their spelling, or change the global
array-pointer helper to treat cursors as indexable arrays.

Peel only pointer casts and parentheses whose removal preserves the recovered
byte address and offset units. Do not turn pointer/integer round trips or offsets
performed through a wider pointee type into byte indexing.

For a raw `.offset(k)` added to a recovered view, the new rule must establish
that the offset is expressible within that view. The required SPHINCS form starts
at a full byte-array field's beginning. Valid C pointer arithmetic on that array
excludes an offset before its beginning; no general sign proof is required.
Do not apply that argument to a slice starting inside a larger allocation, where
a negative raw offset can validly reach earlier elements outside the slice.
Unsupported raw-offset forms stay with the existing behavior. A cursor's own
`offset_by` operation keeps its existing base/position semantics; do not replace
it with unsigned indexing from its current suffix.

For the new route, raw dereferences elsewhere in the enclosing function are not
a rejection reason. Recognized array fields reached through existing promoted
references are eligible. Do not construct a new whole-object reference from a
raw pointer to make a destination eligible. Keep the existing raw-dereference
guards on the legacy typed/object-copy routes and other memory operations.

## Emission and borrowing

Representative input:

```rust
memcpy(
    __crat_borrowed_S.buf.as_mut_ptr().offset(left as isize) as *mut _,
    data.as_ptr() as *const _,
    fill as usize,
);
```

Representative output:

```rust
(&mut __crat_borrowed_S.buf)[(left as isize) as usize..][..fill as usize]
    .copy_from_slice(&data.as_slice()[..fill as usize]);
```

Preserve the original signed offset expression before converting its result to
an index. Preserve the original byte-count expression and casts. Use
suffix-then-prefix slicing so that the rewrite introduces no `start + count`
arithmetic. Both final slices have exactly the requested byte count. Neither
projection advances the cursor.

The hash-message sites have the following shape:

```rust
seed[..count].copy_from_slice(&R.as_slice()[..count]);
seed[start..][..count].copy_from_slice(&pk.as_slice()[..count]);
```

Use ordinary short reborrows of existing references. For SPHINCS,
`__crat_borrowed_S.buf` already projects through a mutable reference and `data`
already contains the shared backing slice. No additional disjoint-owner proof,
whole-array borrow analysis, or runtime overlap check is required.

Preserve the legacy recognized same-array temporary-buffer path. The new route
must not bypass it by emitting conflicting shared/mutable borrows of one place.
If two projections of the same mutable cursor would conflict, leave the new
cursor case unchanged. Distinct textual names are not an alias proof; the reason
for trusting independent promoted views is the existing representation invariant.
Do not add a new allocation strategy or `split_at_mut` framework in this change.

## Evaluation and result handling

Keep the new matcher deliberately restricted to stable operand places and
side-effect-free offset/count expressions. Allow recognized view operations
and cursor-offset operations that preserve the original cursor value and whose
temporary lifetime can be represented correctly. Reject arbitrary function
calls, assignments, state-mutating cursor operations, and `with_borrow` or
`with_borrow_mut` wrappers in the new route.

The builder should implement a conservative structural whitelist. Local values,
constants, fields through existing references, primitive casts, and primitive
arithmetic/bitwise expressions are sufficient for the measured SPHINCS forms.
Preserve wrapping operations verbatim when accepted. Exclude expressions whose
evaluation mutates or invalidates another operand; do not create a general
expression-staging analysis.

Prefer the original offset and count expressions directly in slice indexing,
as the existing memcpy emitter does. Offsets appear once each; the count may
appear twice. Permit repeated or reordered evaluation only when it preserves
behavior and does not conflict with the generated borrows. Stable scalar
expressions such as `fill as usize` and `(datalen >> 3) as usize` need no bindings.
Do not introduce unconditional offset/count temporaries.

Side-effect freedom alone does not guarantee borrow compatibility. For example,
inlining `dst.len()` as the count conflicts with the mutable destination borrow
in `(&mut *dst)[..dst.len()].copy_from_slice(&src[..dst.len()])`. For a supported
expression that needs a binding, evaluate it before the conflicting borrow while
preserving the original evaluation semantics. Otherwise, leave the unsupported
call unchanged; do not add a general expression-staging mechanism.

Keep any cursor temporary alive through the copy. Use collision-free names for
bindings that are actually needed. Keep mutable reborrows local to the copy
expression or its generated block; do not extend them into subsequent statements.

Only replace memcpy calls whose result is discarded as a semicolon statement.
Put this eligibility check at memcpy dispatch so a used-return call cannot fall
through to an existing unit-returning replacement. This is the one intentional
eligibility restriction shared with legacy memcpy routes: C memcpy returns its
destination pointer, whereas `copy_from_slice` returns unit. Supporting consumed
return values is deferred.

Zero-length copies through valid views and copies ending exactly at a view's
boundary must work. Do not manufacture references for arbitrary null/raw
pointers even when the count is zero. This route copies initialized bytes;
general memcpy of uninitialized storage is outside its supported subset.

## Implementation placement and fallback

- `crates/passes/src/libc_replacer/mem_utils.rs`: recognize byte operands, check
  local eligibility, and emit bounded copies.
- `crates/passes/src/libc_replacer/str_utils.rs`: minimally share existing cursor
  recognition/projection helpers if needed; retain existing string behavior.
- `crates/passes/src/libc_replacer/mod.rs`: require a discarded memcpy result.
- `crates/passes/src/libc_replacer/tests.rs`: focused rewrite and behavior tests.

For unsupported new forms, preserve the existing legacy decision; if no existing
route applies, keep memcpy. Do not broaden legacy typed, object, or raw-pointer
eligibility as a side effect. In particular, the byte route uses the original
byte count and does not cancel a wrapping multiplication by element size.

The builder may choose the smallest helper/data structure that retains the
operand type, projection, and offset information needed for emission. Do not
introduce a general memory-view framework or configuration option. Set dependency
flags only when a selected replacement needs them.

## Validation and acceptance

Use existing Crat test conventions. Add meaningful coverage for:

- Plain and offset byte-array destinations with immutable cursor sources,
  including functions with unrelated raw dereferences.
- `u8`/`i8` combinations, mutable cursor sources/destinations, and supported
  cursor temporaries that require careful reborrowing.
- Zero-length, one-past empty, and exact-end copies; verify copied bytes,
  unchanged surrounding bytes, and unchanged cursor position in runtime checks.
- Preservation of the original offset cast and byte-count arithmetic.
- Direct indexing of stable scalar offsets/counts without unnecessary bindings,
  plus binding or fallback when a count reads the mutably borrowed destination.
- Legacy same-array behavior and fallback for conflicting same-cursor borrows,
  interior negative raw offsets, unsupported raw pointers, side-effecting
  operands, borrow wrappers, and consumed memcpy results.
- Existing typed/object-copy and string-helper regressions, including padded
  object exclusions and the existing memory-operation tests.

After implementation, run `cargo fmt`, `cargo clippy --workspace --all-targets`,
and `cargo test --workspace`, plus the required corpus workflow. Transform the
128 SPHINCS cases from the existing pretranslated corpus using an isolated
harness/output directory and a manifest pinned to the implementation revision.
Do not overwrite the archived baseline or regenerate C2Rust inputs. Follow the
Crat corpus skills for targeted runtime vectors and the required wider regression
checks; never access `aws-translate` or `bundles`, or run the translation scripts.

Report per-case memcpy and cursor-adapter deltas, compile/runtime results, and
unchanged pointer owner representations by category. The intended result is all
360 measured candidates replaced, zero cursor-owner changes, and unchanged ABI
boundaries. If any candidate remains, report its exact unsupported form or
failure; do not silently lower the target or broaden analysis scope to force it.

## Decision record

The accepted borrowing revision removes the proposed second proof of whole-array
borrow eligibility. Cursor promotion and existing references already supply that
invariant. The remaining work is local view recovery and correct expression
generation. A focused rewrite is sufficient for the observed opportunity;
general sign/alias extensions and the bounded unsigned-expression proof are
separate work.
