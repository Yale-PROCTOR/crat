# Canonical Rewriter Specification (Current Checked-In Behavior)

## 0) Status and Scope
- This document describes the **current checked-in behavior only** of `crates/pointer_replacer/src/rewriter`.
- It is implementation-canonical for:
  - `crates/pointer_replacer/src/rewriter/mod.rs`
  - `crates/pointer_replacer/src/rewriter/decision.rs`
  - `crates/pointer_replacer/src/rewriter/collector.rs`
  - `crates/pointer_replacer/src/rewriter/transform/mod.rs`
- It does **not** describe planned behavior that is not implemented.

## 1) Module and Function Responsibilities

### `mod.rs`
- `Analysis`
  - Holds rewriter inputs actually consumed by the current decision/rewrite flow:
    - promoted mut refs
    - promoted shared refs
    - mutability analysis result
    - fatness analysis result
    - Andersen-derived param alias map
    - output-parameter facts
    - optional solidified ownership facts
    - offset-sign result
- `Config`
  - `c_exposed_fns`; passed through to Andersen configuration.
  - Test-only field `force_ownership_analysis_failure`; forces the ownership-analysis fallback path for regression coverage.
- `replace_local_borrows(config, tcx) -> (String, bool, bool)`
  - End-to-end driver: build AST, run analyses, compute output-parameter facts, attempt ownership-analysis solidification, construct `TransformVisitor`, mutate AST, render source, optionally append `slice_cursor` module, return feature flags.
- `find_param_aliases(pre, points_to, tcx)`
  - Builds per-function param alias clusters by intersecting points-to sets across call-argument pairs.
- `slice_cursor_mod_str()`
  - Returns the generated `crate::slice_cursor` runtime module source text.

### `decision.rs`
- `PtrKind`
  - Current variants:
    - `OptRef(bool)` (`Option<&T>` / `Option<&mut T>`)
    - `Raw(bool)` (`*const T` / `*mut T`)
    - `Slice(bool)` (`&[T]` / `&mut [T]`)
    - `SliceCursor(bool)` (`SliceCursorRef<'_, T>` / `SliceCursor<'_, T>`)
- `DecisionMaker::new(analysis, did, tcx)`
  - Materializes per-local facts for one function:
    - mutability-by-local
    - array/fatness-by-local
    - promoted mut/shared sets
    - `needs_cursor` set derived from offset-sign facts via THIR->MIR binding mapping
- `DecisionMaker::decide(local, decl, aliases) -> Option<PtrKind>`
  - Core precedence-ordered local decision algorithm.
- `SigDecisions::new(rust_program, analysis)`
  - Produces per-function input/output signature rewrite decisions.
  - Disables signature rewrites for functions used as function pointers.

### `collector.rs`
- `collect_fn_ptrs(rust_program)`
  - Finds local functions used as function pointers by scanning HIR for:
    - `ExprKind::Cast(inner, ty)` where `ty` is `TyKind::BareFn`
    - `inner` resolves to local `Fn`/`AssocFn`
- `collect_diffs(rust_program, analysis) -> FxHashMap<HirId, PtrKind>`
  - Computes local rewrite decisions and maps MIR locals back to HIR binding IDs.
  - Skips input locals for functions used as function pointers.

### `transform/mod.rs`
- `TransformVisitor`
  - Applies signature rewrites (`SigDecisions`) + local rewrites (`ptr_kinds`) and expression-level conversions.
  - Tracks `bytemuck` and `slice_cursor` feature usage flags.
- Major entry points:
  - `visit_item` (signature types)
  - `visit_local` (local type annotations + initializer conversion)
  - `visit_expr` (assignments/calls/methods/returns/deref and pointer adaptation)
  - `transform_ptr` (conversion engine)

## 2) End-to-End Pipeline in `replace_local_borrows`
1. Build expanded AST (`utils::ast::expanded_ast`) and AST->HIR map.
2. Remove unnecessary AST items (`remove_unnecessary_items_from_ast`).
3. Run Andersen points-to:
   - `pre_analyze`
   - `analyze`
4. Derive parameter alias map via `find_param_aliases`.
5. Enumerate crate owners into `RustProgram { tcx, functions, structs }` by scanning HIR owners:
   - include `ItemKind::Fn`
   - include `ItemKind::Struct`
6. Run analyses used by rewriter:
   - mutability analysis
   - output-parameter analysis
   - attempted ownership-analysis solidification (`None` if unavailable or test-forced off)
   - source-variable grouping postprocessing
   - promoted mutable/shared reference extraction
   - fatness analysis
   - offset-sign analysis
7. Build `Analysis` with the eight fields listed in Section 1.
8. Construct `TransformVisitor::new(&input, &analysis_results, ast_to_hir)`:
   - computes `sig_decs = SigDecisions::new(...)`
   - computes `ptr_kinds = collect_diffs(...)`
9. Mutate AST (`visitor.visit_crate(&mut krate)`).
10. Render rewritten crate (`pprust::crate_to_string_for_macros`).
11. If `visitor.slice_cursor` is true, append `slice_cursor_mod_str()`.
12. Return `(rewritten_code, visitor.bytemuck.get(), slice_cursor_used)`.

## 3) Decision Logic (`decision.rs`)

### 3.1 Decision Inputs
For one function (`did`), `DecisionMaker::new` computes:
- `mutable_pointers[local]`:
  - `true` if any mutability fact for that local is mutable.
- `array_pointers[local]`:
  - uses only the first available fatness fact (`iter().next()`); sets `true` only if that first fact is `is_arr()`, otherwise `false`.
- `_owning_pointers[local]`:
  - top-level owning bit from solidified ownership facts when available; otherwise `false`.
- `_output_params`:
  - dense bitset derived from output-parameter facts for the function.
- `promoted_mut_refs` / `promoted_shared_refs`:
  - dense bitsets keyed by MIR `Local`.
- `needs_cursor`:
  - local requires cursor when offset-sign facts for its HIR binding report `needs_cursor()`.

Current consequence:
- `_owning_pointers` and `_output_params` are threaded into `DecisionMaker` but are not yet consulted by `decide`.

### 3.2 Branch-Ordered Precedence (`DecisionMaker::decide`)
The following table is exact branch order.

| Order | Condition | Output |
|---|---|---|
| 1 | `unwrap_ptr_from_mir_ty(decl.ty)` fails | `None` |
| 2 | pointee is `c_void` OR file-like type | `Some(Raw(decl mutability))` |
| 3 | alias cluster exists and any member (including `local`) is mutable | `Some(Raw(mutable_pointers[local]))` |
| 4a | `array_pointers[local]` and local in promoted shared set and `needs_cursor` | `Some(SliceCursor(false))` |
| 4b | `array_pointers[local]` and local in promoted shared set and not `needs_cursor` | `Some(Slice(false))` |
| 4c | `array_pointers[local]` and local in promoted mut set and `needs_cursor` | `Some(SliceCursor(true))` |
| 4d | `array_pointers[local]` and local in promoted mut set and not `needs_cursor` | `Some(Slice(true))` |
| 4e | `array_pointers[local]` and not promoted | `Some(Raw(mutable_pointers[local]))` |
| 5 | non-array and local in promoted shared set | `Some(OptRef(false))` |
| 6 | non-array and local in promoted mut set | `Some(OptRef(true))` |
| 7 | `decl.ty.is_raw_ptr()` | `Some(Raw(mutable_pointers[local]))` |
| 8 | otherwise | `None` |

Notes:
- `unwrap_ptr_from_mir_ty` treats both raw pointers and references as pointer-like for decision purposes.
- Alias rule is intentionally conservative and precedes array/ref promotion.

### 3.3 Signature Decision Rules (`SigDecisions::new`)
1. Compute `fn_ptrs = collect_fn_ptrs(rust_program)`.
2. For each function `did`:
   - If `did in fn_ptrs`:
     - `input_decs = vec![None; input_arity]`
     - `output_dec = None`
   - Else:
     - For each parameter local (`_1..` up to input arity), run `DecisionMaker::decide`.
     - For return local `_0`, run `decide` and keep only raw:
       - `Some(Raw(m)) -> Some(Raw(m))`
       - any other result -> `None`

Current consequence: non-raw return signature rewrites are intentionally disabled.

## 4) `SigDecisions` and `collect_diffs` Interaction
- `TransformVisitor::new` computes both from the same `Analysis` snapshot.
- `SigDecisions` drives:
  - function signature parameter/return type rewriting (`visit_item`)
  - call-argument target kind selection (`visit_expr` call branch)
  - call-site return mutability override when callee output decision is `Raw(m)`.
- `collect_diffs` drives:
  - local variable type rewrite (`visit_local`)
  - source-kind lookup for path-based conversions (`transform_ptr` when base is local path).

`collect_diffs` details:
- For each function, compute local decisions with `DecisionMaker`.
- Build `local -> hir_binding` map by reversing THIR->MIR binding map; this assumes 0/1 binding per local, but collisions are not explicitly rejected (hash-map overwrite semantics apply if they occur).
- If function is used as function pointer, skip input locals by starting iteration at `1 + input_len`.
- Insert only when both a decision and HIR binding exist.

Practical result for function-pointer-used functions:
- signatures stay unchanged (`SigDecisions` all `None`)
- parameter locals are not added to `ptr_kinds` (`collect_diffs` skip)
- conversions that need a local-path `ptr_kinds` source kind for those params use fallback/type-driven paths; this often becomes raw-style handling but is expression-shape-dependent.

## 5) AST Mutation Behavior (`transform/mod.rs`)

### 5.1 `visit_item`
- `ItemKind::Impl(_)` is returned early (impl items/methods are not visited by this pass).
- For `ItemKind::Fn`:
  - Fetch `SigDecision` for this function.
  - For each parameter:
    - `OptRef(m)` -> rewrite to `Option<&{mut?} T>` via `mk_opt_ref_ty`; force binding pattern mutable.
    - `Slice(m)` -> rewrite to `&{mut?}[T]` via `mk_slice_ty`.
    - `Raw(m)` -> rewrite to `*{mut|const} T` via `mk_raw_ptr_ty`.
    - `SliceCursor(m)` -> rewrite to cursor type via `mk_cursor_ty`; set `slice_cursor = true`.
    - `None` -> keep as-is.
  - Return type rewrite occurs only when `sig_dec.output_dec == Some(Raw(m))` and return AST is explicit type.

### 5.2 `visit_local`
- For let-bindings with `ptr_kinds[hir_id]`:
  - Set `local.ty = Some(...)` to the selected pointer-kind type (`OptRef`/`Slice`/`Raw`/`SliceCursor`) even when the original binding had no explicit type annotation.
  - If local has initializer (`Init` / `InitElse`), run `transform_rhs` to convert RHS expression to LHS kind.

### 5.3 `visit_expr` major cases
- Assignment (`ExprKind::Assign`)
  - Compute LHS target kind:
    - if LHS is path and resolves to a local HIR id -> use direct index `self.ptr_kinds[&hir_id]` (not `get`); this can panic if the id is missing from `ptr_kinds`
    - else fallback `Raw(lhs mutability)`
  - Convert RHS with `transform_rhs`.
  - Special case for `SliceCursor` self-assign with single `offset` projection:
    - `p = p.offset(k)` -> `p.seek((k) as isize)`
- Pointer comparisons (`== != < <= > >=`)
  - Convert both operands in raw context before compare.
- Function calls (`ExprKind::Call`)
  - If direct local callee path, use `sig_decs` parameter decisions for each arg.
  - Otherwise fallback per-arg to `Raw(get_mutability_decision(..) or type mutability)`.
  - Run `hoist_opt_ref_borrow` post-pass to reduce repeated mutable deref borrow conflicts.
- Method call `is_null`
  - local `OptRef` receiver -> rename to `is_none`
  - local `Slice` / `SliceCursor` receiver -> rename to `is_empty`
  - `Raw` -> unchanged
- Method call `offset_from`
  - force receiver and argument through raw-pointer conversion.
- Return (`ret expr`)
  - only for raw-pointer function outputs: convert return expr with `sig_decs.output_dec` if present, else raw mutability fallback.
- Unary deref (`*p`)
  - Uses expression context (`Lvalue/Rvalue/AddrTaken`) to choose target mutability.
  - If source is cursor with exactly one offset projection, emits indexed access directly.
  - Otherwise transforms pointer and post-adjusts:
    - deref of `OptRef` -> `.unwrap()`
    - deref of `Slice` -> `[0]`
    - deref of `SliceCursor` -> `[0 as usize]`

### 5.4 Statement flattening (`flat_map_stmt`)
- Rewrites assignment pattern:
  - `lhs = &{mut?}(method_call(...))`
- Into two statements:
  - temp let binding for method call result
  - assignment from temp reference

## 6) Pointer Conversion Engine (`transform_ptr`)

### 6.1 Normalization and decomposition
- Recursively normalizes `if/else` and trailing-expression blocks so conversion is applied to branch results.
- Builds `PtrExpr` decomposition:
  - base kind: `Path`, `Alloca`, `ByteStr`, `Zero`, `Array`, `Other`
  - projection chain: `Offset`, `Cast`, `IntegerOp`, `IntegerBinOp`
  - flags: `addr_of`, `as_ptr`, `cast_int`
- Recognized pointer-expression constructors include:
  - method `offset`
  - method `as_ptr` / `as_mut_ptr` (single-use flag; repeated chaining is rejected)
  - `wrapping_add` / `wrapping_sub` as integer projections
  - `usize` binary ops as integer-bin projections (only `&` and `|` are supported later; other ops panic during emission)
  - alloca-like pattern `last[_mut]().unwrap()` captured as base kind `Alloca`
- Cast handling:
  - each cast is pushed into projections
  - cast-to-`usize` additionally marks `cast_int=true`, which is only supported for raw-target conversion.

### 6.2 Early zero/null conversion
When parsed pointer expression is literal zero with no projections:
- target `SliceCursor(m)` -> `SliceCursor::empty()` / `SliceCursorRef::empty()`
- target `Slice(m)` -> `&mut []` / `&[]`
- target `OptRef(_)` -> `None`
- target `Raw(m)` -> `std::ptr::null_mut()` / `std::ptr::null()`
- deref context -> keep as `Raw`

### 6.3 Special source forms
- Integer-cast pointer pipelines (`cast_int=true`)
  - supported only in raw target context; other contexts panic.
- `addr_of` base (`&x`, `&mut x`)
  - direct conversions to raw/optref/slice/cursor
  - bytemuck path for same-size numeric casts
  - pointer-arithmetic projections on addr_of are handled by creating/transforming slice expressions; unsupported complex projections fall back to raw.
- `as_ptr` / `as_mut_ptr` on non-raw bases
  - converted through slice/container semantics, then adapted to target kind.
- Byte string literals
  - raw: unchanged
  - optref/slice/cursor: shared-only (`m == false`) with optional `bytemuck::cast_slice` for non-`u8` numerics
  - deref context panics
- Raw-to-slice/cursor null/side-effect behavior:
  - in `slice_from_raw` and `cursor_from_raw`, method-call roots `offset`, `as_ptr`, `as_mut_ptr` skip null checks (explicit non-null assumption)
  - otherwise, if source has no side effects, emit inline `is_null()` guard with empty slice/cursor fallback
  - if source has side effects, hoist once into `let _x = ...` and guard on `_x.is_null()` to avoid duplicate evaluation
  - all successful raw->slice/cursor materializations use fixed length sentinel `100000`.

### 6.4 Source-kind/target-kind conversion matrix (local path bases)
This matrix is for the branch where `PtrExpr` base resolves to local path with known `ptr_kinds`.

| Source kind | Target `Raw` | Target `OptRef` | Target `Slice` | Target `SliceCursor` |
|---|---|---|---|---|
| `Raw` | direct / mutability cast | `opt_ref_from_raw` | `slice_from_raw` | `cursor_from_raw` |
| `OptRef` | `raw_from_opt_ref` | `opt_ref_from_opt_ref` | `panic!` | `panic!` |
| `Slice` | `raw_from_slice_or_cursor` | `opt_ref_from_slice_or_cursor` | `plain_slice_from_slice` | `cursor_from_plain_slice` |
| `SliceCursor` | `raw_from_slice_or_cursor` | `opt_ref_from_slice_or_cursor` (offset-only fast path uses `as_slice{_mut}`) | `cursor_or_slice_to_slice_expr` | `cursor_from_slice_or_cursor` (+ possible `to_ref_cursor`/`fork`) |

`raw_from_opt_ref` foreign-type note:
- if RHS inner type is `ty::Foreign`, conversion uses an explicit `match` (`Some(x) => *x as *...`, `None => null`) rather than the normal `.as_deref[_mut]().map_or(...)` path.

Deref context behavior:
- `Deref` targeting `Raw/OptRef/Slice` reuses corresponding conversions.
- `Deref` on `SliceCursor` uses `cursor_from_slice_or_cursor_inner(..., is_plain_slice=false)` then indexing logic in `visit_expr`.

### 6.5 General fallback path
If no local-path kind match applies:
- infer mutability from base raw/array type (with array-path deref inspection)
- if callee return signature mutability was rewritten to raw, override fallback mutability accordingly
- convert to requested target using `opt_ref_from_raw`, `slice_from_raw`, `cursor_from_raw`, or raw cast fallback.

### 6.6 Mutability Heuristics Used by Call/Deref Rewrites
- `get_mutability_decision(hir_expr)`:
  - strips leading `.offset(...)` receivers to the root expression
  - if root is a local path with `ptr_kinds` entry, returns that kind mutability
  - otherwise returns `None` (caller falls back to type mutability).
- `expr_ctx(hir_expr)` classifies expression usage as:
  - `Lvalue`
  - `Rvalue`
  - `ImmediatelyAddrTaken`
  - `AddrTaken(bool mut)`
- `expr_ctx` walks HIR parents and has targeted handling for:
  - `Assign` / `AssignOp`
  - indexing base vs index position
  - `AddrOf`
  - method calls (`as_ptr`, `as_mut_ptr`, and `set_*` treated as address-taking).

## 7) Conservative Fallbacks and Known Limitations
1. Return borrow inference is absent.
- `SigDecisions` only keeps `output_dec = Some(Raw(_))`; non-raw returns are dropped.

2. Ownership/output-parameter analysis is not consumed by current rewriter decisions.
- `Analysis` in `rewriter/mod.rs` now carries output-parameter facts and optional solidified ownership facts.
- Current M2 behavior still does not consult those facts when producing rewrite decisions.
- If ownership analysis is unavailable, the rewriter continues with `ownership_schemes = None`.

3. `ItemKind::Impl(_)` is skipped in `visit_item`.
- Impl methods are not rewritten by this pass.

4. Function-pointer-use detection is narrow.
- Only explicit `fn_item as bare_fn_type` cast patterns are recognized by `collect_fn_ptrs`.

5. Length fallback often uses a fixed sentinel (`100000`) when concrete length is unavailable.
- Appears in raw->slice/cursor materialization and several non-numeric cast fallback conversions.
- Example emitted pattern: `std::slice::from_raw_parts_mut(ptr, 100000)`.

6. Multiple conversion branches intentionally panic on unsupported shapes.
- Examples:
  - integer-cast pointer rewrite requested into non-raw context
  - target slice/cursor from `OptRef` source in local-path matrix
  - byte-string deref context

7. `collect_diffs` only rewrites locals that have at least one mapped HIR binding.
- Locals without binding mapping do not get `ptr_kinds` entries.
- Duplicate reverse-map collisions (multiple bindings to one local) are not guarded; hash-map collection would keep the last one seen.

8. `hoist_opt_ref_borrow` only hoists under a narrow pattern.
- It detects `*arg.as_deref_mut().unwrap()` style shapes and rewrites selected repeated mutable borrows.
- candidate selection iterates hash-map entries and uses `break` when first entry is non-qualifying; this makes hoisting of later candidates iteration-order dependent.

9. Alias conservatism can force raw even when other facts could allow higher-level types.
- Any mutable alias in the alias cluster triggers raw for that local.

10. Hard raw exceptions are always applied first.
- `c_void` and file-like pointees are always `Raw`.

11. Some paths use direct `ptr_kinds` indexing (`[]`) rather than `get`.
- Assignment-LHS resolution can index directly when a local HIR id is found.
- Fallback mutability inference for array+deref roots (`PathOrDeref::Deref`) also indexes directly.
- `is_base_not_a_raw_ptr` deref-path handling indexes directly as well.
- Missing entries in those paths can panic.

## 8) Test Mapping (Current)

### 8.1 Rewriter behavior tests
- File: `crates/pointer_replacer/src/tests.rs`
- Harness `run_test`:
  - runs `replace_local_borrows`
  - type-checks rewritten output
  - asserts include/exclude substrings in emitted source
- Covered rewriter areas include:
  - cross-kind assignment conversions
  - bytemuck and non-bytemuck cast paths
  - `addr_of`, `as_ptr`, byte-string conversions
  - pointer comparisons, call argument adaptation, return adaptation
  - null handling, `if/else` and block expression normalization
  - raw mutability casts and call-site return mutability propagation
  - ownership-analysis-fallback equivalence via test-only forced failure

### 8.2 Ownership analysis tests in same file
- Module: `ownership_analysis` inside `tests.rs`
- Validates ownership and output-param analyses (not rewriter mutation).
- Also includes a MIR-source regression guard over the ownership/output guarded paths.

### 8.3 B02 test suite
- File: `crates/pointer_replacer/src/analyses/B02_tests/mod.rs` + case modules.
- Current checks are ownership-analysis/candidate validation and aggregated stats; this suite does not currently execute the rewriter transform path.

### 8.4 Standard commands used for validation
- `cargo test -p pointer_replacer`
- `cargo test -p pointer_replacer analyses::B02_tests -- --nocapture`
- `cargo test -p pointer_replacer ownership_analysis::malloc_source_marks_return_as_owning`
- `cargo test -p pointer_replacer ownership_analysis::free_sink_clears_ownership_before_return`
- `cargo test -p pointer_replacer ownership_analysis::solidify_marks_return_local_as_owning_for_malloc`
- `cargo test -p pointer_replacer ownership_analysis::mutable_pointer_to_pointer_argument_becomes_output_param`
- `! rg -n "optimized_mir\\(" crates/pointer_replacer/src/analyses/output_params crates/pointer_replacer/src/analyses/ownership crates/pointer_replacer/src/analyses/B02_tests/mod.rs crates/pointer_replacer/src/tests.rs`

## 9) Maintenance Checklist for Spec Sync
When rewriter behavior changes, update this document in the same change set.

Checklist:
1. Update Section 1 if module API/function responsibilities changed.
2. Update Section 2 if pipeline order or analysis inputs changed.
3. Update Section 3 table if `DecisionMaker::decide` precedence changed.
4. Update Section 4 if `SigDecisions`/`collect_diffs` interaction changed.
5. Update Section 5 if any `visit_item`, `visit_local`, `visit_expr`, or statement flattening behavior changed.
6. Update Section 6 matrix and helper descriptions for new/removed conversion paths.
7. Update Section 7 limitations/fallbacks for added/removed conservative behavior or panic guards.
8. Update Section 8 test mapping if coverage location or validation commands changed.
