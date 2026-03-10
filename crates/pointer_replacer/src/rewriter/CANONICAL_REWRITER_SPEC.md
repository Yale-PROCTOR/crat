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
    - `OptBox` (`Option<Box<T>>`)
    - `Raw(bool)` (`*const T` / `*mut T`)
    - `OptBoxedSlice` (`Option<Box<[T]>>`)
    - `Slice(bool)` (`&[T]` / `&mut [T]`)
    - `SliceCursor(bool)` (`SliceCursorRef<'_, T>` / `SliceCursor<'_, T>`)
- `DecisionMaker::new(analysis, did, tcx)`
  - Materializes per-local facts for one function:
    - mutability-by-local
    - array/fatness-by-local
    - top-level owning-by-local
    - output-parameter bitset
    - promoted mut/shared sets
    - `needs_cursor` set derived from offset-sign facts via THIR->MIR binding mapping
- `DecisionMaker::decide(local, decl, aliases) -> Option<PtrKind>`
  - Core precedence-ordered local decision algorithm.
- `SigDecisions::new(rust_program, analysis)`
  - Produces per-function input/output signature rewrite decisions.
  - Carries `signature_locked` when a function is used as a function pointer, keeping that function signature raw.

### `collector.rs`
- `collect_fn_ptrs(rust_program)`
  - Finds local functions used as function pointers by scanning HIR for local `Fn`/`AssocFn` paths whose adjusted HIR type is `FnPtr`.
  - This includes explicit `as bare_fn_type` casts and ordinary fn-pointer coercions such as typed let-bindings.
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
- `_owning_pointers` and `_output_params` are now consulted by `decide`.

### 3.2 Branch-Ordered Precedence (`DecisionMaker::decide`)
The following table is exact branch order.

| Order | Condition | Output |
|---|---|---|
| 1 | `unwrap_ptr_from_mir_ty(decl.ty)` fails | `None` |
| 2 | pointee is `c_void` OR file-like type | `Some(Raw(decl mutability))` |
| 3a | top-level owning, array, `needs_cursor`, output param | `Some(Raw(mutable_pointers[local]))` |
| 3b | top-level owning, array, `needs_cursor`, not output param | `Some(Raw(mutable_pointers[local]))` |
| 3c | top-level owning, array, not `needs_cursor`, output param | `Some(Slice(true))` |
| 3d | top-level owning, array, not `needs_cursor`, not output param | `Some(OptBoxedSlice)` |
| 4a | top-level owning, non-array, output param | `Some(OptRef(true))` |
| 4b | top-level owning, non-array, not output param | `Some(OptBox)` |
| 5 | alias cluster exists and any member (including `local`) is mutable | `Some(Raw(mutable_pointers[local]))` |
| 6a | non-owning array and local in promoted shared set and `needs_cursor` | `Some(SliceCursor(false))` |
| 6b | non-owning array and local in promoted shared set and not `needs_cursor` | `Some(Slice(false))` |
| 6c | non-owning array and local in promoted mut set and `needs_cursor` | `Some(SliceCursor(true))` |
| 6d | non-owning array and local in promoted mut set and not `needs_cursor` | `Some(Slice(true))` |
| 6e | non-owning array and not promoted | `Some(Raw(mutable_pointers[local]))` |
| 7 | non-array and local in promoted shared set | `Some(OptRef(false))` |
| 8 | non-array and local in promoted mut set | `Some(OptRef(true))` |
| 9 | `decl.ty.is_raw_ptr()` | `Some(Raw(mutable_pointers[local]))` |
| 10 | otherwise | `None` |

Notes:
- `unwrap_ptr_from_mir_ty` treats both raw pointers and references as pointer-like for decision purposes.
- `needs_cursor` remains a conservative raw carveout for owning arrays in M4A because signed-offset-safe owning transforms are not implemented yet.
- Alias rule remains intentionally conservative for the non-owning path.
- After the branch-ordered choice is made, mutable `Raw` / `OptRef` / `Slice` / `SliceCursor` results are downgraded back to their shared/const forms when the original pointer type was `*const T` or `&T`; the rewriter does not synthesize mutable borrow-like forms from originally-const pointer types.

### 3.3 Signature Decision Rules (`SigDecisions::new`)
1. Compute `fn_ptrs = collect_fn_ptrs(rust_program)`.
2. For each function `did`:
   - If `did in fn_ptrs`:
     - `input_decs = vec![None; input_arity]`
      - `output_dec = None`
      - `signature_locked = true`
   - Else:
     - For each parameter local (`_1..` up to input arity), run `DecisionMaker::decide`.
      - For return local `_0`, run `decide` and keep:
        - `Some(Raw(m)) -> Some(Raw(m))`, unless `infer_returned_local_box_kind(...)` below finds an owning `OptBox` / `OptBoxedSlice` source local to upgrade from
        - `Some(OptBox) -> Some(OptBox)`
        - `Some(OptBoxedSlice) -> Some(OptBoxedSlice)`
        - any borrow-like result -> try `infer_returned_local_box_kind(body, decision_maker, aliases, _0)`:
          - scan MIR statements for assignments to `_0`
          - if every `_0` assignment is a direct `_0 = move/copy <local>`
          - and every such assignment agrees on one source local
          - and that local decides to `OptBox` / `OptBoxedSlice`
          - use that box kind as `output_dec`
          - otherwise `None`
      - `signature_locked = false`

Current consequence:
- signature decisions can now request owning return rewrites for `OptBox` and `OptBoxedSlice`
- borrow-like return rewrites remain disabled

## 4) `SigDecisions` and `collect_diffs` Interaction
- `TransformVisitor::new` computes both from the same `Analysis` snapshot.
- `SigDecisions` drives:
  - function signature parameter/return type rewriting (`visit_item`)
  - call-argument target kind selection (`visit_expr` call branch)
  - source-kind lookup for local call expressions whose rewritten return kind is non-`None`
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
    - `OptRef(m)` -> rewrite to `Option<&{mut?} T>` via `mk_opt_ref_ty`.
    - `OptBox` -> rewrite to `Option<Box<T>>` via `mk_opt_box_ty`.
    - `OptBoxedSlice` -> rewrite to `Option<Box<[T]>>` via `mk_opt_boxed_slice_ty`.
    - `Slice(m)` -> rewrite to `&{mut?}[T]` via `mk_slice_ty`.
    - `Raw(m)` -> rewrite to `*{mut|const} T` via `mk_raw_ptr_ty`.
    - `SliceCursor(m)` -> rewrite to cursor type via `mk_cursor_ty`; set `slice_cursor = true`.
    - `None` -> keep as-is.
    - after the type rewrite, any mutable chosen kind (`kind.is_mut()`) forces the binding pattern to `mut`
- Return type rewrite occurs when `sig_dec.output_dec` is `Some(Raw(_)|OptBox|OptBoxedSlice)`.
- Borrow-like return kinds still do not rewrite signatures.
- Before the chosen output kind is applied, `visit_item` conservatively downgrades `OptBox` / `OptBoxedSlice` outputs to `Raw` when any explicit `return expr` or implicit tail expression in the function body is not a supported box source for that output kind.

### 5.2 `visit_local`
- For let-bindings with `ptr_kinds[hir_id]`:
  - Set `local.ty = Some(...)` to the selected pointer-kind type (`OptRef`/`OptBox`/`OptBoxedSlice`/`Slice`/`Raw`/`SliceCursor`) even when the original binding had no explicit type annotation.
  - Any mutable selected kind forces the binding pattern to `mut`.
  - For `Raw(...)` locals, tracked outermost-local allocator roots may now bridge before generic raw conversion.
    - tracked candidates are direct local bindings (or direct local wrapper-call results) whose writes stay outermost-local and whose deallocation stays on the same local path
    - exact scalar roots rewrite to `Box::into_raw(Box::new(default_value_expr))`
    - supported array roots rewrite to leaked boxed-slice storage via `Box::leak(...into_boxed_slice()).as_{mut,}ptr()`
    - local raw-bridge admission now accepts bounded scalar-temp size/count DAGs in the current body for non-exact `malloc` / `calloc` / `realloc(null_like, ...)` roots
      - allowed scalar sources include params, scalar locals defined earlier in the same body, casts/drop-temps, integer arithmetic, `wrapping_*` arithmetic methods, and size-query calls such as `strlen(...)`
      - rejected scalar sources include field reads, projection/index reads, raw dereference reads, address-of, globals/statics, and nested-pointer expressions
    - `default_value_expr` now recurses through local structs and array fields, using `std::array::from_fn(...)` instead of `<[T; N] as Default>::default()` for array members
    - locals whose raw value escapes through aliases, returns, or unrelated call arguments stay on the original allocator/free path
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
  - During raw-bridge candidate collection, a tracked local passed to a local callee is no longer disqualified unconditionally.
    - The candidate survives only when the exact matching local-callee raw-pointer parameter is proven `BorrowOnly`.
    - `BorrowOnly` permits transient pointee reads/writes, pointer arithmetic, calls into other local `BorrowOnly` params, and a narrow whitelist of transient foreign buffer APIs:
      - `memcpy` arg positions 0 and 1
      - `memmove` arg positions 0 and 1
      - `memset` arg position 0
      - `strncpy` arg positions 0 and 1
    - Anything inconclusive defaults to `Escapes`, which preserves the previous disqualification behavior.
    - `Escapes` includes:
      - storing the pointer value
      - returning it
      - freeing it
      - writing it into a field / projection / container / global
      - passing it to foreign callees
      - passing it to local callees whose matching parameter is not proven `BorrowOnly`
  - Direct `free`-like calls whose single argument is a tracked raw-bridge local (optionally wrapped in one cast layer) are rewritten to a null-guarded drop:
    - scalar locals use `drop(Box::from_raw(...))`
    - array locals use `drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(...)))`
    - supported local deallocator wrappers participate in the same rewrite path as direct foreign `free(...)`
    - M13 slice 1 broadens local deallocator-wrapper recognition structurally:
      - the wrapper must have exactly one raw-pointer parameter
      - it may null-check that parameter and assign it to null afterwards
      - it must directly call foreign `free(param)`
      - any field access, pointer-value aliasing, return, or non-free call use of that parameter keeps the wrapper out of this path
  - Run `hoist_opt_ref_borrow` post-pass to reduce repeated mutable deref borrow conflicts.
- Method call `is_null`
  - local `OptRef` receiver -> rename to `is_none`
  - local `OptBox` / `OptBoxedSlice` receiver -> rename to `is_none`
  - local `Slice` / `SliceCursor` receiver -> rename to `is_empty`
  - `Raw` -> unchanged
- Method call `add`
  - lower the receiver expression through raw-pointer conversion using the actual raw receiver type mutability
  - this now handles rewritten local and non-local receivers, including `Option<&mut T>`, slices, cursors, and boxed-slice views
- Method call `offset_from`
  - force receiver and argument through raw-pointer conversion.
- Return (`ret expr`)
  - only for original raw-pointer function outputs: convert return expr with:
    - `sig_decs.output_dec` if present
    - else raw mutability fallback
  - the same conservative output fallback used in `visit_item` is based on both explicit `return expr` nodes and the final tail expression, not just tail-local `_0` MIR shapes
- Unary deref (`*p`)
  - Uses expression context (`Lvalue/Rvalue/AddrTaken`) to choose target mutability.
  - If source is cursor with exactly one offset projection, emits indexed access directly.
  - Otherwise transforms pointer and post-adjusts:
    - deref of `OptRef` -> `.unwrap()`
    - deref of `OptBox` -> `.as_deref{_mut}().unwrap()`
    - deref of `OptBoxedSlice` with no projections -> `.as_deref{_mut}().unwrap()[0]`
    - deref of projected `OptBoxedSlice` sources first materializes a slice expression, then indexes `[0]`
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
- target `OptBox` / `OptBoxedSlice` -> `None`
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
This matrix is for the branch where `PtrExpr` base resolves to:
- local path with known `ptr_kinds`, or
- direct local-function call whose rewritten `output_dec` is non-`None`

| Source kind | Target `Raw` | Target `OptRef` | Target `OptBox` | Target `Slice` | Target `OptBoxedSlice` | Target `SliceCursor` |
|---|---|---|---|---|---|---|
| `Raw` | direct / mutability cast | `opt_ref_from_raw` | panic without allocator-root evidence | `slice_from_raw` | panic without allocator-root length evidence | `cursor_from_raw` |
| `OptRef` | `raw_from_opt_ref` | `opt_ref_from_opt_ref` | panic | `panic!` | panic | `panic!` |
| `OptBox` | `raw_from_opt_box` | `opt_ref_from_opt_box` (same-type or same-size numeric bytemuck only) | `opt_box_from_opt_box` (same-type only) | panic | panic | panic |
| `Slice` | `raw_from_slice_or_cursor` | `opt_ref_from_slice_or_cursor` | panic | `plain_slice_from_slice` | panic | `cursor_from_plain_slice` |
| `OptBoxedSlice` | `raw_from_slice_or_cursor` over projected boxed-slice view | `opt_ref_from_slice_or_cursor` over projected boxed-slice view | panic | boxed-slice view -> `plain_slice_from_expr` | `opt_boxed_slice_from_opt_boxed_slice` (identity only, no projections) | boxed-slice view -> `cursor_from_slice_or_cursor_inner(..., is_plain_slice=true)` |
| `SliceCursor` | `raw_from_slice_or_cursor` | `opt_ref_from_slice_or_cursor` (offset-only fast path uses `as_slice{_mut}`) | panic | `cursor_or_slice_to_slice_expr` | panic | `cursor_from_slice_or_cursor` (+ possible `to_ref_cursor`/`fork`) |

`raw_from_opt_ref` foreign-type note:
- if RHS inner type is `ty::Foreign`, conversion uses an explicit `match` (`Some(x) => *x as *...`, `None => null`) rather than the normal `.as_deref[_mut]().map_or(...)` path.

Deref context behavior:
- `Deref` targeting `Raw/OptRef/Slice` reuses corresponding conversions.
- `Deref` on `SliceCursor` uses `cursor_from_slice_or_cursor_inner(..., is_plain_slice=false)` then indexing logic in `visit_expr`.
- `Deref` on `OptBox` keeps same-type box identity, then `visit_expr` appends `.as_deref{_mut}().unwrap()`.
- `Deref` on `OptBoxedSlice`:
  - no projections -> keeps same-type boxed-slice identity, then `visit_expr` appends `.as_deref{_mut}().unwrap()[0]`
  - with projections -> first materializes a plain slice expression, then `visit_expr` indexes `[0]`

### 6.5 Direct owning allocator-root materialization
When the target context is `OptBox` or `OptBoxedSlice`, `transform_ptr` checks the normalized AST expression for direct allocator calls before entering the general conversion matrix:
- exact scalar roots only:
  - `malloc(size_of::<T>())` + target `OptBox`
  - `calloc(1, size_of::<T>())` + target `OptBox`
  - `realloc(null_like, size_of::<T>())` + target `OptBox`
- scalar `OptBox` materialization uses `Some(Box::<T>::new(...))`
  - raw-pointer fields become `std::ptr::null[_mut]::<...>()`
  - program-defined local structs recurse field-by-field into a struct literal default expression
  - all other fields use `<T as Default>::default()`
- `calloc(count, _)` + target `OptBoxedSlice` -> `Some(std::iter::repeat_with(|| { default_expr }).take((count) as usize).collect::<Vec<T>>().into_boxed_slice())`
- `malloc(bytes)` + target `OptBoxedSlice` -> same iterator materialization with element count `bytes / size_of::<T>()`
- `realloc(null_like, bytes)` shares the same allocator-root handling as `malloc(bytes)`
- this direct allocator-root materialization runs for scalar and owning-array M4A roots before raw fallback handling

### 6.6 General fallback path
If no local-path kind match applies:
- infer mutability from base raw/array type (with array-path deref inspection)
- if callee return signature mutability was rewritten to raw, override fallback mutability accordingly
- convert to requested target using `opt_ref_from_raw`, `slice_from_raw`, `cursor_from_raw`, or raw cast fallback.
- Before the generic raw fallback runs, local-binding visitors may pre-rewrite tracked outermost-local allocator roots in `Raw(...)` context:
  - exact scalar roots -> `Box::into_raw(Box::new(default_value_expr))`
  - supported array roots -> leaked boxed slices with tracked length expressions
  - direct local allocator wrappers (`alloc`/`calloc`/`realloc`-style wrappers returning one outermost local) participate when their call arguments preserve the same raw-bridge shape
  - for the direct local raw-bridge path, allocator byte/count expressions may now come from bounded wrapper-local scalar temp DAGs
  - for byte-sized pointees only, direct local `calloc(size_of::<T>(), len)` roots normalize to array length `len`; this is limited to the existing direct-local raw-bridge path
  - reversed non-byte `calloc(size_of::<T>(), len)` roots remain conservative in this path
  - a tracked direct-local returned byte-buffer root may now survive a one-hop same-body byte-view cast alias such as `p = dest as *mut u8`, but only when the alias:
    - stays byte-sized
    - is updated only through transient pointer arithmetic like `offset`/`add`
    - is not returned, freed, stored, or passed to calls
  - tracked raw locals may also survive local helper calls when the matching local callee raw-pointer parameter is proven `BorrowOnly`
  - M12 slice 1 extends that `BorrowOnly` proof narrowly for local helper params that only forward the pointer into transient foreign buffer calls (`memcpy`, `memmove`, `memset`, `strncpy`) without storing, returning, or freeing the pointer value
  - local aggregate-field-storage helpers remain excluded from this relaxation; a `cJSON_PrintPreallocated`-style `p.buffer = buffer` write still classifies that parameter as `Escapes`
  - wrapper eligibility is structural:
    - the wrapper allocates one principal outermost local
    - the same local is ultimately returned or freed
    - simple alias propagation inside the wrapper body is allowed, but the ownership flow must remain confined to that wrapper
    - wrappers that let the allocated value escape through parameters, globals, nested-pointer writes, or indirect container writes remain unchanged
- plain array bases now also participate in non-raw fallback for `Slice`, `SliceCursor`, and `OptRef` targets instead of being left unchanged at rewrite-enabled call sites
- raw fallback support is asymmetric for owning box targets:
  - scalar `OptBox` targets still panic unless direct allocator-root evidence or an existing box source was matched earlier
  - array `OptBoxedSlice` targets still panic unless direct allocator-root length evidence was matched earlier
- before those panic paths are reachable, M4B adds conservative raw downgrades for locals/functions that cannot be safely materialized as owning boxes:
  - scalar locals/functions fed by unsupported composite allocator roots (header padding, arithmetic, multi-`size_of`, etc.)
  - locals assigned from local helper calls whose output decision was explicitly forced raw
  - locals assigned directly from already-raw local aliases (one-hop propagation only)

### 6.7 Mutability Heuristics Used by Call/Deref Rewrites
- `get_mutability_decision(hir_expr)`:
  - strips leading `.offset(...)` receivers to the root expression
  - if root is a local path with `ptr_kinds` entry, returns that kind mutability
  - otherwise returns `None` (caller falls back to type mutability).
- For raw adaptation in `transform_ptr`, source raw mutability now prefers the full raw expression type before falling back to base-local/base-array heuristics.
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
1. Borrow-like return inference is still absent.
- `SigDecisions` keeps `Raw`, `OptBox`, and `OptBoxedSlice` outputs.
- `OptRef` / `Slice` / `SliceCursor` return rewrites are still dropped.
- Non-fn-pointer functions additionally have a narrow MIR returned-local fallback for `_0 = move/copy <local>` shapes that already decide to `OptBox` / `OptBoxedSlice`.

2. Ownership/output-parameter analysis is now consumed by current rewriter decisions.
- `Analysis` in `rewriter/mod.rs` now carries output-parameter facts and optional solidified ownership facts.
- Current behavior consults top-level ownership and output-parameter facts in `DecisionMaker::decide`.
- Struct-field and deeper nested-pointer ownership facts are still not consumed.
- If ownership analysis is unavailable, the rewriter continues with `ownership_schemes = None`.

3. `ItemKind::Impl(_)` is skipped in `visit_item`.
- Impl methods are not rewritten by this pass.

4. Function-pointer-use detection is HIR-type-driven, not purely syntax-driven.
- `collect_fn_ptrs` recognizes both explicit `as bare_fn_type` casts and plain coercions where the adjusted expression type is `FnPtr`.
- It still only protects local functions/assoc fns, not arbitrary foreign callees.

5. Length fallback often uses a fixed sentinel (`100000`) when concrete length is unavailable.
- Appears in raw->slice/cursor materialization and several non-numeric cast fallback conversions.
- Example emitted pattern: `std::slice::from_raw_parts_mut(ptr, 100000)`.

6. Owning box support is implemented only for the M4A-supported source/target surface.
- Direct allocator roots and local/call box sources are supported.
- Local/call box-source propagation now only trusts local function items with bodies; foreign declarations are not treated as rewrite-aware box sources for fallback/propagation purposes.
- M6/M7 add an outermost-local raw-bridge hardening path:
  - exact scalar allocator roots that remain `Raw(...)` are emitted as `Box::into_raw(Box::new(...))` for conservatively tracked outermost locals
  - supported raw array roots (`malloc(bytes)`, `calloc(count, _)`, `realloc(null_like, bytes)`) are emitted as leaked boxed slices with tracked lengths for those same outermost locals
  - direct `free(local[_cast])` and supported local free-wrapper calls are rewritten to null-guarded `drop(Box::from_raw(...))` / `drop(Box::from_raw(slice_from_raw_parts_mut(...)))`
  - simple local allocator-wrapper calls participate when the wrapper body still preserves a direct outermost-local allocator-root shape
  - M9 generalizes that wrapper path to structural local helpers that allocate one principal outermost local, optionally null-check/mutate it, and then return or free that same local without allowing it to escape through params, globals, or indirect container writes
  - M10 slice 1 adds bounded scalar-temp size/count DAG support for that direct local raw-bridge path only; omni-style branch-return `*mut c_void` factories and other caller-side ambiguous deallocation shapes remain unchanged
  - locals whose raw value escapes through aliases, returns, or unrelated call arguments stay on the original allocator/free path
- Scalar `OptBox` allocator roots are intentionally narrower in M4B:
  - only exact `size_of::<T>()` scalar roots stay eligible
  - unsupported composite scalar roots are forced back to raw before rewrite
- Some raw fallback propagation is now intentional rather than panicking:
  - direct local bindings assigned from local helpers whose output decision was forced raw stay raw
  - direct local aliases assigned from already-raw bindings also stay raw
  - unsupported direct `return expr` / tail-expression box outputs are forced back to raw before signature rewrite
  - raw struct-field pointer flows such as `(*map).entries` remain raw; struct-field ownership is still out of scope
- Several non-goal shapes still panic, especially:
  - `addr_of` / `addr_of` arithmetic into box targets
  - `as_ptr` into box targets
  - casted `OptBox -> OptRef` reinterpretation outside the same-size numeric bytemuck path
  - byte-string source into box targets
  - scalar-box to slice/cursor targets
  - raw-to-scalar-box targets without direct allocator-root evidence
  - owning array box target without allocator-root length evidence
  - owner-struct/container field frees and container-internal realloc growth remain unchanged; M7 still does not rewrite through struct fields or container-owner internals

7. Multiple other conversion branches intentionally panic on unsupported shapes.
- Examples:
  - integer-cast pointer rewrite requested into non-raw context
  - target slice/cursor from `OptRef` source in local/call source-kind matrix
  - byte-string deref context

8. `collect_diffs` only rewrites locals that have at least one mapped HIR binding.
- Locals without binding mapping do not get `ptr_kinds` entries.
- Duplicate reverse-map collisions (multiple bindings to one local) are not guarded; hash-map collection would keep the last one seen.

9. `hoist_opt_ref_borrow` is still pattern-driven, but broader than the pre-M4B helper.
- It now hoists repeated mutable borrow roots for:
  - `arg.as_deref_mut().unwrap()` / `arg.as_deref().unwrap()`
  - raw extraction patterns produced from `arg.as_deref_mut().map_or(...)`
- It rewrites field projections and raw extractions to use one hoisted borrowed temp within a call expression.
- It still does not attempt a general borrow-restructuring framework outside those emitted patterns.

10. Alias conservatism can force raw even when other facts could allow higher-level types.
- Any mutable alias in the alias cluster triggers raw for that local.

11. Hard raw exceptions are always applied first.
- `c_void` and file-like pointees are always `Raw`.

12. Some paths use direct `ptr_kinds` indexing (`[]`) rather than `get`.
- Assignment-LHS resolution can index directly when a local HIR id is found.
- Fallback mutability inference for array+deref roots (`PathOrDeref::Deref`) also indexes directly.
- `is_base_not_a_raw_ptr` deref-path handling indexes directly as well.
- Missing entries in those paths can panic.

## 8) Test Mapping (Current)

### 8.1 Rewriter behavior tests
- Files:
  - `crates/pointer_replacer/src/tests.rs`
  - `crates/pointer_replacer/src/rewriter/transform/mod.rs` (`#[cfg(test)]` white-box regression module)
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
  - M4A positive box rewrite regressions:
    - `test_rewriter_rewrites_malloc_scalar_to_opt_box`
    - `test_rewriter_rewrites_calloc_array_to_opt_boxed_slice`
    - `test_rewriter_rewrites_malloc_array_to_opt_boxed_slice`
    - `test_rewriter_rewrites_local_call_boundary_for_opt_box`
    - `test_rewriter_rewrites_local_call_result_from_opt_box`
    - `test_rewriter_converts_opt_box_call_result_into_opt_ref_param`
    - `test_rewriter_converts_opt_boxed_slice_call_result_into_slice_param`
    - `test_rewriter_keeps_explicit_fn_pointer_return_signature_raw`
    - `test_rewriter_keeps_fn_pointer_scalar_return_raw_while_local_is_box`
    - `test_rewriter_keeps_fn_pointer_array_return_raw_while_local_is_boxed_slice`
    - `test_rewriter_preserves_fn_pointer_signature_with_opt_box_raw_fallback`
    - `test_rewriter_preserves_fn_pointer_signature_with_opt_boxed_slice_raw_fallback`
    - `test_rewriter_mixed_return_shapes_do_not_infer_box_signature`
  - M4B direct regressions:
    - `test_rewriter_moves_opt_box_locals_with_take`
    - `test_rewriter_keeps_composite_realloc_struct_raw_across_return_and_call_result`
    - `test_rewriter_keeps_mutable_local_struct_params_raw`
    - `test_rewriter_rewrites_add_on_slice_like_receivers`
    - `test_rewriter_rewrites_realloc_null_char_ptr_to_boxed_slice`
    - `test_rewriter_keeps_foreign_strdup_tail_raw`
    - `test_rewriter_keeps_struct_field_pointer_tail_raw`
    - `test_rewriter_bridges_raw_scalar_allocator_root_and_free`
    - `test_rewriter_bridges_raw_scalar_calloc_root_and_free`
    - `test_rewriter_bridges_raw_array_realloc_null_root_and_free`
    - `test_rewriter_bridges_outermost_local_allocator_wrappers`
    - `test_rewriter_generalizes_wrapper_returning_allocated_local`
    - `test_rewriter_generalizes_wrapper_with_internal_free_after_foreign_use`
    - `test_rewriter_keeps_wrapper_escape_through_parameter_raw_in_m9`
    - `test_rewriter_keeps_wrapper_escape_through_global_raw_in_m9`
    - `test_rewriter_admits_local_scalar_temp_malloc_free_shape_in_m10`
    - `test_rewriter_keeps_field_read_size_source_raw_in_m10`
    - `test_rewriter_keeps_deref_read_size_source_raw_in_m10`
    - `test_rewriter_allows_borrow_only_local_callee_for_raw_bridge_in_m10`
    - `test_rewriter_keeps_local_callee_pointer_alias_raw_in_m10`
    - `test_rewriter_keeps_local_callee_pointer_return_raw_in_m10`
    - `test_rewriter_keeps_local_callee_pointer_free_raw_in_m10`
    - `test_rewriter_keeps_local_callee_pointer_global_store_raw_in_m10`
    - `test_rewriter_keeps_cjson_style_local_field_storage_raw_in_m10`
    - `test_rewriter_allows_memcpy_style_local_helper_use_in_m12`
    - `test_rewriter_keeps_unknown_foreign_helper_use_raw_in_m12`
    - `test_rewriter_allows_returned_byte_calloc_buffer_in_m13`
    - `test_rewriter_allows_byte_view_alias_of_returned_byte_buffer_in_m13`
    - `test_rewriter_keeps_opaque_byte_calloc_wrapper_return_raw_in_m13`
    - `test_rewriter_keeps_helper_cleanup_byte_calloc_raw_in_m13`
    - `test_rewriter_keeps_non_byte_reversed_calloc_raw_in_m13`
    - `test_rewriter_keeps_returned_byte_buffer_alias_return_raw_in_m13`
    - `test_rewriter_keeps_returned_byte_buffer_alias_free_raw_in_m13`
    - `test_rewriter_keeps_returned_byte_buffer_alias_store_raw_in_m13`
    - `test_rewriter_keeps_non_byte_view_alias_raw_in_m13`
    - `test_rewriter_keeps_scalar_raw_malloc_when_only_alias_is_freed`
    - `test_rewriter_keeps_owner_struct_field_frees_raw_in_m7`
    - `transform::tests::struct_default_materialization_uses_recursive_defaults` directly covers scalar `OptBox` struct-default materialization in `transform/mod.rs`
    - `transform::tests::struct_default_materialization_handles_large_array_fields` directly covers recursive raw-bridge struct defaults for large array fields in `transform/mod.rs`
    - `test_rewriter_materializes_local_struct_malloc_default_gotomach_probe` remains an ignored supplemental probe in `tests.rs`; it is not the landed primary coverage artifact
  - The direct `test_rewriter_` bucket now also covers:
    - const-pointer mutability preservation through `rewriter::decision::tests`
    - unsupported foreign `strdup` tail returns staying raw
    - raw struct-field pointer tail flows staying raw
  - Minimal toy array snippets in `tests.rs` are still conservative under the current analysis in some paths; the authoritative rewrite-compile proof for the broader array-owning surface is the landed B02 rewrite gate in Section 8.4

### 8.2 Rewriter decision tests
- File: `crates/pointer_replacer/src/rewriter/decision.rs`
- Internal white-box tests exercise `DecisionMaker::decide` directly with synthetic facts over real MIR `LocalDecl`s.
- Covered decision areas include:
  - owning scalar output override -> `OptRef(true)`
  - owning scalar non-output -> `OptBox`
  - owning array + `needs_cursor` -> conservative `Raw(...)`
  - owning array without `needs_cursor` -> `Slice(true)` / `OptBoxedSlice`
  - non-owning scalar and cursor regressions remain unchanged

### 8.3 Ownership analysis tests in same file
- Module: `ownership_analysis` inside `tests.rs`
- Validates ownership and output-param analyses (not rewriter mutation).
- Also includes a MIR-source regression guard over the ownership/output guarded paths.

### 8.4 B02 test suite
- File: `crates/pointer_replacer/src/analyses/B02_tests/mod.rs` + case modules.
- Shared harness behavior:
  - run ownership analysis and candidate/stat assertions first
  - then run `replace_local_borrows(&Config::default(), tcx)` on the original case source
  - then type-check the rewritten output in a fresh compiler invocation
  - failure messages include the B02 case name plus the rewritten source text
  - a direct census regression also rewrites all 86 case sources from disk and counts emitted `malloc(` / `calloc(` / `free(` tokens
  - a second inspection-only classifier pass scans the rewritten output for remaining `malloc(` / `calloc(` call sites and records future-work metadata for each site
  - M11 extends that inspection pass with a second-stage implementation-oriented landscape report:
    - wrapper-body allocator sites are split into wrapper subshapes
    - remaining `free(` calls are split into teardown shapes
    - allocator and teardown shapes are tagged with policy status
    - allocator shapes are also tagged with whether they are blocked mainly by allocation shape, deallocation shape, or both
  - focused classifier regressions cover:
    - `classifier_direct_local_binding_maps_to_outermost_extension`
    - `classifier_field_target_maps_to_struct_field_scope`
    - `classifier_nested_pointer_scope_augments_but_does_not_change_shape`
    - `classifier_wrapper_body_gets_priority_over_other_shape_buckets`
    - `classifier_return_tail_maps_to_return_flow_generalization`
    - `classifier_same_function_realloc_sets_context_and_capability`
    - `classifier_fallback_uses_manual_followup`
    - `classifier_deduplicates_capabilities_and_respects_primary_precedence`
    - `classifier_normalizes_and_truncates_statement_snippet`
    - `classifier_wrapper_transient_local_helper_use_is_admissible`
    - `classifier_wrapper_local_aggregate_field_storage_is_blocked_struct_field_scope`
    - `classifier_wrapper_branch_return_opaque_type_maps_to_deallocation_blocker`
    - `classifier_wrapper_alias_escape_is_not_worth_targeting_yet`
    - `classifier_free_direct_local_free_is_admissible`
    - `classifier_free_field_owned_teardown_is_blocked_struct_field_scope`
    - `classifier_free_recursive_tree_list_teardown_is_blocked_free_shape`
    - `classifier_free_matrix_row_teardown_is_blocked_free_shape`
    - `classifier_free_helper_destructor_cleanup_is_blocked_free_shape`
    - `remaining_allocator_site_classification_is_complete`
    - `m9_wrapper_generalization_reduction_vs_verified_baseline`
- Current consequence:
  - every B02 case is now gated on both ownership expectations and rewrite-compile success
  - failing rewrite compilation reports the B02 case name plus the rewritten source text
  - the M8 planning baseline was re-verified through the same checked-in classifier path now used by M9 closeout:
    - `remaining_malloc_sites=64`
    - `remaining_calloc_sites=13`
    - `primary_unlock_wrapper_generalization=46`
  - the current post-M12 classifier totals are:
    - `remaining_malloc_sites=49`
    - `remaining_calloc_sites=7`
    - `primary_unlock_wrapper_generalization=33`
    - `alloc_policy_status:admissible_current_policy=6`
  - the direct token census currently reads `malloc=86`, `calloc=20`, `free=254`
  - M8 remains planning metadata only; M9 and M10 reduced wrapper-generalization-backed allocator sites without expanding the rewrite surface beyond the current outermost-only policy
- Remaining allocator-site classifier schema:
  - per-site fields:
    - `case_name`
    - `function_name`
    - `callee_kind` (`malloc` or `calloc`)
    - `statement_snippet`
    - `shape_bucket`
    - `wrapper_subshape` (wrapper-body sites only)
    - `required_capabilities`
    - `primary_unlock`
    - `policy_status`
    - `blocking_axis`
    - `has_adjacent_realloc_context`
    - `has_adjacent_free_context`
  - shape buckets, in fixed priority order:
    - `allocator_wrapper_body`
    - `return_or_tail_alloc`
    - `field_or_projection_assignment`
    - `direct_local_binding`
    - `other`
  - `nested_pointer_scope` is capability metadata only; it does not change the chosen shape bucket by itself
  - capability taxonomy:
    - `outermost_extension`
    - `struct_field_scope`
    - `nested_pointer_scope`
    - `wrapper_generalization`
    - `return_flow_generalization`
    - `realloc_flow_support`
    - `manual_followup`
  - `required_capabilities` are deduplicated and emitted in the fixed taxonomy order above
  - `primary_unlock` is chosen by fixed precedence:
    - `struct_field_scope`
    - `nested_pointer_scope`
    - `wrapper_generalization`
    - `return_flow_generalization`
    - `realloc_flow_support`
    - `outermost_extension`
    - `manual_followup`
  - `has_adjacent_realloc_context = true` when the same function contains `realloc(`
  - `has_adjacent_free_context = true` when the same function contains `free(`
  - `statement_snippet` is normalized to single-space whitespace and truncated to at most 200 characters
  - wrapper subshapes:
    - `transient_local_helper_use`
    - `local_aggregate_field_storage`
    - `branch_return_opaque_typed_deallocation_recovery`
    - `alias_escape_mediated`
  - policy-status tags:
    - `admissible_current_policy`
    - `blocked_struct_field_scope`
    - `blocked_dedicated_free_shape_reduction`
    - `not_worth_targeting_yet`
  - allocator blocking-axis tags:
    - `allocation_shape`
    - `deallocation_shape`
    - `both_together`
- Remaining `free(` classifier schema:
  - per-site fields:
    - `case_name`
    - `function_name`
    - `statement_snippet`
    - `teardown_shape`
    - `policy_status`
  - teardown shapes:
    - `direct_local_free`
    - `field_owned_teardown`
    - `recursive_tree_list_destruction`
    - `matrix_row_element_teardown`
    - `helper_destructor_mediated_cleanup`
- Example M8 classification record:
  - `case_name: b02_list_push`
  - `function_name: push_node`
  - `callee_kind: malloc`
  - `statement_snippet: node = malloc(sizeof(struct Node))`
  - `shape_bucket: direct_local_binding`
  - `required_capabilities: [outermost_extension]`
  - `primary_unlock: outermost_extension`
  - `has_adjacent_realloc_context: false`
  - `has_adjacent_free_context: true`
- The M8 harness now prints:
  - shape-bucket totals
  - capability totals
  - `primary_unlock` totals
  - wrapper-subshape totals
  - allocator policy-status totals
  - allocator blocking-axis totals
  - remaining `free(` totals by teardown shape
  - `free(` policy-status totals
  - top unresolved cases by remaining `malloc` / `calloc` count

### 8.5 Standard commands used for validation
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
