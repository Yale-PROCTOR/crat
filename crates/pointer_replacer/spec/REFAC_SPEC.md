# Canonical Refactor Rewrite Specification

Status: Canonical, corrected-intended semantics
Scope: refactor rewrite behavior only (no analysis algorithm changes)

## 1. Purpose
This document defines the required rewrite outcome for a refactor module so independent implementations (including AST-based rewrites) produce the same observable transformed Rust program as a legacy span-based baseline, except where this spec explicitly defines corrected behavior.

The method is intentionally not prescribed. Only externally visible rewrite results are normative.

## 2. Normative Language
- `MUST`: required behavior.
- `MUST NOT`: forbidden behavior.
- `SHOULD`: recommended unless a justified compatibility reason exists.
- `COMPAT`: current implementation divergence note; not normative unless explicitly adopted for compatibility mode.

## 3. Self-Containment and Non-goals
This specification is self-contained and MUST be sufficient for implementation without access to any specific repository layout or source paths.

Non-goals:
- Re-specifying ownership/mutability/fatness/taint analyses.
- Changing runtime semantics beyond the intended rewrite contract.
- Defining rustc-internal API upgrades.

## 4. Inputs
## 4.1 Analysis Inputs
The rewrite consumes:
- ownership schemes precision (`precision(did)`)
- solidified ownership per pointer depth
- mutability per pointer depth
- fatness per pointer depth
- taint field-alias sets

## 4.2 Rewrite Options
- `type_only`
- `const_reference`
- `type_reconstruction`
- `no_box`
- `force_box`
- `raw_mutability`
- `no_attempt` (regex over function path)

Option precedence:
1. If any function has `precision == 0`, effective `no_box` becomes `true`.
2. If `force_box == true`, effective `no_box` becomes `false`.
3. Per-function `no_attempt` can still force raw behavior for matching functions.

## 5. DecisionVector Contract
A `DecisionVector` is a pointer-depth-indexed vector of pointer classes for each field/local.

Pointer classes:
- `Move`
- `Mut`
- `Const`
- `Raw(Move)`
- `Raw(Mut)`
- `Raw(Const)`

Depth indexing:
- index 0 = outermost pointer after stripping array/slice layers
- index N = Nth pointee pointer layer

## 5.1 Struct Field Decision Derivation
For each pointer depth on a struct field:
1. If ownership says owning:
   - choose `Raw(Move)` when any of:
     - fatness says array
     - field aliases with another field whose ownership vector is entirely non-owning
     - effective `no_box == true`
   - else choose `Move`
2. If ownership says non-owning:
   - if `raw_mutability == true`:
     - choose `Raw(Const)` when mutability says immutable and current pointee type is not mutable pointer
     - else choose `Raw(Mut)`
   - else:
     - choose `Raw(Const)` when current pointee type is not mutable pointer
     - else choose `Raw(Mut)`

## 5.2 Function Local Decision Derivation
For each pointer depth on each local:
1. If ownership says owning:
   - choose `Raw(Move)` when fatness says array
   - else choose `Move`
2. If ownership says non-owning:
   - if `raw_mutability == true`: same rule as struct non-owning
   - else if `const_reference == true`:
     - choose `Const` when mutability says immutable and fatness is not array
     - else fallback to `Raw(Const)`/`Raw(Mut)` by pointer mutability
   - else fallback to `Raw(Const)`/`Raw(Mut)` by pointer mutability
3. Output-parameter override (`fn_sig` marks output):
   - if depth-0 is `Move` and function does not match `no_attempt`: replace depth-0 with `Mut`
   - else if depth-0 is `Raw(Move)` or function matches `no_attempt`: replace depth-0 with `Raw(Const)`/`Raw(Mut)` by declared pointer mutability
4. If effective `no_box == true` or function matches `no_attempt`, all remaining `Move` entries become `Raw(Move)`.

## 6. RuleId Namespace
Stable rule IDs MUST use one of:
- `TY-*`
- `SIG-*`
- `MIR-*`
- `CALL-*`
- `CONST-*`
- `ADAPT-*`

## 7. Rewrite Pipeline
1. Compute decisions (`StructFields`, `FnLocals`).
2. Rewrite struct types and append generated impls.
3. Rewrite function signatures.
4. If `type_only == false` and function is not C variadic, rewrite MIR-driven body usage.
5. Apply edits grouped per file in reverse insertion order.

## 8. Type Rules (`TY-*`)
- `TY-100`: pointer class mapping in type positions:
  - `Move -> Option<Box<T>>`
  - `Mut -> Option<&mut T>`
  - `Const -> Option<&T>`
- `TY-110`: raw mapping in type positions:
  - `Raw(Const) -> *const T`
  - `Raw(Mut) -> *mut T`
  - `Raw(Move) -> *mut /* owning */ T`
- `TY-120`: with `type_reconstruction == true`, type rewrite MUST reconstruct the whole visited type recursively.
- `TY-130`: with `type_reconstruction == false`, rewrite MUST update each outermost raw pointer qualifier per depth and preserve remaining type text.
- `TY-140`: for each struct, append `impl Default` block when effective `no_box == false`.
- `TY-150`: if struct is owning (`is_owning == true`), prepend:
  - `struct ErasedByRefactorer{N};`
  - `#[repr(C)]`
  and append `fn take(&mut self) -> Self { core::mem::take(self) }`.
- `TY-160`: `Default` field initializer policy:
  - pointer field with raw decision -> `null`/`null_mut` by mutability
  - pointer field with safe decision -> `None`
  - array field -> recursive array default form (`[Default::default(); LEN]` at leaves)
  - others -> `Default::default()`
- `TY-170`: local type aliases SHOULD be dealiased for decision application.
- `TY-180`: if effective `no_box == true`, generated `Default` impl insertion MUST be skipped.

## 9. Signature Rules (`SIG-*`)
- `SIG-100`: function return type MUST be rewritten from decision vector index 0.
- `SIG-110`: function input parameter types MUST be rewritten from decision vectors indices 1..N.
- `SIG-120`: every HIR parameter binding MUST be prefixed with `mut` when originally non-mutable.
- `SIG-130`: body rewrite MUST be skipped when `type_only == true`.
- `SIG-140`: body rewrite MUST be skipped for C-variadic functions.

## 10. MIR Rules (`MIR-*`)
- `MIR-100`: assignment statements are rewrite-eligible when destination local is:
  - a user variable, or
  - a deref temp not assigned from `CopyForDeref`, or
  - call destination temporary, or
  - static reference local.
- `MIR-110`: plain assignment expression MUST split LHS span and rewrite place-store path separately from RHS rewrite.
- `MIR-120`: intrinsic `assume` statement MUST become `()`.
- `MIR-130`: `SwitchInt` discriminator load MUST be rewritten in by-value mode; if textual snippet starts with `match` and parser fails, normalize prefix to `match ` before replacing discriminator expression.
- `MIR-140`: terminator `Return` rewrites return temporary only when return local is not a user variable and has a non-entry def.
- `MIR-150`: place-store rewriting MUST:
  - resolve deref-copy temporaries to base place
  - build projected replacement over deref/field/index
  - use safe-pointer deref form `*x.as_deref_mut().unwrap()` for non-raw
  - use raw deref `*x` for raw
  - recursively rewrite index temporaries
- `MIR-160`: place-load by-value MUST:
  - resolve deref-copy temporaries
  - rewrite projections similar to store
  - choose deref accessor (`clone`, `as_deref`, `as_deref_mut`) by required/produced context
  - apply post-load adaptation via `ADAPT-*`
- `MIR-170`: place-load by-ref MUST append:
  - `.as_mut_ptr()` when source snippet contains `as_mut_ptr()`
  - `.as_va_list()` when source snippet contains `as_va_list`
- `MIR-180`: place-load by-addr MUST wrap expression as one of:
  - `Some(&mut expr)`
  - `Some(&expr)`
  - `core::ptr::addr_of!(expr)`
  - `core::ptr::addr_of_mut!(expr)`
  based on required pointer class.
- `MIR-190`: temporary rewrite MUST follow def-use chain:
  - phi: rewrite each incoming assign def
  - mir assign: rewrite assigned rvalue
  - deinit: no rewrite
- `MIR-200`: indexed place replacement MUST preserve index subexpressions by splitting replacement text at sentinel boundaries and applying per-span replacement.
- `MIR-210`: known partial handling:
  - checked-add tuple-like field projection without ADT: no rewrite for that field step
  - union field projection: treat pointer vector as empty and continue
- `MIR-220`: unsupported terminators/rvalues MAY be logged and left unchanged.
- `MIR-230`: deref-temp chains MUST be collapsed by recursively following `CopyForDeref` defs.

## 11. Adaptation Rules (`ADAPT-*`)
`adapt_usage(expr, produced, required)` rules:
- `ADAPT-100`: required rustc-move object:
  - produced rustc-move + indirect place -> append `.take()`
  - produced raw pointer -> wrap `Some(Box::from_raw(expr))`
- `ADAPT-110`: required raw-move pointer (`required is copy-object but move-object`):
  - produced safe move pointer -> append `.map(|b| Box::into_raw(b)).unwrap_or(std::ptr::null_mut())`
  - produced raw pointer -> unchanged
- `ADAPT-120`: required raw const/mut pointer:
  - produced safe pointer -> append map/cast/null fallback sequence:
    - const target: use `.clone()` for produced `Const`, else `.as_deref()`, cast to `*const _`, null `std::ptr::null()`
    - mut target: use `.as_deref_mut()`, cast to `*mut _`, null `std::ptr::null_mut()`
  - produced raw mut and required raw const -> append `as *const PointeeType`
- `ADAPT-130`: required safe `Const`/copy pointer:
  - produced raw -> append `.as_ref()`
  - produced safe move-like -> append `.as_deref()`
  - produced safe copy-like -> append `.clone()`
- `ADAPT-140`: required irrelevant context and produced safe pointer -> append `.as_deref().map(|r| r as *const _).unwrap_or(std::ptr::null())`.
- `ADAPT-150`: required mutable safe pointer:
  - produced raw -> append `.as_mut()`
  - produced safe -> append `.as_deref_mut()`
- `ADAPT-160` (corrected): `raw_mut` classification MUST mean `Raw(Mut)` only.

## 12. Constant Rules (`CONST-*`)
- `CONST-100`: null integer scalar constant used where required class is safe pointer (`Move`/`Mut`/`Const`) MUST rewrite to `None`.
- `CONST-110`: non-null constants MUST remain unchanged.
- `CONST-120`: null constants in raw-required contexts MUST remain raw null forms.

## 13. Call Rules (`CALL-*`)
### 13.1 Intra-crate Boundary Calls
- `CALL-100`: each argument MUST be rewritten according to callee parameter decision vector depth-0+.
- `CALL-110`: destination usage MUST adapt from callee return decision vector (index 0) to destination required context.
- `CALL-120`: if required arg class is `Mut` pointer and argument local is itself the destination of a call definition, `.as_mut()` MUST be appended at arg def span end before rewriting temporary.
- `CALL-130`: if function precision is 0 and return produced is rustc-move while destination required is rustc-copy, required context MUST degrade to `Raw(Move)` leak behavior.

### 13.2 Libc Calls
- `CALL-200`: `malloc` direct call rewrite performs no immediate function-name replacement.
- `CALL-210`: `free(arg)` where arg local decision depth-0 is `Move` MUST replace callee span with `()`.
- `CALL-220`: other `free(arg)` cases MUST rewrite arg-def rvalue as required raw mutable pointer context.
- `CALL-230`: `printf` arguments after format string MUST rewrite pointer args as required raw-const context.
- `CALL-240`: cast/use path fed by `malloc`/`calloc` and required rustc-move destination MUST rewrite allocator callsite into `Some(Box::new(<crate::T as Default>::default()))` and erase trailing cast text.
- `CALL-250`: same allocator path when move destination not required MUST fallback to default call rewrite over call args.

### 13.3 Library Calls
- `CALL-300`: `core::slice::*::as_mut_ptr` MUST rewrite first argument under required raw-mut pointer context.
- `CALL-310`: `core::option::Option::{is_some,is_none}` shape recognized by MIR temp-from-ref pattern MUST rewrite receiver temp and join with method call using dot insertion.
- `CALL-320`: `core::ptr::*::is_null` when produced argument context is safe pointer MUST replace callee span with `is_none()` and rewrite operand under required safe-const context.
- `CALL-330`: `core::ptr::*::is_null` raw case MUST rewrite operand under raw const/mut requirement by declared pointer mutability.
- `CALL-340`: `core::ptr::*::addr` MUST be left unchanged.
- `CALL-350`: unmatched library calls MUST use default pointer-argument rewrite behavior.

### 13.4 Closure/Fn Pointer + Default Calls
- `CALL-400`: non-constant callee (closure/fn pointer) MUST rewrite pointer args by declared arg type:
  - unsafe ptr -> raw const/mut required
  - region ptr -> safe const/mut required
- `CALL-410`: default call rewrite for known callee MUST apply same pointer-arg requirement policy as `CALL-400`.

## 14. Rewrite Ordering and Overlap Semantics
- Replacements are accumulated as suggestions.
- Suggestions are grouped by file.
- Within each file, suggestions are applied in reverse insertion order.
- Failed suggestion applications are logged; rewriting continues.

AST-based implementations MUST preserve final replacement effect equivalent to this ordering policy.

## 15. Unsupported / Partial Behavior Contract
Where implementation currently logs and skips:
- unsupported rvalues
- unsupported terminators
- union-specific exact pointer semantics
- certain checked-add tuple projections

A conforming implementation MUST either:
1. Preserve source in those cases and continue, or
2. Produce behavior provably equivalent to preserving source.

## 16. Corrected Semantics and COMPAT Notes
### C-01: `is_raw_mut` contradiction
Normative correction:
- `raw_mut` means `Raw(Mut)` only (`ADAPT-160`).

COMPAT:
- Legacy span-based implementations may define `is_raw_mut()` as `Raw(Move)`, which can mis-route raw-move vs raw-mut adaptation branches.
- Implementers MAY support a compatibility mode that reproduces current branch behavior, but canonical mode MUST follow corrected semantics.
- Conformance mapping: `ADAPT-160-RAW-MUT-CORRECTED`.

### C-02: same-outcome requirement for non-span engines
Normative requirement:
- AST-based engines MAY choose different internal decomposition, but MUST match emitted textual constructs (or alpha-equivalent Rust code) expected by conformance cases.
- Conformance mapping: `COMPAT-C02-AST-EQUIV`.

## 17. Acceptance Criteria
A rewrite module is conformant when:
1. Every rule in Sections 8-13 has at least one passing conformance case.
2. All compatibility notes have explicit compatibility-tagged cases.
3. Two consecutive review rounds report no `critical` or `major` gaps.
4. The implementation-independence clause is satisfied: same rewrite outcome, different method permitted.
