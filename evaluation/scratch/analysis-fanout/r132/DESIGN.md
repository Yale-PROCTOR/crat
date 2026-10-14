# r132 — raw-to-safe conversion sites (relay 132): design

Status 2026-10-10: **written, not built, not run.** Batch 58's census holds the corpus lock
(`worktrees/CORPUS-SLOT.lock`, main, 11:02Z, expected end 15:02Z), so nothing here has been compiled or
executed: no cargo, no rustc, no counter run. Every MIR shape below is **reasoned from the rustc source** of
nightly-2025-06-23 (`~/.rustup/toolchains/nightly-2025-06-23-x86_64-unknown-linux-gnu/lib/rustlib/rustc-src`), and
the toy's expected rows are predictions. `run.py all` checks them first and does not run the corpus if they fail.

**Revised 10-10 after the independent review** (`prep-results.json`, the object with `defects`): every defect is fixed
in the source and the toy, still without a build or a run (batch 58's census holds the lock). §11 lists each defect,
its fix and the file:line. `toy/expected.tsv` was rewritten BEFORE any run.

The question (relay 132): do Laertes and CROWN convert raw pointers into safe ones, and where? This counts, per
emitted program, every place where the program's own code produces a safe pointer value from a raw pointer.

## Files

| path | what |
|---|---|
| `counter/` | a copy of docs `agents/tools/rq2/pos_counter/` at 9d79b3a (`main.rs` sha256 `aa481f48…`, unchanged since 031), renamed `rq2_site_counter`. The `main.rs` diff is five hunks: `mod sites;`, the `--sites` flag, `sites.tsv` cleared, the bodies cloned beside T2's `promoted_bodies` (before `tcx.analysis` steals them), and `sites.tsv` written. T1 and T2 are unchanged. |
| `counter/src/sites.rs` | the new pass. Its header defines every column of `sites.tsv`. |
| `toy/lib.rs`, `toy/expected.tsv` | the toy crate: 76 expected rows over 75 tagged lines, plus two functions (`n01_rawonly`, `n02_safe`) that must produce none. |
| `run.py` | build / toy / run / summarize / all (usage in its docstring) |
| `out/` | `out/<side>/<p>/{sites.tsv,sites-status.txt,positions.tsv,uses.tsv,status.txt,cmd.txt[,stderr.txt]}`, `out/toy/check.txt`, `out/summary.tsv`, `out/summary-long.tsv`, `out/spot.txt`, `out/run.log`, `out/build.log` |

The r043 binary and target are not touched: `r132/target` is a separate target directory.

## 1. What counts as a site

A **site** is a point in an emitted program's own code (every fn, method and closure body; `const` and `static`
initializers are not scanned) where a safe pointer value is produced from a raw pointer. A safe pointer value is a
reference, an `Option` of one, a slice reference, a `Box`, a `Box<[T]>` or an `Option<Box<..>>`.

- **(a) a reference taken through a raw dereference.** An `Rvalue::Ref` (fake borrows skipped) whose place has at
  least one `Deref` whose base type is `*const T` / `*mut T`. Examples: `&mut *p`, `&*p.offset(k)` (the offset is a
  call whose result temporary is dereferenced), `&mut (*p).f`, `&mut *(*s).q`, and the autoref of `(*p).m()`.
  `src_ty` is the base type at the **last** raw `Deref`, and `raw_derefs` counts the raw `Deref`s. The kind is
  `a:ref` or `a:mut-ref`. `post_raw_derefs` counts the non-raw `Deref`s after the last raw one: `&mut *(*p).r`
  (r: `&mut T`) and `&(*(*p).b).x` (b: `Box<S>`) are 1, a reborrow of a safe pointer that was only *loaded* through a
  raw pointer; `summary.tsv` splits kind a into `a_direct` (0) and `a_via_safe` (> 0).
- **`NonNull` receivers:** for `b:nonnull-*` rows `src_ty` is the receiver's pointee `NonNull<T>`, not the `&NonNull<T>`
  argument (`NonNull::as_ref(&self)`).
- **(b) a conversion call** (a core / std / alloc function, identified by its impl's self type and its name):
  - `<*T>::as_ref`, `as_mut`, `as_uninit_ref`, `as_uninit_mut`, `as_uninit_slice(_mut)`, `as_ref_unchecked`,
    `as_mut_unchecked` (`b:ptr-*`)
  - `Box::from_raw`, `from_raw_in`, `from_non_null(_in)` (`b:box-*`)
  - free `slice::from_raw_parts(_mut)` (`b:slice-*`)
  - `NonNull::as_ref`, `as_mut`, `as_uninit_*` (`b:nonnull-*`)
- **(x) extras, reported but never added to a or b:** `transmute` (only when the source is a raw pointer and the
  result is a safe form), `CStr::from_ptr`, `Vec` / `String::from_raw_parts`, `Rc` / `Arc::from_raw`, and
  `str::from_raw_parts`. They are outside the relay's list but are the same kind of operation, so they are not
  dropped silently.
- **(h) a wrapper call.** A program-local *wrapper* is a function with a non-excluded site (of any kind, h included)
  that meets two conditions: its pointer resolves to one of the function's own raw formals, and its value reaches
  the function's return place, either directly or as a field of the returned struct. The set is a fixpoint, so a
  wrapper of a wrapper counts. A call of a wrapper is an `h` row, with the callee in `call`. The wrapper's internal
  row is still listed, with `in_wrapper=yes`. `in_wrapper` is **per row**: only the row that makes its function a
  wrapper says yes; the wrapper's other rows (`safe_mut(&mut *q)` beside `&mut *p` returned, toy w4) say no. So
  `ab_not_in_wrapper` drops only the wrapping conversions, not every site in a wrapper's body (before the fix a
  wrapper's whole body left that reading, and an uncalled wrapper lost its conversion from `ab_not_in_wrapper + h`).

  This case exists for our trees. Their `slice_cursor` prelude is in-tree: `SliceCursor::from_raw_parts(ptr, len)`
  builds `{ base: slice::from_raw_parts(ptr, len), pos: 0 }`. Without h, every call of that constructor would be
  invisible, and only the one `from_raw_parts` inside the prelude would count.

  Summaries can count either `a + b` (every direct site) or `a + b` outside wrappers plus `h`. `summary.tsv` carries
  `ab`, `ab_not_in_wrapper` and `h`.

## 2. Which MIR, and why: `mir_promoted`

The pass runs on each body's **`mir_promoted`**, cloned before borrowck steals it. This is the same phase and the same
cloning point as T2's `full_*` columns.

- **What c2rust's idiom becomes.** In `&mut *p.offset(k) as *mut T` the cast is a *coercion cast*. Typeck's
  `try_coercion_cast` succeeds (`rustc_hir_typeck/src/cast.rs:1084`). `coerce_raw_ptr` then records the adjustments
  `Deref(None)` + `Borrow(AutoBorrow::RawPtr(m))` on the `&mut *…` expression (`coercion.rs:1014-1020`), and THIR
  lowers the cast to `ExprKind::Use` (`rustc_mir_build/src/thir/cx/expr.rs:258-260`). The adjustments become
  `RawBorrow { Deref { Borrow { Deref(offset(..)) } } }` (`thir/cx/expr.rs:140-142, 175-176`). MIR building gives the
  inner `Borrow` its own temporary, because `as_place` of a `Deref` of an rvalue goes through `as_temp`
  (`builder/expr/as_place.rs:446-449`). So the MIR is:

  ```
  _4 = <*mut T>::offset(copy _p, k) -> bb1
  _3 = &mut (*_4);             // the site (kind a)
  _2 = &raw mut (*_3);         // its only use: back to raw (the exclusion)
  ```

  Nothing in `mir_built` or `mir_promoted` folds this. `mir_built` runs only lints and `SimplifyCfg::Initial`
  (`rustc_mir_transform/src/lib.rs:373-395`). `mir_promoted` adds `PromoteTemps` (a dereference of a run-time pointer
  is never promotable), `SimplifyCfg::PromoteConsts` and coverage (`lib.rs:441-444`).

  An array reference has the same use. In `&mut *a as *mut T` with `a: *mut [T; N]`, `check_ref_cast` first coerces
  to `*mut [T; N]` (`cast.rs:1041-1061`), giving `&raw mut (*_3)`, and then applies `ArrayToPointer` to the raw
  pointer. A reference passed to a raw formal (`strncmp(&mut *s.offset(1), ..)`) is an argument coercion with the
  same adjustments, so it also becomes `&raw const (*_t)`.
- **Why not `mir_built`.** It is stolen by `mir_promoted`. The pre-existing counter already pins `mir_promoted`, and
  the two phases agree on everything this pass reads.
- **Why not optimized MIR.**
  1. `ReferencePropagation` (`ref_prop.rs`, enabled at mir-opt-level >= 2, which is the default under `-O`) rewrites
     `_2 = &raw mut (*_3)` to `_2 = &raw mut (*_4)` and deletes `_3`. The exclusion and the site both vanish.
  2. `ElaborateBoxDerefs` (`lib.rs:617`) turns every `Box` dereference into a dereference of a raw pointer, which
     would create false kind-a sites wherever a `Box` is borrowed.
  3. `CleanupPostBorrowck` (`lib.rs:580`) removes the `FakeRead(ForLet)` statements, which are the only MIR evidence
     separating `let x = &mut *p` (decl) from `x = &mut *p` (assign). `mir_built` emits that `FakeRead` right after
     the initializer (`builder/matches/mod.rs:598-610`, and `:616-640` for `let x: T = …`).
- **Cleanup blocks are skipped** for uses, definitions and sites. `build_drop_and_replace` (`builder/scope.rs:1405-1436`)
  assigns the new value in both the normal block and the unwind block. Without the skip, `(*h).b = Some(Box::from_raw(p))`
  would read as a two-use temporary.

## 3. Destination of the safe value

The pass starts from the place the site writes to (the `Ref` statement's left side, or the call's destination). It
then follows the value through **compiler temporaries** (non-user, non-argument locals), using an index of each
temporary's uses (`index_uses`). These uses are ignored: `PlaceMention`, `FakeRead`, `StorageLive/Dead`,
`AscribeUserType`, a discriminant read, a `SwitchInt` / `Assert` operand, and a shared borrow of the whole temporary
(`opt.is_some()`'s autoref). After those are removed, the temporary must have exactly one use, and these uses step on:

| use | step | `via` |
|---|---|---|
| `d = move t` / `CopyForDeref` / an unsizing pointer coercion | to d | - |
| `d = &(mut) (*t)` (a reborrow, the coercion of a `&mut` argument / return) | to d | `reborrow` |
| `d = Option::Some(t)` | to d | `Some` |
| `d = move (t as Some).0` (an `if let` / `match` payload) | to d | `match-some` |
| `t` passed to `Option::unwrap / expect / unwrap_unchecked` | to the call's destination | `unwrap` … |
| `d = &raw (*t)` / `d = t as *T` | to d, **excluded** (§4) | `rawptr-of-deref` / `cast-to-raw` |
| `t` is argument 0 of a std method `as_ptr` / `as_mut_ptr` / `as_ptr_range` / `as_mut_ptr_range` with a raw result | to the call's destination, **excluded** (§4) | `method-to-raw:<name>` |

**A `Drop` after a move is not a use.** `mir_built` schedules a value drop for every operand temporary
(`builder/expr/as_temp.rs:129-131`) and unschedules it only for call arguments (`record_operands_moved`,
`builder/scope.rs:1260-1281`, called for call arguments at `expr/into.rs:260`, tail-call arguments at `expr/stmt.rs:126`
and an array repeat at `expr/as_rvalue.rs:772`). An aggregate's fields
(`expr/into.rs:384-404`, `local_temp_lifetime`) and an assignment's right-hand side (`expr/stmt.rs`, `as_local_rvalue`)
are never unscheduled, so `Some(Box::from_raw(p))` is `_t = Box::from_raw(..); _s = Some(move _t); drop(_t)` in the
normal path; drop elaboration removes the dead drop only later. When a temporary has exactly one non-`Drop` use and that
use moves it (`Move`, `Some(..)`, a payload read, a field / element init, a call argument), its `Drop`s are ignored.
A lone `Drop` is still `other drop` (`let _ = Box::from_raw(p)`).

The walk ends at one of these destinations:

| dest | when | dest_detail |
|---|---|---|
| `call-arg` | `t` is a call argument (any other callee) | the callee path (`tail:` for a tail call); `formal_ty`, `formal_safe` = the instantiated formal's depth-0 form in T1's vocabulary: `safe`, `raw`, `generic`, `other`, or `variadic` (past a C variadic's formals) |
| `decl` | a user variable written by a `let` (the next non-trivial statement is `FakeRead(ForLet, x)`), or a single-definition binding that has an initializer or a match place (`VarBindingForm::opt_match_place` is `Some`: `if let Some(r) = …`, c2rust's `let ref mut freshN = …`, a `let b = Some(..)` whose `FakeRead` sits after the operand's drop). `let r; r = …` has no initializer (`builder/block.rs:283` passes `None`) and is `assign`; so is a guard's `if let` binding (`matches/mod.rs:801`, a FIXME passing `None`) | the variable |
| `assign` | any other write of a user variable or a formal | the variable |
| `return` | `_0` | - |
| `field-store` | a place with a `Field` projection (`(*s).f = …`); also a struct / enum / union literal | `Struct.field`, with `@raw` when the store goes through a raw pointer; a literal is `init:Struct.field>DEST`, where DEST is where the struct goes; a union literal names its **active** field (`AggregateKind::Adt`'s fifth component, `mir/syntax.rs:1552`), not the operand index |
| `other` | everything else | `deref-use` (used only through `*t`, e.g. `(&mut *p).x`, `*p.as_ref().unwrap()`), `drop` (`let _ = Box::from_raw(p)`), `store-deref` (`*pp = &mut *p`), `elem-store` (`a[1] = &mut *p`), `elem:tuple.N>DEST` / `elem:array>DEST` / `elem:array-repeat>DEST` / `elem:closure-capture>DEST` (an element of a tuple / array / closure aggregate, and where the aggregate goes), `observed-only` (only a test reads it), `unused`, `multi-use:<uses>`, … |

Our exposure boundary is counted separately. In the C-named wrapper `f(p: *mut T) { __crat_safe_f(&mut *p) }`, the
row's destination is `call-arg __crat_safe_f`; `summary.tsv` counts these in `ab.call-arg.boundary`.

## 4. Exclusion (the control)

A kind-a (or b / x / h) row is **excluded** when the safe value's only use, reached through temporaries alone (moves,
reborrows, an `unwrap`), is a conversion straight back to a raw pointer:

- `&raw (mut|const) (*t)` (`rawptr-of-deref`) is the `&T → *T` coercion. This covers the coercion cast
  `&mut *p as *mut T`, a reference passed to a raw formal, and the array-to-pointer cast.
- `&raw (*t).f…` is `rawptr-of-subplace` (toy t57: `&raw mut (&mut *p).x`).
- `Cast(_, t, *U)` is `cast-to-raw` (kept as a fallback). No surface cast reaches it: a `&T as *const T` is a coercion
  cast (`cast.rs:1084`, lowered as above), the array case goes through `check_ref_cast` (`cast.rs:1041-1061`), and any
  other `&T as *U` is rejected by typeck. So the toy has no row for it.
- **`method-to-raw`**: the reference is argument 0 of a core / std / alloc *method* named `as_ptr`, `as_mut_ptr`,
  `as_ptr_range` or `as_mut_ptr_range` whose result is a raw pointer (or a `Range` of them). This is c2rust's method-form
  address idiom: `(*buff).vals.as_mut_ptr()` is the autoref `_a = &mut (*buff).vals`, an unsizing coercion
  `_b = move _a as &mut [T]` (arrays have no inherent `as_mut_ptr`, so probing reaches `<[T]>::as_mut_ptr` through the
  unsize step), and `<[T]>::as_mut_ptr(move _b)`. `Vec::as_mut_ptr`, `str::as_ptr` and `MaybeUninit::as_ptr` take the
  autoref directly. The chase then follows the raw result (dest = where the raw pointer went). The review's regex lower
  bound found at least 108 such sites in the rs-crown input and at least 184 in CROWN's trees, all counted as
  `call-arg safe` rows before this fix. Toy: t42-t45 excluded, t46 (`.len()`) not.

The excluded row's `dest` then describes where the raw value went: for example `call-arg strncmp`, `formal_safe=raw`.
A reference bound to a user variable is never excluded, even if the variable is later cast (`let r = &mut *p; r as
*mut T`), because its use is not "only a cast". Excluded rows are listed and counted separately (`excluded`). They
are not sites.

## 5. Null dominance

`null_dom` is computed for every row that has a pointer operand. The relay asks for it for `Box::from_raw` and
`as_ref` / `as_mut`; for the others it is informational. For a `NonNull` receiver it is `n/a`. MIR dominators
approximate a dominating null test as follows:

1. **The tests.** Each non-cleanup block ending in a `SwitchInt` on a bare local is resolved through
   single-definition locals (and `!`) to one of these:
   - `is_null(q)` (`<*T>::is_null`);
   - `q == null` / `q != null`, where null is a constant integer 0, a cast of one (`0 as *mut T`), or
     `ptr::null()` / `null_mut()`;
   - `discriminant(o)` with `o = q.as_ref()` / `q.as_mut()` (`if let Some(_) = q.as_ref()`, `opt-discr`);
   - `Option::is_some(&o)` / `is_none(&o)` with the same `o` (`opt-is_some` / `opt-is_none`).

   `if !p.is_null()` produces no `Not` statement: `then_else_break` swaps the arms (`builder/matches/mod.rs:166-191`).
   So the switch is on the `is_null` result itself, and the non-null arm is its value-0 target. A `Not` statement
   (`let c = !p.is_null(); if c`) is handled by flipping the polarity: `if c` switches on a temporary copy of `c`
   (`then_else_break_inner`'s default arm, `as_temp`, `matches/mod.rs:210-226`), whose single definition leads to `c`,
   whose single definition
   is `Not(is_null(..))`.
2. **Non-null successor S.** S is the switch target for the non-null outcome. It counts only if it has **exactly one
   predecessor** (the switch block), so that S dominating a block means the edge dominates it.
3. **Same place.** The tested `q` and the site's pointer are each resolved to a place (`canon`) through
   single-definition temporaries, `Use`, `PtrToPtr` / `PointerCoercion` casts, `CopyForDeref` and `cast()` /
   `cast_mut()` / `cast_const()`. When the resolved place is a `Deref` of a temporary `t`, and
   `t = Option::unwrap / expect / unwrap_unchecked(t1)`, `t1 = Option::as_ref / as_mut / as_deref / as_deref_mut(t2)`,
   `t2 = &(mut) base`, the place becomes `base`'s `Some` payload (one more `Deref` for `as_deref(_mut)`) followed by
   the rest of the projection. This is CROWN's quadtree shape (`node.rs:121-133`): the test reads
   `(*node.as_deref().unwrap()).nw` and the site `(*node.as_deref_mut().unwrap()).nw` through two different call-result
   temporaries, and both now resolve to `node`·payload·`*`·`nw`. It is sound for place equality: the same receiver
   place, the same accessor meaning (`as_ref` ≡ `as_mut`, `as_deref` ≡ `as_deref_mut`), the same field path. The two
   places (local plus steps) must be equal, so a test on `(*s).q` matches a site on `*(*s).q`. If the site's pointer
   was resolved through an `offset` / `add` / `sub` / `wrapping_*` / `byte_*` call, the value is `yes-base…` rather
   than `yes…`.
4. **Dominance.** S must dominate the site's block (`body.basic_blocks.dominators()`; a site block that is not
   reachable is `no`, because `Dominators::dominates` asserts reachability, `dominators/mod.rs:384`).
5. **Value, not only place.** Place equality does not prove the pointer *value* is the tested one
   (`if p.is_null() { return } loop { let r = &*p; …; p = (*p).next; }`). So the place-only result is split:
   - `yes` (and `yes-base`): no statement or terminator on any path from the test's read of the place (the earliest
     definition `canon` walked, or the test itself) to the site can change the value, and every read the site's own
     resolution walked lies in a block S dominates. The paths are the blocks reachable forward from the read and
     backward from the site without re-entering the read's block (a re-entry re-reads), plus the rest of the site's
     block when a cycle through it avoids the read's block. A **kill** is: an assignment / `SetDiscriminant` /
     `Deinit` / `StorageLive` / `StorageDead` of the root local, a call writing it, a `Drop` of it, inline asm or a
     `Yield`. When the place holds a `Deref` (a field test such as `(*s).q`) or the root's address is taken anywhere
     in the body, the proof is **strict**: in addition, any store through a `Deref`, any `Drop`, any
     `Intrinsic` (`copy_nonoverlapping`) and any call other than the pure std accessors (`pure_call`: the raw-pointer
     arithmetic and conversion methods, `Option`'s `as_ref / as_mut / as_deref(_mut) / unwrap / expect / is_some /
     is_none`, `Box::from_raw`, `NonNull` accessors, `ptr::null(_mut)`, `slice::from_raw_parts(_mut)`, `as_ptr` /
     `as_mut_ptr` / `len`) is a kill.
   - `yes-place` (and `yes-base-place`): the place is equal and dominated, the value proof fails.

   `summary.tsv` reports the four separately (`b_box_nd_yes`, `b_box_nd_yes_place`, `b_box_nd_yes_base`,
   `b_box_nd_yes_base_place`, and the same for `b_asrefmut`); nothing merges them.

`null_test` names the test used and its line (`is_null@L`, `eq-null@L`, `ne-null@L`, `opt-discr@L`, `opt-is_some@L`,
`opt-is_none@L`). When several tests match, a `yes` one is preferred to a `yes-place` one.

Stated approximations:

- An `Option` check is recognized only on `as_ref` / `as_mut` of the same pointer.
- `&&` chains are covered by dominance. For `||`: `if p.is_null() || c { return; } site` yields `yes`, which is
  correct (the non-null successor of the `is_null` switch is the block that evaluates `c`, and it dominates the
  continuation); only `if !p.is_null() || c { site }` yields `no`, because the site is reached through `c` without the
  test. A test under another `if` that does not dominate the site (toy t32) is `no`.
- A test inside a callee is not seen.
- `pure_call` trusts std's accessors; `Option::as_deref(_mut)` on a payload with a user `Deref` impl would run user
  code (c2rust output defines none).

## 6. The toy: expected rows (written before any run)

`toy/expected.tsv` holds the 76 expected rows over 75 tagged lines; `run.py toy` checks them. Its columns are
`tag fn kind call dest dest_detail formal_ty formal_safe via excluded excl_reason null_dom null_test src_ty raw_derefs
post_raw_derefs in_wrapper macro`. Matching (`run.py field_ok`): `*` = not checked; `re:<regex>` = `re.search`; `-` =
exact; `fn`, `call`, `formal_ty`, `via`, `null_test` and `src_ty` are substrings (type strings print with paths, tests
with lines), as is `dest_detail` for call-arg rows; every other column is exact. Every row not listed is UNEXPECTED: in
particular `n01_rawonly` (`(*p).x += 1`, `&raw mut (*p).x`, `(*p.offset(1)).x`) and `n02_safe` (`let r2 = &mut *r` with
r: `&mut i32`; `&mut *b` and `&mut b.x` with b: `Box<S>`) must produce none. The toy run also fails unless
`sites-status.txt` says `ok`.

| tag | case | kind | dest / detail | excl | null_dom | wrapper |
|---|---|---|---|---|---|---|
| t01 | `let r = &mut *p` | a:mut-ref | decl r | no | no | no |
| t02a / b | `let mut r: &i32 = &*p;` / `r = &*q;` | a:ref | decl r / assign r | no | no | no |
| t03 | `&mut *p` as the tail (`-> &'a mut i32`) | a:mut-ref | return (via reborrow) | no | no | yes |
| t04 | `safe_mut(&mut *p)` | a:mut-ref | call-arg safe_mut, safe | no | no | no |
| t05 | `safe_opt(Some(&mut *p.offset(1)))` (the CROWN brotli shape) | a:mut-ref | call-arg safe_opt, safe, via Some | no | no | no |
| t06 | `(*v).push(1)` (autoref) | a:mut-ref | call-arg Vec::push, safe | no | no | no |
| t07 | `h.f = &mut *p` | a:mut-ref | field-store Holder.f | no | no | no |
| t08 | `Holder { f: &mut *p }` returned | a:mut-ref | field-store init:Holder.f>return | no | no | yes |
| t09 | `&mut *p.offset(2) as *mut i32` returned | a:mut-ref | return (of the raw value) | **yes** rawptr-of-deref | no | no |
| t10 | `strncmp(&mut *s.offset(1), &*t, 3)` (the Laertes libtree shape) | a:mut-ref + a:ref | call-arg strncmp, raw, formal `*const i8` | **yes** ×2 | no | no |
| t11 | `takes_raw(&mut *p as *mut i32 as *mut i32)` | a:mut-ref | call-arg takes_raw, raw | **yes** | no | no |
| t12 | `&mut *a as *mut i32`, `a: *mut [i32; 4]` | a:mut-ref | return | **yes** | no | no |
| t13 | `(&mut *p).x` | a:mut-ref | other deref-use | no | no | no |
| t14 | `if !p.is_null() { let r = &*p; .. }` | a:ref | decl r | no | **yes** is_null | no |
| t15 | `if p.is_null() { return None; } p.as_mut()` | b:ptr-as_mut | return | no | **yes** is_null | yes |
| t16 | `*p.as_ref().unwrap()` | b:ptr-as_ref | other deref-use (via unwrap) | no | no | no |
| t17 | `if let Some(r) = p.as_mut()` | b:ptr-as_mut | decl r (via match-some) | no | no | no |
| t18 | `if !p.is_null() { drop(Box::from_raw(p)) }` | b:box-from_raw | call-arg drop, safe | no | **yes** is_null | no |
| t19 | `let _ = Box::from_raw(p)` | b:box-from_raw | other drop | no | no | no |
| t20 | `if p != ptr::null_mut() { let b = Box::from_raw(p); .. }` | b:box-from_raw | decl b | no | **yes** ne-null | no |
| t21 | `if p == 0 as *mut S { return 0; } let b = Box::from_raw(p)` | b:box-from_raw | decl b | no | **yes** eq-null | no |
| t22 | `let s = slice::from_raw_parts(p, n)` | b:slice-from_raw_parts | decl s | no | no | no |
| t23 | `safe_slice(slice::from_raw_parts_mut(p, n))` | b:slice-from_raw_parts_mut | call-arg safe_slice, safe | no | no | no |
| t24 | `*p.as_ref()`, `p: NonNull<i32>` | b:nonnull-as_ref | other deref-use; src_ty `NonNull<i32>` | no | n/a | no |
| w1 | `mk_ref(p) -> &mut i32 { &mut *p }` | a:mut-ref | return | no | no | yes |
| w2 | `mk_ref2(p: *const) { mk_ref(p as *mut i32) }` | h mk_ref | return | no | no | yes |
| t25a / b | `safe_mut(mk_ref(p))` / `let r = mk_ref2(p)` | h | call-arg safe_mut / decl r | no | no | no |
| w3 | `Cur::from_raw` = `Cur { base: from_raw_parts(p, n), pos: 0 }` (the SliceCursor shape) | b:slice-from_raw_parts | field-store init:Cur.base>return | no | no | yes |
| t26 | `let c = Cur::from_raw(p, 3)` | h | decl c | no | no | no |
| t27 | `|| unsafe { &mut *p }` | a:mut-ref in `t27_closure::{closure#0}` | return | no | (not checked) | no |
| t28 | `transmute::<*mut i32, &mut i32>(p)` returned | x:transmute | return | no | no | yes |
| t29 | `let c = CStr::from_ptr(s)` | x:cstr-from_ptr | decl c | no | no | no |
| t30 | `if !(*s).q.is_null() { let r = &mut *(*s).q; .. }` | a:mut-ref (raw_derefs 2) | decl r | no | **yes** (field place, strict proof, nothing between) | no |
| t31 | `if !p.is_null() { let r = &*p.offset(1); .. }` | a:ref | decl r | no | **yes-base** | no |
| t32 | `if flag { if p.is_null() { return 0; } } let r = &*p` | a:ref | decl r | no | no (not dominating) | no |
| t33a | `if p.as_ref().is_some()` | b:ptr-as_ref | other observed-only | no | no | no |
| t33b | `.. { drop(Box::from_raw(p)) }` | b:box-from_raw | call-arg drop, safe | no | **yes** opt-is_some | no |
| t34 | `*pp = &mut *p` | a:mut-ref | other store-deref | no | no | no |
| t35 | `let rx = &mut (*p).x` | a:mut-ref | decl rx | no | no | no |
| t36 | `Some(&mut *p)` returned | a:mut-ref | return (via Some) | no | no | yes |
| t37 | `let ref mut fresh0 = *p.offset(1)` (c2rust) | a:mut-ref | decl fresh0 | no | no | no |
| t38 | `let r = &mut *p; r as *mut i32` | a:mut-ref | decl r (a variable is never "only a cast") | no | no | no |
| t40 | `(*h).b = Some(Box::from_raw(p))` (drop-and-replace) | b:box-from_raw | field-store BoxHolder.b@raw (via Some; the operand's normal-path drop ignored, §3) | no | no | no |
| t42 | `(*b).vals.as_mut_ptr()` returned, `vals: [i32; 4]` | a:mut-ref | return | **yes** method-to-raw | no | no |
| t43 | `takes_rawc((*b).vals.as_ptr())` | a:ref | call-arg takes_rawc, raw | **yes** method-to-raw | no | no |
| t44 | `(*b).v.as_mut_ptr()` returned, `v: Vec<i32>` | a:mut-ref | return | **yes** method-to-raw | no | no |
| t45 | `(*s).as_ptr()` returned, `s: *const str` | a:ref | return | **yes** method-to-raw | no | no |
| t46 | `(*b).vals.len()` (control: a non-raw method) | a:ref | call-arg `<[i32]>::len`, safe | no | no | no |
| t50a / b | `if let Some(_) = p.as_ref() { drop(Box::from_raw(p)) }` | b:ptr-as_ref / b:box-from_raw | other observed-only / call-arg drop | no | no / **yes** opt-discr | no |
| t51 | `let c = !p.is_null(); if c { drop(Box::from_raw(p)) }` | b:box-from_raw | call-arg drop | no | **yes** is_null (Not statement) | no |
| t52a / b | `if p.as_ref().is_none() { return 0; } let b = Box::from_raw(p)` | b:ptr-as_ref / b:box-from_raw | other observed-only / decl b | no | no / **yes** opt-is_none | no |
| t53 | `if p == ptr::null() { return 0; } let r = &*p` | a:ref | decl r | no | **yes** eq-null | no |
| t54 | `__crat_safe_t54(if p.is_null() { None } else { Some(Box::from_raw(p)) })` (our exposure shape) | b:box-from_raw | call-arg `__crat_safe_t54` (boundary), via Some | no | **yes** is_null | no |
| t55 | `if !(*node.as_deref().unwrap()).nw.is_null() { qfree(Some(Box::from_raw((*node.as_deref_mut().unwrap()).nw))) }` (CROWN quadtree) | b:box-from_raw | call-arg qfree, via Some | no | **yes** (accessor canon; only pure calls between) | no |
| t56a / b | `let v = Vec::from_raw_parts(p, n, n)` / `let r = Rc::from_raw(p as *const i32)` | x:vec-from_raw_parts / x:rc-from_raw | decl v / decl r | no | no | no |
| t57 | `&raw mut (&mut *p).x` returned | a:mut-ref | return | **yes** rawptr-of-subplace | no | no |
| t58 | `let s = &*ptr::slice_from_raw_parts(p, n)` | a:ref (src_ty `*const [i32]`) | decl s | no | no | no |
| t59 | `safe_mut(deref_mut!(p))`, the macro expanding to `&mut *$p` | a:mut-ref, macro yes | call-arg safe_mut | no | no | no |
| t60a / b | `let a = &mut *(*p).r` (r: `&'static mut i32`) / `let c = &(*p).b.x` (b: `Box<S>`) | a:mut-ref / a:ref, post_raw_derefs 1 | decl a / decl c | no | no | no |
| t61 | `if p.is_null() { return 0; } loop { let r = &*p; ..; p = (*p).next; if p.is_null() { break } }` | a:ref | decl r | no | **yes-place** (p reassigned on the loop path) | no |
| t62 | `if !(*s).q.is_null() { opaque(); let r = &*(*s).q; .. }` | a:ref | decl r | no | **yes-place** (a call between, strict proof) | no |
| t63 | `r = &*p` with `r` a formal | a:ref | assign r | no | no | no |
| t64 | `a[1] = &mut *p`, `a: &mut [&'static mut i32; 2]` | a:mut-ref | other elem-store | no | no | no |
| t65 | `let _ = &*p;` | a:ref | other unused | no | no | no |
| t66 | `let t = (&mut *p, 1);` | a:mut-ref | other `elem:tuple.0>decl` | no | no | no |
| t67 | `let r; r = &mut *p;` | a:mut-ref | assign r (no initializer) | no | no | no |
| t68 | `let b = Some(Box::from_raw(ptr::slice_from_raw_parts_mut(p, n)))` (brotli's shape) | b:box-from_raw | decl b (via Some; drop ignored, single-def-with-initializer rule) | no | no | no |
| w4a / b | `w4_mixed(p, q) { safe_mut(&mut *q); &mut *p }` | a:mut-ref ×2 | call-arg safe_mut / return | no | no | **no** / yes (per row) |

Predictions most at risk (they rest on MIR shapes reasoned rather than observed):

- t17: the pattern binding is a single definition with no `ForLet` read; it is `decl` by the single-definition rule
  (its `opt_match_place` is `Some`, `lower_let_expr`, `matches/mod.rs:2383-2392`).
- t19: the `let _` temporary's only live use is its `Drop`.
- t27: the closure's capture shape; only kind and dest are checked.
- t33a, t50a, t52a: the scrutinee / autoref temporary is only observed (a shared borrow of the whole temporary, a
  discriminant read, a `PlaceMention`).
- t40, t54, t55, t68: depend on the drop-after-move rule (§3) and, for t40, on the cleanup skip.
- t50b: the `Some` target of the variant switch is a fresh block with one predecessor (`test_candidates`' branch
  blocks, `matches/mod.rs:2318`).
- t55: the accessor canonicalisation and the strict proof's `pure_call` list (`as_deref_mut`, `unwrap`, `is_null`).
- t59: the borrow statement's span is the macro's (`from_expansion`), reported at the call site.
- t64 / t65: the assignment lowers rhs-first (`expr/stmt.rs`, Assign) and `let _ =` evaluates into an unused
  temporary (`expr_into_pattern`'s wildcard arm, `matches/mod.rs:674-679`).
- t68: the `FakeRead(ForLet)` lands after the operand's `Drop`, in the next block (`expr_into_pattern`,
  `matches/mod.rs:598-610`, pushes it after `expr_into_dest` returns past the Adt scope's exit), so `is_let_write`
  misses it and the single-definition-with-initializer rule must give `decl`.

A failure is a finding about either the counter or the prediction, and is resolved before any corpus run, within
MAX-3.

## 7. Corpus checks (`out/spot.txt`)

`run.py summarize` checks the relay's three known examples, and the null-dominance example the review named:

- **CROWN** `brotli/src/enc/histogram.rs:150-151`: `HistogramAddCommand(Some(&mut *insert_and_copy_histograms.offset(..)), ..)`,
  where `insert_and_copy_histograms` is the caller's `*mut` parameter at `:119`. Expected: an a:mut-ref row, not
  excluded, `call-arg HistogramAddCommand` via `Some`. Its `formal_ty` shows whether the callee takes `Option<&mut _>`.
- **CROWN** `b:box-from_raw` rows in quadtree + json.h = **9**. The source text holds exactly 9 `Box::from_raw`
  (quadtree 7, json.h 2).
- **CROWN** of those 9, **4 are null-dominated**, read from the source on 10-10: `quadtree/src/src/node.rs:123`, `:126`,
  `:129`, `:132`, each `quadtree_node_free(Some(Box::from_raw((*node.as_deref_mut().unwrap()).<f>)), ..)` under
  `if !(*node.as_deref().unwrap()).<f>.is_null()` for f = nw / ne / sw / se. The other five have no test: `node.rs:77`
  (`(*node).point` in `quadtree_node_reset`), `node.rs:134` (`bounds`, after the four ifs), `quadtree.rs:212` (a call
  result) and `json.rs:2273` / `:2286` (call results). The check passes when exactly those four keys have a non-`no`
  value; the line prints the yes / yes-place / yes-base / yes-base-place split and every row's value (predicted: 4
  `yes`, since only `as_deref_mut` / `unwrap` run between the test and the site).
- **Laertes** `libtree/src/libtree.rs:1199`: `strncmp(&mut *((*(borrow(&st)).unwrap()).arr).offset(curr_src as isize), ..)`.
  Expected: an a:mut-ref row, **excluded** `rawptr-of-deref`, `call-arg strncmp`, `formal_safe=raw`.

A program is read only when `status.txt` and `sites-status.txt` both say `ok`.

## 8. Build and invocation per side

**Build** (031 / 043 built the same way, through `pos_census.build()` into `r043/target`). `run.py build` runs, with
`RUSTUP_TOOLCHAIN=nightly-2025-06-23 CARGO_TARGET_DIR=r132/target CARGO_INCREMENTAL=0 CRAT_LANE=analysis-fanout`:

```
bash docs/agents/tools/crat-cargo.sh build --release --offline \
     --manifest-path scratch/analysis-fanout/r132/counter/Cargo.toml
```

`crat-cargo.sh` takes one of the build slots and runs cargo under `nice -n 10 ionice -c2 -n7`. The run quotes the
`Compiling rq2_site_counter` line and refuses a line that does not point into r132. The binary is
`r132/target/release/rq2_site_counter`. Compile errors follow the anti-loop rule (MAX-3, then stop with the log).

**Per tree** (pos_census.py's invocation, plus `--sites`, without `--universe` / `--strip-src`, which only key T2):

```
SYSROOT=$(rustc +nightly-2025-06-23 --print sysroot) LD_LIBRARY_PATH=$SYSROOT/lib DIR=crat \
RUSTUP_TOOLCHAIN=nightly-2025-06-23 \
nice -n 10 /usr/bin/time -f 'wall=%e maxrss_kb=%M' r132/target/release/rq2_site_counter \
     --root <root> --out r132/out/<side>/<p> --sites
```

The driver configuration is the census's (edition 2021, rlib, deps_crate's rlibs as externs, lints capped at allow).
`<root>` = `pos_census.root_of(<tree>)`: `lib.rs`, `c2rust-lib.rs`, `src/lib.rs`, `rust/src/lib.rs`, or `test.rs`.
Programs run one at a time behind the MemAvailable floor (40 GiB).

| side | trees | notes |
|---|---|---|
| `input` | `crat/benchmarks/rs-crown/<p>` (20) | the control: c2rust's own `&mut *` idioms (`fresh` refs, coercion casts) |
| `crown` | `crat/benchmarks/rs-crown-transformed/<p>` (20) | as distributed (031: whole = joined on all twenty) |
| `laertes` | `seed_rq2.laertes_root(p)`, i.e. `crown-artifact/comparison/laertes-crown/after/<p>` for avl binn bst buffer heman ht json.h libtree lodepng quadtree rgba (11) and `laertes-laertes/after/<dir of laertes-path>` for bzip2 genann libcsv lil robotfindskitten tulipindicators urlparser libzahl (8); brotli has no tree | 031's E0557 feature-gate shim when rustc reports a removed gate (in 043: `const_raw_ptr_to_usize_cast` and `main` for bzip2 genann lil robotfindskitten tulipindicators urlparser, `const_raw_ptr_to_usize_cast` for libzahl), into `out/shimroot/shim/laertes/<p>`. libzahl first gets r117's `adapt_llvm_asm.py`, unchanged (29 `llvm_asm!` sites to `asm!(.., options(att_syntax))`), into `out/adapted/laertes/libzahl/tree`, then the shim (relay 116/117's order) |
| `ours56` | `scratch/main/batch56/emitted-trees/<p>` (20) | batch 56 (`batch56-done`: DONE) |
| `ours58` | `scratch/main/batch58/emitted-trees/<p>` | runs only once `main/batch58-done` exists (19 of 20 trees present at 12:2xZ) |

`run.py all` runs these steps in order: build, then the toy (a failure stops everything), then the five sides, then
`summarize` and `spot`. It refuses to start while `CORPUS-SLOT.lock` exists unless `--beside-lock` is given, and it
re-checks the lock before each side.

## 9. Outputs

- `out/<side>/<p>/sites.tsv`: one row per site, with the 21 columns in `sites.rs`'s header (`post_raw_derefs` is new).
- `out/<side>/<p>/sites-status.txt`: `ok\t<rows>`, or `panic\t<message>` when the site pass panicked (main.rs runs it
  under `catch_unwind`, so T1 / T2's `positions.tsv` / `uses.tsv` / `status.txt` are still written). A program counts
  only when both statuses are `ok`; otherwise `summary.tsv` shows `sites-panic` / `sites-no-sites-status`. If the driver
  dies before writing `status.txt`, `run.py` writes `exit-<rc>` itself (as `run_t5.py` does); a tree without a crate
  root is `no-root`.
- `out/summary.tsv`: one row per side × program, plus TOTAL. Columns:
  - `ab`: a + b, not excluded;
  - `ab_not_in_wrapper` (per row: excludes only the wrapping conversions);
  - `a`, split into `a_direct` (`post_raw_derefs` = 0) and `a_via_safe` (> 0: a reborrow of a safe reference / `Box`
    loaded through a raw pointer);
  - `a_decl_fresh`: c2rust `freshN` bindings;
  - `b_box` and its null-dominance split `b_box_nd_yes`, `b_box_nd_yes_place`, `b_box_nd_yes_base`,
    `b_box_nd_yes_base_place`; `b_asrefmut` with the same four `b_asrefmut_nd_*`; `b_slice`, `b_nonnull`;
  - `x`, `h`, `excluded`, `excluded.method-to-raw`;
  - the destination split `ab.call-arg{,.safe,.raw,.other,.boundary}`, `ab.decl`, `ab.assign`, `ab.return`,
    `ab.field-store`, `ab.other`.
- `out/summary-long.tsv`: side × program × family × kind × excluded × excl_reason × dest × formal_safe × null_dom ×
  in_wrapper × boundary × post_raw (`via-safe` / `-`), with counts.

## 10. Rules kept

- Writes only under `r132/`. The docs tools (`pos_census.py`, `seed_rq2.py`) are imported read-only, with bytecode
  writing off.
- Never edits crat source, never stashes, never pushes, never kills by pattern, and never loads a model-cache entry
  (the counter reads only source trees).
- Nothing was built or run on 10-10 while batch 58's census held the lock, neither for the first version nor for the
  review fixes below.

## 11. Changelog: the 10-10 review (`prep-results.json`, the object with `defects`)

Line numbers are those of the revised files. Nothing below has been compiled; every MIR claim cites the rustc source
of nightly-2025-06-23.

| # | defect (review severity) | fix | where |
|---|---|---|---|
| 1 | [HIGH] null dominance misses CROWN's guarded `Box::from_raw` (quadtree `node.rs:121-133`): `canon` stopped at a non-empty projection, and the test and the site read the field through different call-result temporaries (`as_deref().unwrap()` vs `as_deref_mut().unwrap()`), so 0 of the 4 guarded sites were dominated | `canon` resolves a `Deref` of a temporary defined by `Option::unwrap / expect / unwrap_unchecked` of `Option::as_ref / as_mut / as_deref / as_deref_mut(&(mut) base)` to `base`'s payload (+ `Deref` for `as_deref*`) followed by the rest of the projection; canonical places are now `Step` lists (`P(elem)` / `Payload`), equal only for the same receiver place, accessor meaning and field path. spot.txt checks that exactly the four quadtree keys (`node.rs:123/126/129/132`) are null-dominated; toy t55 | `counter/src/sites.rs:582-598` (`Step`, `Canon`), `:736-743` (`call_at`), `:747-781` (`accessor`), `:783-841` (`canon`); `run.py:384-405` (spot); `toy/lib.rs` t55 |
| 2 | [HIGH] the exclusion misses c2rust's method-form address idiom `(*buff).vals.as_mut_ptr()` / `.as_ptr()` (autoref, possibly unsized to a slice, used only as the receiver of a raw-returning std method); ≥ 108 input / ≥ 184 CROWN sites counted as `call-arg safe` | a reference whose only use (through temporaries, incl. the unsizing coercion) is argument 0 of a core / std / alloc method `as_ptr / as_mut_ptr / as_ptr_range / as_mut_ptr_range` with a raw (or `Range`-of-raw) result is excluded, `excl_reason = method-to-raw`; the chase follows the raw result; `summary.tsv` counts it in `excluded` and in `excluded.method-to-raw`; toy t42-t45 (t46 `.len()` the control) | `counter/src/sites.rs:195-209` (`method_to_raw`, `returns_raw`), `:1286-1300` (chase); `run.py:311` (counter), `:286` (column) |
| 3 | [MED] `null_dom = yes` compared places, not values (`p = (*p).next` on a loop path, a store into `(*s).q`, a call between), and the summary counted those straight in | `yes` now requires the value proof: no kill on any path from the test's read to the site (root-local writes; in strict mode, when the place holds a `Deref` or the root's address is taken, also stores through a `Deref`, `Drop`s, intrinsics, inline asm and calls outside `pure_call`), and the site's own reads after S; otherwise `yes-place` (`yes-base` / `yes-base-place` for offsets). The summary has four separate columns per family, never merged; toy t61 (reassignment) and t62 (a call) are `yes-place`, t55 (pure calls only) `yes` | `counter/src/sites.rs:211-257` (`pure_call`), `:645` + `:670-686` (`addr_taken`), `:965-993` (`null_facts` keeps the read point), `:995-1026` (`null_info`), `:1030-1114` (`reach`, `clear`, `seg_ok`, `kills_*`); `run.py:282-289` (columns), `:327-335` (counts) |
| 4 | [MED] expected.tsv lacked `via`, `null_test`, `raw_derefs`, `formal_ty`, `src_ty`, so DESIGN §6's stated values were never checked | expected.tsv has all of them (plus `post_raw_derefs`, `macro`), filled where §6 states them and where the printed value is certain, `*` elsewhere; `run.py` checks every column (`field_ok`: `*`, `re:`, substring for type / test / via columns, exact otherwise) | `toy/expected.tsv`; `run.py:210-224` (`FIELDS`, `field_ok`), `:253-257` (the check) |
| 5 | [MED] toy gaps | added: explicit negatives `n02_safe` (`&mut *r` of a reference, `&mut *b` / `&mut b.x` of a `Box`); opt-discr dominance t50; the `Not`-statement polarity t51; `is_none` t52; `ptr::null()` t53; our exposure wrapper's `Option<Box>` argument t54; CROWN's accessor shape t55; reassignment / call between t61 / t62; `x:vec` / `x:rc` t56; `rawptr-of-subplace` t57 (`cast-to-raw` is unreachable from source, §4); `&*ptr::slice_from_raw_parts` t58; a macro span t59; derefs after a raw deref t60; assign-to-formal t63; `elem-store` t64; `unused` t65; a tuple element t66; `let r; r = ..` t67; brotli's `Some(Box::from_raw(slice_from_raw_parts_mut(..)))` t68; a wrapper's non-wrapping row w4a. (`multi-use` has no clean source shape in the toy and stays unexercised.) | `toy/lib.rs`, `toy/expected.tsv` (76 rows / 75 tagged lines) |
| 6 | [LOW-MED] kind a counted a reborrow of a safe reference / `Box` loaded through a raw pointer together with a reference made from the raw pointer itself | new column `post_raw_derefs` (non-raw `Deref`s after the last raw one); `summary.tsv` splits `a` into `a_direct` / `a_via_safe`; summary-long carries `post_raw`; toy t60 | `counter/src/sites.rs:1378` (count), `:1556` (header); `run.py:304`, `:322-324` |
| 7 | [LOW] `in_wrapper` was per function, so `ab_not_in_wrapper` dropped every site in a wrapper's body and an uncalled wrapper's conversion | `in_wrapper` = `wraps(r).is_some()` per row | `counter/src/sites.rs:1512`; toy w4 |
| 8 | [LOW] a panic in `sites::sites` (e.g. `Dominators::dominates` on an unreachable block) aborted the driver after `status.txt` was deleted; `run.py` wrote no status on a crash; `P.root_of(d)` could be `None` | `main.rs` runs the pass under `catch_unwind` and writes `sites-status.txt` (`ok` / `panic`), keeping T1 / T2; `null_info` checks `is_reachable` before `dominates`; `run.py` writes `exit-<rc>` when the driver left no status (run_t5.py's rule), writes `no-root` for a tree without a crate root, and counts a program only when both statuses are `ok` | `counter/src/main.rs:614` (cleared), `:638-651` (catch_unwind), `:658-670` (sites-status.txt); `counter/src/sites.rs:1003-1006`; `run.py:166-170` (no-root), `:183-186` (crash status), `:192-206` (`sites_status`, `row_status`), `:233-234` (toy) |
| 9 | [LOW] DESIGN.md said `||` yields `no` | §5 states it exactly: `if p.is_null() || c { return; } site` is `yes` (correct), only `if !p.is_null() || c { site }` is `no` | `DESIGN.md` §5 |
| 10 | [LOW] destination labels | `let r; r = &mut *p` is `assign` (the single-definition rule now requires an initializer / match place, `VarBindingForm::opt_match_place`); tuple / array / array-repeat / closure-capture aggregates are `other elem:<what>>DEST`, not `field-store`; a union literal names its active field | `counter/src/sites.rs:730-734` (`bound_with_place`), `:1204-1206` (decl rule), `:441-460` (aggregates, union), `:1256-1272` (chase); toy t66, t67 |
| 11 | [LOW] `StatementKind::BackwardIncompatibleDropHint` was not ignored (would turn a single-use temporary into multi-use) | ignored in `index_uses` and `is_let_write` | `counter/src/sites.rs:500`, `:1137` |
| 12 | [LOW] `b:nonnull-*` `src_ty` was `&NonNull<T>` | the receiver's pointee, `NonNull<T>` (`builtin_deref`) | `counter/src/sites.rs:1416`; toy t24 |
| N1 | (found while fixing 1 / 5, not in the review) a moved aggregate / assignment operand temporary still has a normal-path `Drop` in `mir_built` (only call arguments are unscheduled, `record_operands_moved`), so every `Some(Box::from_raw(..))` — t40, our exposure shape t54, CROWN's quadtree calls, brotli's `Some(Box::from_raw(..))` — read as `multi-use:wrap,drop` | a temporary with exactly one non-`Drop` use that moves it ignores its `Drop`s (§3); the decl rule's second arm covers the `FakeRead(ForLet)` that then lands in the next block (t68) | `counter/src/sites.rs:337-341` (`Use::moves`), `:1212-1216` (chase) |
| N2 | (found while fixing 3) `opt-is_some` labelled an `is_none` test too | `opt-is_none` | `counter/src/sites.rs:957` |
