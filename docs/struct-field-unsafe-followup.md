# Struct Field Unsafe Follow-Up

Until the struct-field unsafe reduction work is finished, start each follow-up
by consulting the merged evidence artifacts in the workspace root:

- `/workspace/crat-workspace/struct-field-unsafe-usage-merged-20260527.md`
- `/workspace/crat-workspace/struct-field-unsafe-usage-merged-20260527.csv`
- `/workspace/crat-workspace/struct-field-unsafe-usage-merged-20260527.jsonl`
- `/workspace/crat-workspace/struct-field-unsafe-spans-merged-20260527.jsonl`

From the main Crat checkout these are also available as
`../struct-field-unsafe-usage-merged-20260527.*`.

Current next track: continue reducing pointer-field-specific unsafe usage,
especially the broader `raw_pointer_struct_field_deref` bucket beyond the small
field-base cleanup already committed. Prefer a task with an unsafe-count win;
avoid more correctness-only groundwork unless it directly unlocks a measured
reduction.

## Handled So Far

- `adb11bd` (`Simplify promoted ref field access`) handled the small field-base
  cleanup for already-promoted struct roots. Direct field expressions such as
  `(*node).next` can now simplify to safe field access when `node` has already
  become a reference, while address-taken field bases are preserved for raw
  boundary adapters.
- `c65a68f` (`Allow thin C ABI field promotion`) partially handled
  pointer-field dereferences on thin C-exposed struct inputs. Nullable pointer
  fields on simple ABI structs can promote to `Option<&T>` / `Option<&mut T>`,
  while wider ABI-sensitive cases, slice-element structs, allocator-owned
  `strdup` storage, and cursor-tainted offset aliases remain raw.
- `b413380` (`Promote bounded field pointer aliases`) handled a bounded
  fixed-array alias subset of `field_root_offset` / local field-alias evidence.
  Initializers like `let p = (*root).buffer.as_mut_ptr()` can promote to a slice
  when the root is borrow-like, mutability is compatible, offset use does not
  require cursor behavior, and later root uses are disjoint field projections.
  Same-field reuse, local/unbounded index offsets, static roots, and dynamic
  pointer buffers still stay raw.
- The current uncommitted session added a conservative shared pointer-field
  alias rule for no-op casts such as
  `let next: *const Node = (*current).next as *const Node`. It only applies when
  the field itself is already promoted, the root is borrow-like, the pointee
  types match, and the alias is shared-only. This passed smoke/full/vector
  evaluation but did not reduce benchmark unsafe totals, so treat it as a
  correctness guard rather than a measured unsafe-reduction win.
- The next uncommitted session explored the high-frequency
  `field_offset;local_alias_to_field_root;raw_deref_field` subshape by promoting
  shared local aliases initialized from pointer-field `.offset` / `.add` /
  `.wrapping_offset` calls to `SliceCursor`. The initial version reduced unsafe
  totals by 6 in smoke/full, but full vectors caught an ABI regression in
  `Public-Tests/B01_organic/read_side_info_lib`: the exported `bs_t` struct's
  `buf` field became a `SliceCursor`, changing the `repr(C)` layout observed by
  the C-compatible harness. The final guarded version keeps cursor-tainted
  fields raw for structs reached through C-exposed pointer inputs while still
  allowing internal non-C-exposed cursor aliases. Final validation passed, but
  unsafe totals returned to baseline (`20263` smoke, `70395` full), so this is
  also correctness groundwork, not the desired unsafe-count-winning track.

## Still Open

- The broad pointer-field-specific `raw_pointer_struct_field_deref` bucket is
  still the main opportunity: the merged evidence shows 1073 pointer-field rows
  across 24 cases. Prior work only covers direct safe roots and a narrow shared
  local-alias shape.
- Dynamic pointer fields with offset, sentinel `from_raw_parts`, allocation/free
  ownership, unsafe call-boundary adapters, function-pointer fields, mutable
  statics, and broad mutable local aliases remain out of scope until a targeted
  pattern is selected from the merged span evidence.
- For the next session, skip C-exposed cursor-field layout rewrites unless the
  interface layer can preserve ABI. Mine the merged span evidence for a
  non-C-exposed or ABI-neutral subshape whose benchmark rows can plausibly move
  the unsafe total, and write the red test from that concrete corpus evidence.

## 2026-05-28 Evidence Pass

- Aggregating `raw_pointer_struct_field_deref` by pointer-field-only rows shows
  the biggest pointer-field local-alias shapes are still:
  `field_offset;local_alias_to_field_root;raw_deref_field` (348 rows),
  `local_alias_to_field_root;raw_deref_field` (226 rows), and
  `field_mut_borrow;field_offset;local_alias_to_field_root;raw_deref_field`
  (80 rows). Most high-count cases are C-exposed or ownership-heavy.
- `Public-Tests/B02_synthetic/generic_foreach` has many `data;size` rows, but
  its config exposes the array/list APIs. Promotion diagnostics show 8 candidate
  mutable fields, all shape-demoted, with `raw_storage_allocator` on all 8 and
  `raw_binding_from_field` / `raw_pointee_field_move` on the array `data`
  fields. This is not a quick ABI-neutral pointer-field alias win.
- `Public-Tests/B02_synthetic/memcpy_fun_buffers` is ABI-neutral
  (`c_exposed_fns = []`) and has 34 pointer-field rows around
  `buffer_array_t.buffers`. Diagnostics show one candidate field
  (`src::main::buffer_array_t.buffers`, 23 promoted-field uses), but it is
  shape-demoted and blocked by `raw_storage_allocator` plus
  `raw_pointee_field_move`. Treat this as a possible boxed-slice/length-recovery
  track, not a local-alias-only change.
- `Public-Tests/B02_organic/underhanded_c_luggage` is also ABI-neutral and has
  21 pointer-field rows around `RoutingDirective.next_directive`. Diagnostics
  show one candidate field with 10 uses, no shape demotion, blocked by
  `raw_binding_from_field` and `raw_pointee_field_move`. A targeted red-test
  attempt confirmed the hard part: the insertion routine copies
  `previous.next_directive` into a local, conditionally moves it into
  `new_directive.next_directive`, and otherwise recurses. A simple mutable alias
  promotion either borrows `previous.next_directive` too long or would need
  `take()` plus path-sensitive restoration on the recursive branch. Do not
  promote this shape until the transform can model take/restore semantics for
  linked-list field moves.
