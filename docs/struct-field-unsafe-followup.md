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
field-base cleanup already committed.

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

## Still Open

- The broad pointer-field-specific `raw_pointer_struct_field_deref` bucket is
  still the main opportunity: the merged evidence shows 1073 pointer-field rows
  across 24 cases. Prior work only covers direct safe roots and a narrow shared
  local-alias shape.
- Dynamic pointer fields with offset, sentinel `from_raw_parts`, allocation/free
  ownership, unsafe call-boundary adapters, function-pointer fields, mutable
  statics, and broad mutable local aliases remain out of scope until a targeted
  pattern is selected from the merged span evidence.
