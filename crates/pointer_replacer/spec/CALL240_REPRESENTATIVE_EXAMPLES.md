# CALL-240 Representative Examples (Fully Self-Contained)

## Goal
Provide a standalone evidence packet for spec discussion about why only part of `malloc/calloc` sites are promoted to box-form in the current B02 rewrite sweep.

No external files are required to understand this document.

## Snapshot totals
The following numbers are the full run snapshot used for this report:

- Cases: `86` (all passed compile check)
- Allocator-unsafe calls before rewrite: `172`
- Allocator-unsafe calls after rewrite: `154`
- Allocator-unsafe removed: `18`
- `call240_applied`: `18`
- `call250_non_move_required`: `78`
- `call240_compile_risk_default_missing`: `16`
- By allocator:
- `malloc`: `call240_applied=13`, `call250_non_move_required=70`, `call240_compile_risk_default_missing=11`
- `calloc`: `call240_applied=5`, `call250_non_move_required=8`, `call240_compile_risk_default_missing=5`

Interpretation used in this report:

- `call240_applied`: allocator-origin site was rewritten to a `Box::new` path.
- `call250_non_move_required`: allocator-origin site was found, but destination requirement was not `Move`, so CALL-240 was not selected.
- `call240_compile_risk_default_missing`: diagnostic risk marker for `<T as Default>::default()` usage.

## Example 1: CALL-240 applied (rewritten)
Case: `arity_lib`  
Function: `compare_allocations`  
Allocator: `malloc`

Before:

```rust
let ptr1: *mut core::ffi::c_int =
    malloc(::core::mem::size_of::<core::ffi::c_int>() as size_t)
        as *mut core::ffi::c_int;
let ptr2: *mut core::ffi::c_int =
    malloc(::core::mem::size_of::<core::ffi::c_int>() as size_t)
        as *mut core::ffi::c_int;
if ptr1.is_null() || ptr2.is_null() {
    free(ptr1 as *mut core::ffi::c_void);
    free(ptr2 as *mut core::ffi::c_void);
    return -(1 as core::ffi::c_int);
}
*ptr1 = val1;
*ptr2 = val2;
```

After:

```rust
let mut ptr1: Option<Box<i32>> =
    Some(Box::new(<i32 as Default>::default()));
let mut ptr2: Option<Box<i32>> =
    Some(Box::new(<i32 as Default>::default()));
if ptr1.is_none() || ptr2.is_none() {
    drop(ptr1);
    drop(ptr2);
    return -(1 as core::ffi::c_int);
}
*((ptr1).as_deref_mut().map_or(std::ptr::null_mut::<i32>(), |_x| _x)).as_mut().unwrap() = val1;
*((ptr2).as_deref_mut().map_or(std::ptr::null_mut::<i32>(), |_x| _x)).as_mut().unwrap() = val2;
```

Raw interop adaptation in same function:

```rust
(ptr1).take().map(|_x| Box::into_raw(_x)).unwrap_or(std::ptr::null_mut())
```

Why this is representative:

- It shows the intended CALL-240 path: allocator call disappears and object initialization becomes `Box::new(<T as Default>::default())`.

## Example 2: Mixed outcome in one case (applied and not applied together)
Case: `generic_foreach`

Applied site (`list_double_append`):

Before:

```rust
let node: *mut list_node_double_t =
    malloc(::core::mem::size_of::<list_node_double_t>() as size_t)
        as *mut list_node_double_t;
if node.is_null() { return -(1 as core::ffi::c_int); }
(*node).data = value;
```

After:

```rust
let mut node: Option<Box<crate::src::inventory::list_node_double>> =
    Some(Box::new(<crate::src::inventory::list_node_double as Default>::default()));
if node.is_none() { return -(1 as core::ffi::c_int); }
(*((node).as_deref_mut().map_or(std::ptr::null_mut::<crate::src::inventory::list_node_double>(),
                                |_x| _x)).as_mut().unwrap()).data = value;
```

Not-applied site in the same case (`list_double_create`):

Before:

```rust
let list: *mut list_double_t =
    malloc(::core::mem::size_of::<list_double_t>() as size_t)
        as *mut list_double_t;
if list.is_null() {
    return std::ptr::null_mut::<list_double_t>();
}
```

After:

```rust
let list: *mut list_double_t =
    malloc(::core::mem::size_of::<list_double_t>() as size_t)
        as *mut list_double_t;
if list.is_null() {
    return std::ptr::null_mut::<list_double_t>();
}
```

Why this is representative:

- Same benchmark file, same allocator family, different destination context.
- One site takes CALL-240 (`Move`-required), the other remains raw (`non-Move`, counted as CALL-250).

## Example 3: Preserved raw allocator site (non-Move side)
Case: `betagamma_lib`  
Function: `allocate_block`  
Allocator: `malloc`

Before:

```rust
let mb: *mut MemoryBlock =
    malloc(::core::mem::size_of::<MemoryBlock>() as size_t) as *mut MemoryBlock;
if mb.is_null() { return std::ptr::null_mut::<MemoryBlock>(); }
(*mb).data =
    calloc(count, ::core::mem::size_of::<core::ffi::c_int>() as size_t)
        as *mut core::ffi::c_int;
```

After:

```rust
let mb: *mut MemoryBlock =
    malloc(::core::mem::size_of::<MemoryBlock>() as size_t) as *mut MemoryBlock;
if mb.is_null() { return std::ptr::null_mut::<MemoryBlock>(); }
(*mb).data =
    calloc(count, ::core::mem::size_of::<core::ffi::c_int>() as size_t)
        as *mut core::ffi::c_int;
```

Why this is representative:

- It is a clean preserved example: allocator-origin call remains unchanged through rewrite.

## Bottom line
- Current reduction (`18`) corresponds to CALL-240-applied sites.
- The larger remainder is dominated by `call250_non_move_required` (`78`), i.e. allocator-origin sites where required destination context is not `Move`.
- This is why allocator removal does not approach total `malloc/calloc` count under the current rule selection.
