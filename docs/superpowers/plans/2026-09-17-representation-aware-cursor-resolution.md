# Representation-Aware Cursor Resolution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Re-solve cursor demand after pointer representations stabilize so cursors blocked by finalized raw pointers demote to same-mutability slices without changing any other pointer decision.

**Architecture:** Preserve the current offset-sign answer by closing private legacy graphs, while retaining separate complete local, return, field, seed, and boundary constraints for a late solver. A read-only final-decision snapshot maps MIR nodes to emitted owners and representations; a pure directed worklist stops at raw barriers, carries demand through cursors and compiler temporaries, and emits an atomically validated cursor-to-slice delta. C-exposed inputs remain eligible because the existing Interface pass adapts both cursor and slice inputs back to the same raw exported ABI.

**Tech Stack:** Rust, rustc-private HIR/MIR APIs, `rustc_hash`, `rustc_index`, Crat Pointer and Interface passes, Cargo tests, and the pretranslated Crat test corpus.

**Spec:** `/home/ubuntu/crat/docs/superpowers/specs/2026-09-16-representation-aware-cursor-resolution-design.md`

## Global Constraints

- The only permitted representation changes are `SliceCursor(false) -> Slice(false)` and `SliceCursor(true) -> Slice(true)`.
- Do not rerun or change rawness, ownership, nullability, mutability, borrow promotion, or lifetime policy.
- Existing `access_signs` and `field_access_signs` must continue to come only from private legacy graphs with current source-order behavior.
- Retained `local_edges` must be the complete non-return graph; retained `return_edges` must contain only complete modeled direct-local return edges.
- Raw is the only absorbing representation. Cursors, including frozen cursors, propagate demand; proven compiler temporaries are transparent; reached unsupported boundaries poison their weak safety component.
- Struct fields, return owners, function-pointer groups, signature-locked functions, unmodeled calls, unresolved mappings, missing sign provenance, and `CursorFieldOffsetAlias` provenance remain protected.
- Exposure through `Config::c_exposed_fns` is not by itself a protection reason.
  Pointer and Interface must use the same item-name/`export_name` match, and a
  C-facing pipeline must run Interface so the exported raw-pointer ABI is unchanged.
- Resolve after the final `collect_diffs` and both normalization functions, before field lifetime injection and bridge collection. No `collect_diffs` may run after applying the delta.
- Validate the entire delta before the first mutation. A mismatch must leave both `SigDecisions` and `ptr_kinds` unchanged.
- Results, diagnostics, retention witnesses, and demotion order must be deterministic. Solving the post-delta state must yield an empty delta.
- Add no dependency and no permanent configuration or report-only flag.
- Do not run `scripts/translate.py` or `scripts/translate_all.py`.
- Do not read or modify `aws-translate` or any directory named `bundles`.
- Treat `/home/ubuntu/crat-workspace/transformed` as an immutable behavior baseline; candidate transformations go to a fresh directory.

---

## File and Responsibility Map

| File | Responsibility |
| --- | --- |
| `crates/pointer_replacer/src/analyses/offset_sign/sign.rs` | Preserve private legacy closure and expose complete retained cursor constraints |
| `crates/pointer_replacer/src/analyses/offset_sign/tests.rs` | Characterize legacy results, complete call coverage, direct seeds, and unmodeled boundaries |
| `crates/pointer_replacer/src/analyses/mir_variable_grouping.rs` | Expose source-owner representative/member queries |
| `crates/pointer_replacer/src/rewriter/mod.rs` | Retain `SourceVarGroups` in `Analysis` and register the resolver module |
| `crates/pointer_replacer/src/rewriter/collector.rs` | Return final pointer kinds together with cursor-field-alias provenance |
| `crates/pointer_replacer/src/rewriter/decision.rs` | Provide the narrow lifetime-preserving cursor-input demotion |
| `crates/pointer_replacer/src/rewriter/diagnostics.rs` | Name the late stage and its sole decision reason |
| `crates/pointer_replacer/src/rewriter/cursor_resolution.rs` | Own final-decision mapping, safety components, pure solving, outcomes, witnesses, and delta validation |
| `crates/pointer_replacer/src/rewriter/transform/mod.rs` | Take the final snapshot, invoke the resolver, atomically apply the delta, and record diagnostics |
| `crates/pointer_replacer/src/tests.rs` | Exercise complete Pointer rewriting for demotion, retention, and protected-boundary cases |
| `crates/passes/src/interface_fixer.rs` | Test that exposed slice and cursor inputs produce equivalent raw exported wrappers |

## Stable Interfaces Used Across Tasks

The implementation must converge on these crate-private interfaces. Private helpers may be added, but later tasks must use these names and meanings.

```rust
pub(crate) type CursorLocalNode = (LocalDefId, Local);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CursorFieldNode {
    Local(LocalDefId, Local),
    Field(StructFieldSlot),
}

#[derive(Debug, Default)]
pub(crate) struct CursorConstraints {
    pub(crate) local_seeds: FxHashSet<CursorLocalNode>,
    pub(crate) local_edges:
        FxHashMap<CursorLocalNode, FxHashSet<CursorLocalNode>>,
    pub(crate) return_edges:
        FxHashMap<CursorLocalNode, FxHashSet<CursorLocalNode>>,
    pub(crate) unmodeled_call_nodes: FxHashSet<CursorLocalNode>,
    pub(crate) field_seeds: FxHashSet<CursorFieldNode>,
    pub(crate) field_edges:
        FxHashMap<CursorFieldNode, FxHashSet<CursorFieldNode>>,
}

pub(crate) struct CollectedDiffs {
    pub(crate) ptr_kinds: FxHashMap<HirId, PtrKind>,
    pub(crate) cursor_field_offset_alias_bindings: FxHashSet<HirId>,
}

pub(crate) fn resolve_late_cursors(
    constraints: &CursorConstraints,
    view: &FinalCursorDecisionView,
) -> CursorResolution;

pub(crate) fn validate_cursor_demotions(
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    demotions: &[CursorDemotion],
) -> Result<(), CursorDemotionValidationError>;
```

---

### Task 1: Split Legacy Closure from Complete Retained Constraints

**Files:**
- Modify: `crates/pointer_replacer/src/analyses/offset_sign/sign.rs:29-34,1078-1491`
- Modify: `crates/pointer_replacer/src/analyses/offset_sign/tests.rs:1-100,1030-end`

**Interfaces:**
- Consumes: existing `StructFieldSlot`, `RustProgram`, MIR `Local`, and current legacy graph directions.
- Produces: `CursorLocalNode`, `CursorFieldNode`, `CursorConstraints`, and `OffsetSignResult::cursor_constraints`.
- Preserves: current `OffsetSignResult::access_signs` and `field_access_signs`, including `_0` omission and source-order sensitivity.

- [ ] **Step 1: Add a failing source-order characterization test**

Add a helper that runs `offset_sign_analysis` inside `run_compiler_on_str` and returns owned node labels `(function_name: String, local_index: usize)`, so no `TyCtxt`-bound value escapes the callback.

Add `complete_argument_edges_preserve_legacy_order_behavior` using both item orders:

```rust
pub unsafe fn caller(p: *const i32) {
    callee(p)
}
unsafe fn callee(p: *const i32) {
    let _ = *p.offset(-1);
}
```

```rust
unsafe fn callee(p: *const i32) {
    let _ = *p.offset(-1);
}
pub unsafe fn caller(p: *const i32) {
    callee(p)
}
```

Assert closed legacy behavior and retained coverage separately:

```rust
assert_eq!(needs_cursor(&caller_first.closed, "caller", "p"), None);
assert_eq!(
    needs_cursor(&callee_first.closed, "caller", "p"),
    Some(true)
);
assert!(caller_first.local_edges.contains(&(
    ("callee".into(), 1),
    ("caller".into(), 1),
)));
assert!(callee_first.local_edges.contains(&(
    ("callee".into(), 1),
    ("caller".into(), 1),
)));
```

- [ ] **Step 2: Run the test and confirm the red state**

Run:

```bash
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::complete_argument_edges_preserve_legacy_order_behavior \
  -- --exact --nocapture
```

Expected: compilation fails because `OffsetSignResult` has no `cursor_constraints`.

- [ ] **Step 3: Define retained constraint types**

At the analysis output boundary, replace private `Node` and `FieldNode` with the stable interfaces above and extend the result:

```rust
#[derive(Debug, Default)]
pub struct OffsetSignResult {
    pub access_signs: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    pub field_access_signs: FxHashSet<StructFieldSlot>,
    pub(crate) cursor_constraints: CursorConstraints,
}
```

Keep `SignGraph` and `FieldSignGraph` as private aliases.

- [ ] **Step 4: Give `Collector` separate legacy and complete sinks**

Replace its single graph pair with:

```rust
modeled_functions: &'a FxHashSet<LocalDefId>,
legacy_local_edges: &'a mut SignGraph,
complete_local_edges: &'a mut SignGraph,
return_edges: &'a mut SignGraph,
unmodeled_call_nodes: &'a mut FxHashSet<CursorLocalNode>,
legacy_field_edges: &'a mut FieldSignGraph,
complete_field_edges: &'a mut FieldSignGraph,
local_seeds: &'a mut FxHashSet<CursorLocalNode>,
field_seeds: &'a mut FxHashSet<CursorFieldNode>,
```

For assignment, cast, conservative dereference-store flow, and field relationships, write the same existing edge to both graph families. Preserve directions:

```text
assignment or cast: destination -> source
conservative memory flow: address-taken local -> stored source
field relationship: bidirectional safety relation
```

- [ ] **Step 5: Initialize and close graph families correctly**

In `offset_sign_analysis`:

```rust
let modeled_functions = rust_program.functions.iter().copied().collect();

let mut legacy_local_edges = SignGraph::default();
let mut legacy_field_edges = FieldSignGraph::default();

let mut local_edges = SignGraph::default();
let mut return_edges = SignGraph::default();
let mut field_edges = FieldSignGraph::default();

let mut local_seeds = FxHashSet::default();
let mut field_seeds = FxHashSet::default();
let mut unmodeled_call_nodes = FxHashSet::default();
```

Before visiting bodies, establish every `(did, local)` in complete `local_edges` and `field_edges`. Inside the existing per-function loop, keep destructive `insert` initialization only for `legacy_local_edges` and `legacy_field_edges`; this retains current overwrite behavior.

Run the existing SCC closures only on legacy graphs. Continue `.skip(1)` when building `access_signs`.

- [ ] **Step 6: Retain direct seeds without widening them**

For a supported pointer-offset primitive with a potentially negative offset, insert the receiver into the existing legacy taint set and `local_seeds`. Insert its local-or-field identity into the legacy field taint set and `field_seeds`.

Closure and `SourceVarGroups` postprocessing must not mutate retained seeds or edges.

- [ ] **Step 7: Record complete modeled direct-call edges**

For a constant `FnDef` whose local ID belongs to `modeled_functions`, record:

```text
callee parameter -> caller argument
caller destination -> callee::_0
```

Argument edges go in `complete_local_edges` regardless of source order. A pointer-return edge goes only in `return_edges`, never `complete_local_edges`, and the equivalent safety relationship goes in complete `field_edges`.

Keep the current conditional argument/return collection path against legacy graphs.

- [ ] **Step 8: Add coverage and parity tests**

Add:

```text
legacy_results_remain_characterized_with_retained_constraints
retained_constraints_cover_assignment_cast_recursion_and_fields
direct_seeds_remain_distinct_from_transitive_results
return_edges_are_complete_and_return_only_in_both_orders
```

The return test must assert:

```rust
assert!(return_edges[&caller_destination].contains(&callee_return));
assert!(
    return_edges
        .values()
        .flatten()
        .all(|(_, local)| *local == Local::from_usize(0))
);
```

Also assert that an integer-returning call adds no return edge and that assignments and arguments appear only in `local_edges`.

- [ ] **Step 9: Run focused and module tests**

```bash
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::complete_argument_edges_preserve_legacy_order_behavior \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::return_edges_are_complete_and_return_only_in_both_orders \
  -- --exact --nocapture
cargo test -p pointer_replacer analyses::offset_sign::tests -- --nocapture
```

Expected: all offset-sign tests pass; the pre-change baseline was 37 passing tests.

- [ ] **Step 10: Commit**

```bash
git add \
  crates/pointer_replacer/src/analyses/offset_sign/sign.rs \
  crates/pointer_replacer/src/analyses/offset_sign/tests.rs
git commit -m "feat(pointer): retain complete cursor constraints"
```

---

### Task 2: Protect Unmodeled Call Boundaries

**Files:**
- Modify: `crates/pointer_replacer/src/analyses/offset_sign/sign.rs:1219-1293`
- Modify: `crates/pointer_replacer/src/analyses/offset_sign/tests.rs`

**Interfaces:**
- Consumes: `Collector::modeled_functions`, `CursorConstraints::unmodeled_call_nodes`, and `is_pointer_offset_like_call`.
- Produces: conservative pointer-operand boundary nodes for indirect and foreign calls without invented flow.

- [ ] **Step 1: Add failing boundary tests**

Add:

```text
indirect_local_fn_pointer_call_is_unmodeled
indirect_field_fn_pointer_call_is_unmodeled
foreign_call_is_unmodeled
pointer_offset_call_is_seed_not_unmodeled
direct_local_call_is_modeled_not_unmodeled
```

For the first three, raw-pointer `Copy`/`Move` arguments and raw-pointer destinations must enter `unmodeled_call_nodes`; integer operands and function-pointer containers must not.

- [ ] **Step 2: Confirm the red state**

```bash
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::indirect_local_fn_pointer_call_is_unmodeled \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::foreign_call_is_unmodeled \
  -- --exact --nocapture
```

Expected: boundary assertions fail.

- [ ] **Step 3: Classify calls without `unreachable!()`**

Derive an optional constant `FnDef`; do not assume every constant callable operand has `TyKind::FnDef`.

Apply:

1. recognized pointer-offset primitive: execute the seed rule;
2. `FnDef` in `modeled_functions`: add complete argument/return constraints;
3. every other target: record an unmodeled boundary.

For private legacy graphs, preserve the existing constant-local-`FnDef` insertion behavior.

- [ ] **Step 4: Record only raw-pointer operands**

Use MIR types:

```rust
if arg.node.ty(self.body, self.tcx).is_raw_ptr()
    && let Operand::Copy(place) | Operand::Move(place) = arg.node
{
    self.unmodeled_call_nodes
        .insert((self.def_id, place.local));
}

if destination.ty(self.body, self.tcx).ty.is_raw_ptr()
    && !contains_deref(destination)
{
    self.unmodeled_call_nodes
        .insert((self.def_id, destination.local));
}
```

Add no directed parameter or return edge for an unmodeled call. Projected destinations rely on field safety relationships.

- [ ] **Step 5: Run the boundary suite**

```bash
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::indirect_local_fn_pointer_call_is_unmodeled \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::indirect_field_fn_pointer_call_is_unmodeled \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::foreign_call_is_unmodeled \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  analyses::offset_sign::tests::pointer_offset_call_is_seed_not_unmodeled \
  -- --exact --nocapture
cargo test -p pointer_replacer analyses::offset_sign::tests
```

- [ ] **Step 6: Commit**

```bash
git add \
  crates/pointer_replacer/src/analyses/offset_sign/sign.rs \
  crates/pointer_replacer/src/analyses/offset_sign/tests.rs
git commit -m "feat(pointer): retain unmodeled cursor boundaries"
```

---

### Task 3: Retain Source-Variable Ownership

**Files:**
- Modify: `crates/pointer_replacer/src/analyses/mir_variable_grouping.rs:24-125`
- Modify: `crates/pointer_replacer/src/rewriter/mod.rs:49-64,128-159`
- Modify: `crates/pointer_replacer/src/analyses/fn_ptr_groups.rs:211-247`
- Modify: `crates/pointer_replacer/src/analyses/fn_ptr_rewrite_decision.rs:367-403`
- Modify: `crates/pointer_replacer/src/rewriter/transform/mod.rs:16871-16934`

**Interfaces:**
- Produces:

```rust
pub fn representative(
    &self,
    did: LocalDefId,
    local: Local,
) -> Option<Local>;

pub fn members(
    &self,
    did: LocalDefId,
    representative: Local,
) -> &[Local];
```

- Produces: `Analysis::source_var_groups: SourceVarGroups`.

- [ ] **Step 1: Add reciprocal-query tests**

In a same-module test, construct a group with a representative and two members. Add:

```text
source_var_groups_expose_representative_and_members
seed_on_nonrepresentative_member_widens_to_owner
```

Assert:

```rust
assert_eq!(groups.representative(did, Local::from_usize(3)), Some(rep));
assert_eq!(
    groups.members(did, rep),
    &[rep, Local::from_usize(2), Local::from_usize(3)]
);
assert_eq!(groups.representative(did, Local::from_usize(9)), None);
assert!(groups.members(did, Local::from_usize(9)).is_empty());
```

Seed only the last member in a `DenseBitSet` and assert postprocessing widens to all members.

- [ ] **Step 2: Confirm missing methods**

```bash
cargo test -p pointer_replacer \
  analyses::mir_variable_grouping::tests::source_var_groups_expose_representative_and_members \
  -- --exact
```

Expected: compilation fails because the query methods do not exist.

- [ ] **Step 3: Add a reverse owner map and the two queries**

Extend storage:

```rust
pub struct SourceVarGroups {
    inner: FxHashMap<LocalDefId, FxHashMap<Local, Vec<Local>>>,
    representatives:
        FxHashMap<LocalDefId, FxHashMap<Local, Local>>,
}
```

Build `representatives` once from `inner` in `new`. Implement
`representative` with the reverse map, and implement `members` as:

```rust
self.inner
    .get(&did)
    .and_then(|groups| groups.get(&representative))
    .map(Vec::as_slice)
    .unwrap_or(&[])
```

Do not change existing widening behavior.

- [ ] **Step 4: Retain groups in `Analysis`**

Add:

```rust
source_var_groups: SourceVarGroups,
```

Move the already-built value into `Analysis` after existing postprocessing. Add the field to all three test-only `Analysis` literals listed above.

- [ ] **Step 5: Run tests**

```bash
cargo test -p pointer_replacer analyses::mir_variable_grouping::tests::
cargo test -p pointer_replacer
```

- [ ] **Step 6: Commit**

```bash
git add \
  crates/pointer_replacer/src/analyses/mir_variable_grouping.rs \
  crates/pointer_replacer/src/rewriter/mod.rs \
  crates/pointer_replacer/src/analyses/fn_ptr_groups.rs \
  crates/pointer_replacer/src/analyses/fn_ptr_rewrite_decision.rs \
  crates/pointer_replacer/src/rewriter/transform/mod.rs
git commit -m "feat(pointer): retain MIR source variable groups"
```

---

### Task 4: Retain Cursor-Field-Alias Provenance

**Files:**
- Modify: `crates/pointer_replacer/src/rewriter/collector.rs:22-237,394-468`
- Modify: `crates/pointer_replacer/src/rewriter/transform/mod.rs:1526,1851,1915,17842,18013`

**Interfaces:**
- Produces `CollectedDiffs` from both collection entry points.

- [ ] **Step 1: Add provenance tests**

Add:

```text
collect_diffs_tracks_cursor_field_offset_alias_without_local_sign
ordinary_sign_cursor_has_no_cursor_field_alias_provenance
```

For the alias case:

```rust
assert_eq!(
    collected.ptr_kinds.get(&binding),
    Some(&PtrKind::SliceCursor(false))
);
assert!(
    collected
        .cursor_field_offset_alias_bindings
        .contains(&binding)
);
assert!(!analysis.offset_sign_result.access_signs[&did].contains(local));
```

The ordinary negative-offset cursor must leave the provenance set empty.

- [ ] **Step 2: Confirm the red state**

```bash
cargo test -p pointer_replacer \
  rewriter::transform::tests::collect_diffs_tracks_cursor_field_offset_alias_without_local_sign \
  -- --exact --nocapture
```

Expected: collection does not expose provenance.

- [ ] **Step 3: Return `CollectedDiffs`**

Initialize the map and set. When `cursor_field_offset_alias_kind` returns:

```rust
if alias_kind != ptr_kind {
    cursor_field_offset_alias_bindings.insert(*hir_id);
}
ptr_kind = alias_kind;
```

Return both fields. Do not reconstruct provenance from diagnostics.

- [ ] **Step 4: Update callers without changing final timing**

At initial collection, destructure only `ptr_kinds`. At compatibility recollections and test helpers, use `.ptr_kinds`. Keep the existing conditional final recollection until Task 8 makes it unconditional.

- [ ] **Step 5: Run tests**

```bash
cargo test -p pointer_replacer \
  rewriter::transform::tests::collect_diffs_tracks_cursor_field_offset_alias_without_local_sign \
  -- --exact --nocapture
cargo test -p pointer_replacer cursor_field
cargo test -p pointer_replacer
```

- [ ] **Step 6: Commit**

```bash
git add \
  crates/pointer_replacer/src/rewriter/collector.rs \
  crates/pointer_replacer/src/rewriter/transform/mod.rs
git commit -m "feat(pointer): retain cursor alias provenance"
```

---

### Task 5: Add Narrow Signature Mutation and Diagnostic Vocabulary

**Files:**
- Modify: `crates/pointer_replacer/src/rewriter/decision.rs:373-417`
- Modify: `crates/pointer_replacer/src/rewriter/diagnostics.rs:71-301,600-end`

**Interfaces:**
- Produces `SigDecision::demote_cursor_input`.
- Produces `DecisionStage::LateCursorResolution`.
- Produces `DecisionReason::NoReachableCursorDemandAfterNormalization`.

- [ ] **Step 1: Add signature mutation tests**

Add:

```text
demote_cursor_input_preserves_shared_cursor_lifetime
demote_cursor_input_preserves_mutable_cursor_lifetime
demote_cursor_input_rejects_non_cursor
```

Assert exact transition and unchanged lifetime:

```rust
assert!(sig.demote_cursor_input(0));
assert_eq!(sig.input_decs[0], Some(PtrKind::Slice(false)));
assert_eq!(sig.input_lifetimes[0], before_lifetime);
```

Raw, reference, slice, box, and `None` inputs must return `false` and leave the decision equal to its clone.

- [ ] **Step 2: Confirm the red state**

```bash
cargo test -p pointer_replacer \
  rewriter::decision::tests::demote_cursor_input \
  -- --nocapture
```

Expected: method missing.

- [ ] **Step 3: Implement only the narrow mutation**

```rust
pub(crate) fn demote_cursor_input(&mut self, index: usize) -> bool {
    let Some(PtrKind::SliceCursor(mutability)) =
        self.input_decs.get(index).copied().flatten()
    else {
        return false;
    };
    self.input_decs[index] = Some(PtrKind::Slice(mutability));
    true
}
```

Do not call `set_input_dec`.

- [ ] **Step 4: Add diagnostic variants and tests**

Insert `LateCursorResolution` immediately before `AstRewriteFallback`:

```rust
Self::LateCursorResolution => "late_cursor_resolution",
```

Add:

```rust
Self::NoReachableCursorDemandAfterNormalization => {
    "no_reachable_cursor_demand_after_normalization"
}
```

Add:

```text
late_cursor_resolution_names_are_stable
ast_rewrite_fallback_supersedes_late_cursor_resolution_summary
```

The second records a late event followed by an AST fallback event for one subject and asserts `summaries()` selects the fallback.

- [ ] **Step 5: Run and commit**

```bash
cargo test -p pointer_replacer rewriter::decision::tests::demote_cursor_input
cargo test -p pointer_replacer rewriter::diagnostics::tests::
```

```bash
git add \
  crates/pointer_replacer/src/rewriter/decision.rs \
  crates/pointer_replacer/src/rewriter/diagnostics.rs
git commit -m "feat(pointer): add late cursor demotion vocabulary"
```

---

### Task 6: Implement the Pure Cursor-Demand Solver

**Files:**
- Create: `crates/pointer_replacer/src/rewriter/cursor_resolution.rs`
- Modify: `crates/pointer_replacer/src/rewriter/mod.rs:36-45`

**Interfaces:**
- Consumes `CursorConstraints` and a precomputed owned view.
- Produces:

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CursorOwner {
    Param {
        did: LocalDefId,
        index: usize,
        binding: HirId,
    },
    Binding {
        did: LocalDefId,
        hir_id: HirId,
    },
    Return(LocalDefId),
    Field(StructFieldSlot),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CursorFlow {
    Transparent,
    Cursor(CursorOwner),
    RawBarrier,
    UnsupportedBoundary,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FreezeReason {
    FieldConnected,
    FunctionPointerGroup,
    SignatureLocked,
    CursorReturn,
    UnmodeledCall,
    CursorFieldOffsetAlias,
    NotSignDerived,
    MissingMirMembers,
    UnresolvedMapping,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ProtectionSite {
    Node(CursorLocalNode),
    Owner(CursorOwner),
    Function(LocalDefId),
}

pub(crate) struct FinalCursorDecisionView {
    flows: FxHashMap<CursorLocalNode, CursorFlow>,
    owner_members: FxHashMap<CursorOwner, Vec<CursorLocalNode>>,
    cursor_kinds: FxHashMap<CursorOwner, PtrKind>,
    protections: Vec<(ProtectionSite, FreezeReason)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorDemotion {
    pub(crate) owner: CursorOwner,
    pub(crate) expected_old_kind: PtrKind,
    pub(crate) replacement_kind: PtrKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CursorRetention {
    Required { witness: Vec<CursorLocalNode> },
    Protected { reasons: Vec<FreezeReason> },
    Poisoned { boundary: CursorLocalNode },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorResolutionStats {
    pub(crate) candidates: usize,
    pub(crate) required: usize,
    pub(crate) protected: usize,
    pub(crate) poisoned: usize,
    pub(crate) demoted: usize,
    pub(crate) reached_raw_barriers: usize,
    pub(crate) protected_by_reason: Vec<(FreezeReason, usize)>,
}


pub(crate) struct CursorResolution {
    demotions: Vec<CursorDemotion>,
    retained: FxHashMap<CursorOwner, CursorRetention>,
    reached_raw_barriers: FxHashSet<CursorLocalNode>,
}

impl CursorResolution {
    pub(crate) fn demotions(&self) -> &[CursorDemotion];
    pub(crate) fn retention(&self, owner: CursorOwner) -> Option<&CursorRetention>;
    pub(crate) fn stats(&self) -> CursorResolutionStats;
}
```

`FreezeReason` has no C-exposure variant.

- [ ] **Step 1: Add basic synthetic solver tests**

Register `mod cursor_resolution;`. Add:

```text
raw_seed_stops_and_demotes_unreached_cursor
cursor_seed_retains_cursor_suppliers
cursor_then_raw_stops_after_required_cursor
transparent_temporary_forwards_demand
shared_and_mutable_demotions_preserve_mutability
```

Build constraints and view manually inside a small `run_compiler_on_str` callback used only to obtain real identifiers. The solver accepts no `TyCtxt`.

Assert:

```rust
assert_eq!(
    resolution.demotions(),
    &[CursorDemotion {
        owner,
        expected_old_kind: PtrKind::SliceCursor(true),
        replacement_kind: PtrKind::Slice(true),
    }]
);
```

- [ ] **Step 2: Confirm the red state**

```bash
cargo test -p pointer_replacer \
  rewriter::cursor_resolution::tests::raw_seed_stops_and_demotes_unreached_cursor \
  -- --exact --nocapture
```

Expected: resolver missing.

- [ ] **Step 3: Build one undirected safety graph**

Use:

```rust
enum SafetyVertex {
    Local(CursorLocalNode),
    Owner(CursorOwner),
    Field(StructFieldSlot),
}
```

Add both directions for:

- every `local_edges` edge;
- every `return_edges` edge;
- every `field_edges` edge after mapping `CursorFieldNode`;
- every `Local(member) <-> Owner(owner)` membership.

Insert vertices independently of edge presence for every adjacency-map key and
value, every `local_seeds`, `field_seeds`, and `unmodeled_call_nodes` entry,
and every cursor owner. This gives an isolated seed or boundary a component and
keeps an orphan owner as a singleton.

Components containing `Field` receive `FieldConnected`.
`unmodeled_call_nodes` receive `UnmodeledCall`. Expand view protections by
node, owner, or all vertices belonging to a function.

Compute components with a queue and stable vertex ordering.

- [ ] **Step 4: Implement directed demand**

Seed only `local_seeds`, sorted by `(did.local_def_index.as_u32(), local.as_usize())`.

```rust
match view
    .flows
    .get(&node)
    .copied()
    .unwrap_or(CursorFlow::UnsupportedBoundary)
{
    CursorFlow::Transparent => enqueue_successors(node),
    CursorFlow::Cursor(owner) => {
        required.insert(owner);
        record_first_predecessor(owner, node);
        enqueue_successors_of_all_owner_members(owner);
    }
    CursorFlow::RawBarrier => {
        reached_raw_barriers.insert(node);
    }
    CursorFlow::UnsupportedBoundary => {
        poisoned_components.insert(component_of(node));
    }
}
```

Frozen cursors still take the cursor arm. Do not SCC-compress directed flow.

- [ ] **Step 5: Assign one outcome per candidate**

In deterministic owner order:

1. required with a predecessor witness;
2. protected with sorted reasons;
3. poisoned at the first stable unsupported boundary;
4. otherwise exact `SliceCursor(m) -> Slice(m)` demotion.

Define an explicit owner sort key from variant, definition index, parameter/field index, and HIR local ID. Never rely on hash iteration.

`CursorResolution::stats()` derives its totals only from `demotions`,
`retained`, and `reached_raw_barriers`. Count every protected reason even when
one owner has several, and return `protected_by_reason` in the explicit
`FreezeReason` declaration order rather than hash order.

- [ ] **Step 6: Add fan-out, cycle, and protection tests**

Add:

```text
owner_fanout_enqueues_every_member_successor
grouped_temporary_seed_stops_at_raw_parameter
mixed_raw_cursor_cycle_does_not_cross_raw_barrier
active_sibling_branch_retains_cursor_after_raw_branch_stops
field_protected_component_freezes_grouped_owner
frozen_cursor_still_propagates
protected_component_reasons_freeze_entire_component
unsupported_boundary_poisons_component
unresolved_boundary_poisons_component
```

Table-drive all freeze reasons listed above. There must be no C-exposure case.

- [ ] **Step 7: Add accounting and determinism tests**

Add:

```text
resolver_accounts_for_every_cursor_owner
resolution_stats_count_every_outcome_by_reason
results_and_witnesses_ignore_hash_insertion_order
resolver_is_idempotent_after_delta
```

For idempotence, create a second synthetic view without demoted cursor candidates and assert the second delta is empty.

- [ ] **Step 8: Run and commit**

```bash
cargo test -p pointer_replacer rewriter::cursor_resolution::tests:: -- --nocapture
```

```bash
git add \
  crates/pointer_replacer/src/rewriter/cursor_resolution.rs \
  crates/pointer_replacer/src/rewriter/mod.rs
git commit -m "feat(pointer): solve late cursor demand"
```

---

### Task 7: Build the Final-Representation View

**Files:**
- Modify: `crates/pointer_replacer/src/rewriter/cursor_resolution.rs`

**Interfaces:**
- Produces:

```rust
impl FinalCursorDecisionView {
    pub(crate) fn new<'tcx>(
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
        sig_decs: &SigDecisions,
        ptr_kinds: &FxHashMap<HirId, PtrKind>,
        forced_raw_bindings: &FxHashSet<HirId>,
        cursor_field_offset_alias_bindings: &FxHashSet<HirId>,
        fn_ptr_groups: &FnPtrGroups,
    ) -> Self;
}
```

There is no C-exposure input.

- [ ] **Step 1: Add mapping-precedence tests**

Add:

```text
final_view_maps_parameter_before_binding
final_view_maps_return_and_freezes_it
final_view_maps_source_group_to_one_binding_owner
final_view_distinguishes_transparent_and_source_visible_unmapped_locals
```

Inputs and their group members map to one `Param`; their HIR bindings never become separate `Binding` candidates. `_0` maps to `Return`.

- [ ] **Step 2: Confirm the red state**

```bash
cargo test -p pointer_replacer \
  rewriter::cursor_resolution::tests::final_view_maps_parameter_before_binding \
  -- --exact --nocapture
```

Expected: constructor missing.

- [ ] **Step 3: Build unambiguous ownership maps**

For each function:

- build `Local -> Vec<HirId>` from `binding_to_local`;
- collect debug-visible root locals from every `VarDebugInfoContents::Place(place)`, including projected places through `place.local`;
- map in order: parameter, `_0`, source-group representative, unique direct binding, transparent compiler temporary, unresolved source-visible local.

Missing or multiple source-owner mappings produce `UnsupportedBoundary` and `UnresolvedMapping`, never `Transparent`.

- [ ] **Step 4: Classify final representations**

```text
SliceCursor(m) -> Cursor(owner)
Raw(m) -> RawBarrier
unchanged original raw with no explicit decision -> RawBarrier
Slice/Ref/OptRef/Box/OptBox/OptBoxedSlice -> UnsupportedBoundary
representation-less compiler temporary -> Transparent
```

For a parameter, compare signature input with effective binding kind. Consult `forced_raw_bindings` even if `ptr_kinds` lacks an entry. Any disagreement protects the owner.

- [ ] **Step 5: Enumerate candidates and protections**

Candidates come from cursor signature inputs, cursor local bindings, cursor returns, and orphan cursor bindings. Parameter identity suppresses duplicate binding candidates.

Add protections:

- return cursor: `CursorReturn`;
- no postprocessed sign member: `NotSignDerived`;
- no mapped member: `MissingMirMembers`;
- alias provenance: `CursorFieldOffsetAlias`;
- function-pointer membership: `FunctionPointerGroup`;
- `signature_locked`: `SignatureLocked`;
- ambiguous or inconsistent mapping: `UnresolvedMapping`.

Do not inspect `c_exposed_fns`, `extern "C"`, `no_mangle`, or `export_name`.

- [ ] **Step 6: Add fail-closed and non-freeze tests**

Add:

```text
final_view_freezes_signature_binding_disagreement
final_view_freezes_forced_raw_disagreement
final_view_freezes_missing_or_ambiguous_parameter_binding
final_view_accounts_for_orphan_cursor
final_view_protects_function_pointer_and_signature_lock
final_view_protects_cursor_field_alias
final_view_does_not_model_c_exposure_as_a_freeze_reason
```

- [ ] **Step 7: Run and commit**

```bash
cargo test -p pointer_replacer rewriter::cursor_resolution::tests:: -- --nocapture
cargo test -p pointer_replacer
```

```bash
git add crates/pointer_replacer/src/rewriter/cursor_resolution.rs
git commit -m "feat(pointer): model final cursor representations"
```

---

### Task 8: Validate and Atomically Apply the Delta

**Files:**
- Modify: `crates/pointer_replacer/src/rewriter/cursor_resolution.rs`
- Modify: `crates/pointer_replacer/src/rewriter/transform/mod.rs:1506-1940,10072-10172`

**Interfaces:**
- Produces:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CursorDemotionValidationError {
    InvalidTransition(CursorOwner, PtrKind, PtrKind),
    DuplicateOwner(CursorOwner),
    MissingSignature(LocalDefId),
    SignatureMismatch(CursorOwner, Option<PtrKind>),
    BindingMismatch(CursorOwner, Option<PtrKind>),
    UnsupportedOwner(CursorOwner),
}

pub(crate) fn apply_cursor_demotions(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &mut FxHashMap<HirId, PtrKind>,
    demotions: &[CursorDemotion],
    diagnostics: &mut DecisionDiagnostics,
) -> Result<(), CursorDemotionValidationError>;
```

- [ ] **Step 1: Add validation and atomicity tests**

Add:

```text
validate_demotions_accepts_exact_binding_and_parameter_snapshots
validate_demotions_rejects_wrong_mutability
validate_demotions_rejects_duplicate_owner
validate_demotions_rejects_return_and_field
apply_demotions_validates_full_delta_before_writing
```

For atomicity, make the first entry valid and the second mismatched. Assert `Err`, then exact equality with cloned `sig_decs` and `ptr_kinds`.

- [ ] **Step 2: Confirm the red state**

```bash
cargo test -p pointer_replacer \
  rewriter::transform::tests::apply_demotions_validates_full_delta_before_writing \
  -- --exact --nocapture
```

Expected: functions missing.

- [ ] **Step 3: Validate the whole delta first**

Validate unique owners, exact same-mutability transitions, exact binding snapshots, exact parameter signature and binding snapshots, valid indexes, and no return/field owner.

Do not insert missing map entries or normalize disagreement.

- [ ] **Step 4: Commit writes, then diagnostics**

After successful validation:

- binding: update only `ptr_kinds`;
- parameter: call `demote_cursor_input` and update its HIR binding;
- record one event per owner after writes.

```rust
diagnostics.record(
    subject,
    DecisionStage::LateCursorResolution,
    Some(demotion.expected_old_kind),
    Some(demotion.replacement_kind),
    DecisionReason::NoReachableCursorDemandAfterNormalization,
    None,
);
```

Retained outcomes produce no event.

- [ ] **Step 5: Take one unconditional final snapshot**

After field-source signature changes:

```rust
let final_diffs =
    collect_diffs(rust_program, analysis, &sig_decs, &fn_ptr_groups);
let mut ptr_kinds = final_diffs.ptr_kinds;
let cursor_field_offset_alias_bindings =
    final_diffs.cursor_field_offset_alias_bindings;

normalize_forced_raw_bindings(
    rust_program.tcx,
    &mut ptr_kinds,
    &forced_raw_bindings,
);
normalize_owning_call_result_bindings(
    rust_program.tcx,
    &sig_decs,
    &mut ptr_kinds,
    &forced_raw_bindings,
);
```

Remove the now-unneeded `sig_changed` collection guard.

- [ ] **Step 6: Wire the resolver before lifetime injection**

```rust
let resolution = {
    let view = FinalCursorDecisionView::new(
        rust_program,
        analysis,
        &sig_decs,
        &ptr_kinds,
        &forced_raw_bindings,
        &cursor_field_offset_alias_bindings,
        &fn_ptr_groups,
    );
    resolve_late_cursors(
        &analysis.offset_sign_result.cursor_constraints,
        &view,
    )
};

apply_cursor_demotions(
    rust_program.tcx,
    &mut sig_decs,
    &mut ptr_kinds,
    resolution.demotions(),
    &mut diagnostics,
)
.expect("late cursor resolution snapshot must remain valid");
```

Place it before `apply_field_storage_input_lifetimes`. Search to prove no `collect_diffs` follows.

For rustc-backed report tests, add a test-only visitor field:

```rust
#[cfg(test)]
cursor_resolution: CursorResolution,
```

The application borrows `resolution.demotions()`, then test builds move the
unchanged pre-application resolution into this field during visitor construction.
Production builds gain neither state nor a report-only flag.


- [ ] **Step 7: Add application and event tests**

Add:

```text
apply_demotions_updates_parameter_and_binding_together
apply_demotions_updates_local_only
apply_demotions_preserves_lifetime_mutability_and_non_cursor_decisions
late_cursor_demotion_records_one_change_event
retained_cursor_records_no_change_event
```

Snapshot raw owners and all unaffected kinds before and after.

- [ ] **Step 8: Run and commit**

```bash
cargo test -p pointer_replacer \
  rewriter::transform::tests::apply_demotions \
  -- --nocapture
cargo test -p pointer_replacer \
  rewriter::transform::tests::late_cursor \
  -- --nocapture
cargo test -p pointer_replacer rewriter::diagnostics::tests::
cargo test -p pointer_replacer
```

```bash
git add \
  crates/pointer_replacer/src/rewriter/cursor_resolution.rs \
  crates/pointer_replacer/src/rewriter/transform/mod.rs
git commit -m "feat(pointer): apply late cursor demotions atomically"
```

---

### Task 9: Add Full-Rewrite and Interface Regressions

**Files:**
- Modify: `crates/pointer_replacer/src/tests.rs`
- Modify: `crates/pointer_replacer/src/rewriter/transform/mod.rs`
- Modify: `crates/passes/src/interface_fixer.rs`

**Interfaces:**
- Consumes complete Pointer rewrite and existing Interface shape recognition.
- Produces source-level regressions for demotion, retention, protection, and raw exports.

- [ ] **Step 1: Add the exposed merge-sort demotion regression**

Add `test_late_cursor_resolution_demotes_merge_sort_wrappers_at_raw_barrier` using this reduced shape:

```rust
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Sprite {
    pub key: i32,
}

unsafe extern "C" fn iteration(
    a: *const Sprite,
    lo: i32,
    split: i32,
    hi: i32,
    b: *mut Sprite,
) {
    let mut i = lo;
    let mut j = split;
    let mut k = lo;
    while k < hi {
        if i < split
            && (j >= hi
                || (*a.offset(i as isize)).key
                    <= (*a.offset(j as isize)).key)
        {
            *b.offset(k as isize) = *a.offset(i as isize);
            i += 1;
        } else {
            *b.offset(k as isize) = *a.offset(j as isize);
            j += 1;
        }
        k += 1;
    }
}

unsafe extern "C" fn recurse(
    b: *mut Sprite,
    lo: i32,
    hi: i32,
    a: *mut Sprite,
) {
    if hi - lo <= 1 {
        return;
    }
    let split = (lo + hi) / 2;
    recurse(a, lo, split, b);
    recurse(a, split, hi, b);
    iteration(b, lo, split, hi, a);
}

#[no_mangle]
pub unsafe extern "C" fn merge_sort(
    a: *mut Sprite,
    b: *mut Sprite,
    size: i32,
) {
    recurse(b, 0, size, a);
}
```

Set `config.c_exposed_fns.insert("merge_sort".to_string())`.

Assert helpers stay raw, `merge_sort` inputs become `&mut [Sprite]`, no cursor remains in its signature, and helper calls use `.as_mut_ptr()`.

Also add
`rewriter::transform::tests::merge_sort_final_view_report_demotes_exposed_inputs`.
Parameterize the existing test-only `build_analysis` helper with `&Config` so
its Andersen configuration matches production, construct `TransformVisitor`
with `c_exposed_fns = {"merge_sort"}`, and inspect its captured
pre-application `CursorResolution`.

Map owners to owned `(tcx.def_path_str(did), parameter_index)` labels inside
the compiler callback. Assert that both pointer inputs of `merge_sort` are
demotions and have no retained outcome. Assert:

```rust
let resolution = &visitor.cursor_resolution;
let stats = resolution.stats();
assert_eq!(stats.demoted, resolution.demotions().len());
assert_eq!(
    stats.candidates,
    stats.required + stats.protected + stats.poisoned + stats.demoted,
);
assert!(stats.reached_raw_barriers > 0);
```

Include `stats` and `protected_by_reason` in assertion failures. This is the
actual final-view report-only check proving configured C exposure did not
silently swallow the intended candidates.

- [ ] **Step 2: Add retention and boundary regressions**

Add `test_late_cursor_resolution_retains_fallcalc_reverse_chain` and assert both the reverse callee and its end-pointer local remain cursors.

Retain and run:

```text
test_interproc_negative_offset_propagation
test_raw_local_caller_keeps_negative_cursor_input_raw
test_array_pointer_caller_keeps_negative_cursor_input_cursor
all cursor-field-offset-alias tests
```

Add:

```text
test_late_cursor_resolution_preserves_cursor_field_offset_alias
test_late_cursor_resolution_freezes_function_pointer_signature
test_late_cursor_resolution_freezes_signature_locked_input
```

Do not add a C-exposure freeze test.

- [ ] **Step 3: Test equivalent Interface adapters**

Add `wraps_exposed_slice_and_cursor_inputs_with_same_raw_abi` in `interface_fixer.rs`. Provide minimal local `SliceCursor` and `SliceCursorMut` definitions with `empty` and `new`, and four exposed functions taking shared slice, mutable slice, shared cursor, and mutable cursor.

Run `fix_interfaces`, type-check output, and assert:

```text
all exported parameters are *const/*mut element pointers
all Rust bodies are renamed to *_internal
slice wrappers call from_raw_parts/from_raw_parts_mut
cursor wrappers call SliceCursor::new/SliceCursorMut::new
export attributes remain only on raw wrappers
```

- [ ] **Step 4: Run focused regressions**

```bash
cargo test -p pointer_replacer \
  tests::test_late_cursor_resolution_demotes_merge_sort_wrappers_at_raw_barrier \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  rewriter::transform::tests::merge_sort_final_view_report_demotes_exposed_inputs \
  -- --exact --nocapture
cargo test -p pointer_replacer \
  tests::test_late_cursor_resolution_retains_fallcalc_reverse_chain \
  -- --exact --nocapture
cargo test -p passes \
  interface_fixer::tests::wraps_exposed_slice_and_cursor_inputs_with_same_raw_abi \
  -- --exact --nocapture
```

- [ ] **Step 5: Run package suites**

```bash
cargo test -p pointer_replacer tests::test_late_cursor_resolution_
cargo test -p pointer_replacer
cargo test -p passes interface_fixer::tests::
```

- [ ] **Step 6: Commit**

```bash
git add \
  crates/pointer_replacer/src/rewriter/transform/mod.rs \
  crates/pointer_replacer/src/tests.rs \
  crates/passes/src/interface_fixer.rs
git commit -m "test(pointer): cover late cursor resolution end to end"
```

---

### Task 10: Repository and Corpus Validation

**Files:**
- Verify: all files changed in Tasks 1–9.
- Generate: a fresh `/home/ubuntu/crat-workspace/transformed-cursor-resolution.*`.
- Do not modify: `/home/ubuntu/crat-workspace/transformed`.

**Interfaces:**
- Produces formatter, linter, workspace-test, targeted-diff, vector, unsafe-count, cursor-count, ABI, and determinism evidence.

- [ ] **Step 1: Run repository checks**

```bash
cargo fmt
cargo clippy --workspace --all-targets
git diff --check
cargo test --workspace
```

Expected: all commands exit zero.

- [ ] **Step 2: Create a harness that targets this checkout**

Run from the implementation checkout:

```bash
CURSOR_HARNESS="$(mktemp -d /tmp/crat-cursor-harness.XXXXXX)"
CURSOR_OUT="$(mktemp -d \
  /home/ubuntu/crat-workspace/transformed-cursor-resolution.XXXXXX)"

cp -a /home/ubuntu/crat-workspace/scripts "$CURSOR_HARNESS/scripts"
ln -s "$(pwd -P)" "$CURSOR_HARNESS/crat"
ln -s /home/ubuntu/crat-workspace/c2rust-translated \
  "$CURSOR_HARNESS/c2rust-translated"
ln -s /home/ubuntu/crat-workspace/Test-Corpus \
  "$CURSOR_HARNESS/Test-Corpus"
ln -s /home/ubuntu/crat-workspace/PUBLIC-Test-Corpus \
  "$CURSOR_HARNESS/PUBLIC-Test-Corpus"

ln -sfn "$CURSOR_HARNESS" /tmp/crat-cursor-harness-current
ln -sfn "$CURSOR_OUT" /tmp/crat-cursor-output-current

test "$(readlink -f "$CURSOR_HARNESS/crat")" = "$(pwd -P)"
cd "$CURSOR_HARNESS"
PYTHONPATH=scripts python3 -c \
  'import transform; print(transform._crat_dir().resolve())'
```

Expected: the final command prints the implementation checkout, not `/home/ubuntu/crat-workspace/crat`.

All corpus-script tool calls must use `sandbox_permissions=require_escalated`.

- [ ] **Step 3: Record targeted baseline vector status**

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

python3 scripts/test.py \
  /home/ubuntu/crat-workspace/transformed \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B01_organic/merge_sort_lib \
  --verbose
python3 scripts/test.py \
  /home/ubuntu/crat-workspace/transformed \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/fallcalc_lib \
  --verbose
python3 scripts/test.py \
  /home/ubuntu/crat-workspace/transformed \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_organic/pinflate_lib \
  --verbose
python3 scripts/test.py \
  /home/ubuntu/crat-workspace/transformed \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/gotomach_lib \
  --verbose
```

Record pre-existing failures.

- [ ] **Step 4: Transform targeted cases through Pointer**

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT="$(readlink -f /tmp/crat-cursor-output-current)"
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B01_organic/merge_sort_lib \
  pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/fallcalc_lib \
  pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_organic/pinflate_lib \
  pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/gotomach_lib \
  pointer --run-dependencies
```

Expected: all four succeed.

- [ ] **Step 5: Inspect Pointer diffs**

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT="$(readlink -f /tmp/crat-cursor-output-current)"
diff -ru \
  /home/ubuntu/crat-workspace/transformed/pointer/Public-Tests/B01_organic/merge_sort_lib \
  "$CURSOR_OUT/pointer/Public-Tests/B01_organic/merge_sort_lib"
diff -ru \
  /home/ubuntu/crat-workspace/transformed/pointer/Public-Tests/B02_synthetic/fallcalc_lib \
  "$CURSOR_OUT/pointer/Public-Tests/B02_synthetic/fallcalc_lib"
diff -ru \
  /home/ubuntu/crat-workspace/transformed/pointer/Public-Tests/B02_organic/pinflate_lib \
  "$CURSOR_OUT/pointer/Public-Tests/B02_organic/pinflate_lib"
diff -ru \
  /home/ubuntu/crat-workspace/transformed/pointer/Public-Tests/B02_synthetic/gotomach_lib \
  "$CURSOR_OUT/pointer/Public-Tests/B02_synthetic/gotomach_lib"
```

`diff` exit 1 is expected for intentional changes. Verify:

- `merge_sort`: helpers raw; exposed inputs `&mut [spritebatch_sprite_t]`.
- `fallcalc`: reverse-walk parameter and `last_element` remain cursors.
- `pinflate`: cursor field remains protected.
- `gotomach`: function-pointer signature is unchanged.

- [ ] **Step 6: Transform through Bin and run targeted vectors**

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT="$(readlink -f /tmp/crat-cursor-output-current)"
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B01_organic/merge_sort_lib \
  bin --run-dependencies
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/fallcalc_lib \
  bin --run-dependencies
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_organic/pinflate_lib \
  bin --run-dependencies
python3 scripts/transform.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/gotomach_lib \
  bin --run-dependencies

python3 scripts/test.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B01_organic/merge_sort_lib \
  --verbose
python3 scripts/test.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/fallcalc_lib \
  --verbose
python3 scripts/test.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_organic/pinflate_lib \
  --verbose
python3 scripts/test.py "$CURSOR_OUT" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/gotomach_lib \
  --verbose
```

Expected: no new vector failures.

Inspect candidate Interface output for:

```text
merge_sort_internal with &mut [spritebatch_sprite_t] inputs
exported merge_sort with *mut spritebatch_sprite_t inputs
from_raw_parts_mut in both wrapper adaptations
```

- [ ] **Step 7: Run full public and hidden transformations**

Only after targeted cases pass:

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT="$(readlink -f /tmp/crat-cursor-output-current)"
CRAT_POINTER_DECISION_DIAGNOSTICS=summary \
python3 scripts/transform_all.py "$CURSOR_OUT" pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=summary \
python3 scripts/transform_all.py "$CURSOR_OUT" bin --run-dependencies
```

Expected: zero transformation failures. Both public and hidden corpora are included.

- [ ] **Step 8: Record baseline and candidate vector/unsafe summaries**

Baseline first:

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

python3 scripts/test_all.py /home/ubuntu/crat-workspace/transformed
python3 scripts/find_unsafe.py
python3 scripts/summarize_unsafe.py
```

Candidate second:

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT="$(readlink -f /tmp/crat-cursor-output-current)"
python3 scripts/test_all.py "$CURSOR_OUT"
python3 scripts/find_unsafe.py
python3 scripts/summarize_unsafe.py
```

Run unsafe scripts immediately after each `test_all.py`. Candidate failures must not exceed baseline failures; unsafe counts must not increase without an intended, documented cause.

- [ ] **Step 9: Compare global cursor counts**

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT="$(readlink -f /tmp/crat-cursor-output-current)"
rg -o --glob lib.rs \
  'crate::slice_cursor::SliceCursor(Mut)?' \
  /home/ubuntu/crat-workspace/transformed/pointer | wc -l
rg -o --glob lib.rs \
  'crate::slice_cursor::SliceCursor(Mut)?' \
  "$CURSOR_OUT/pointer" | wc -l
```

Expected: candidate count does not increase.

- [ ] **Step 10: Check targeted determinism**

```bash
CURSOR_HARNESS="$(readlink -f /tmp/crat-cursor-harness-current)"
cd "$CURSOR_HARNESS"

CURSOR_OUT_1="$(mktemp -d \
  /home/ubuntu/crat-workspace/transformed-cursor-resolution-determinism-a.XXXXXX)"
CURSOR_OUT_2="$(mktemp -d \
  /home/ubuntu/crat-workspace/transformed-cursor-resolution-determinism-b.XXXXXX)"
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT_1" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B01_organic/merge_sort_lib \
  pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT_1" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/fallcalc_lib \
  pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT_2" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B01_organic/merge_sort_lib \
  pointer --run-dependencies
CRAT_POINTER_DECISION_DIAGNOSTICS=full \
python3 scripts/transform.py "$CURSOR_OUT_2" \
  /home/ubuntu/crat-workspace/Test-Corpus/Public-Tests/B02_synthetic/fallcalc_lib \
  pointer --run-dependencies

diff -ru \
  "$CURSOR_OUT_1/pointer/Public-Tests/B01_organic/merge_sort_lib" \
  "$CURSOR_OUT_2/pointer/Public-Tests/B01_organic/merge_sort_lib"
diff -ru \
  "$CURSOR_OUT_1/pointer/Public-Tests/B02_synthetic/fallcalc_lib" \
  "$CURSOR_OUT_2/pointer/Public-Tests/B02_synthetic/fallcalc_lib"
```

Expected: both diffs exit zero, including their full-diagnostic `stderr.log` files.

- [ ] **Step 11: Inspect and commit task-owned final adjustments**

```bash
cd "$(readlink -f /tmp/crat-cursor-harness-current/crat)"

git status --short
git diff --check
```

Stage only task files:

```bash
cd "$(readlink -f /tmp/crat-cursor-harness-current/crat)"

git add \
  crates/pointer_replacer/src/analyses/offset_sign/sign.rs \
  crates/pointer_replacer/src/analyses/offset_sign/tests.rs \
  crates/pointer_replacer/src/analyses/mir_variable_grouping.rs \
  crates/pointer_replacer/src/rewriter/mod.rs \
  crates/pointer_replacer/src/rewriter/collector.rs \
  crates/pointer_replacer/src/rewriter/decision.rs \
  crates/pointer_replacer/src/rewriter/diagnostics.rs \
  crates/pointer_replacer/src/rewriter/cursor_resolution.rs \
  crates/pointer_replacer/src/rewriter/transform/mod.rs \
  crates/pointer_replacer/src/tests.rs \
  crates/passes/src/interface_fixer.rs
git commit -m "test(pointer): validate representation-aware cursor resolution"
```

Do not stage unrelated changes or generated corpus output.

---

## Final Review Checklist

- [ ] Every final cursor owner has one outcome: demoted, required with a seed witness, protected with reasons, or poisoned at a reached unsupported boundary.
- [ ] `local_edges` is complete and excludes returns; `return_edges` is return-only.
- [ ] Private legacy graphs alone determine `access_signs` and `field_access_signs`.
- [ ] Raw stops only its directed branch; frozen cursors propagate.
- [ ] C exposure is absent from `FreezeReason`, `FinalCursorDecisionView::new`, and protected-component construction.
- [ ] Interface restores raw parameters for every demoted exposed input.
- [ ] Validation completes before mutation and an error leaves the snapshot unchanged.
- [ ] No `collect_diffs` occurs after late application.
- [ ] Raw owners, ownership, nullability, mutability, and lifetimes are unchanged.
- [ ] A post-delta solve is empty and repeated runs produce identical witnesses and source.
- [ ] Targeted and full corpus results are compared against the immutable baseline.
