# Representation-Aware Cursor Re-solving and Late Demotion

Date: 2026-09-16

Status: approved in-chat design; implementation not started

Scope: the pointer replacer's offset-sign constraints, final pointer decisions, and
ordinary local/direct-call cursor representations

## Summary

The pointer replacer currently decides whether a raw C pointer needs
`SliceCursor` by propagating negative-offset requirements before pointer
representations are finalized. Later compatibility processing may force an
intermediate function parameter or local back to a raw pointer, but the already
closed sign result continues to make upstream pointers cursors. This leaves
unnecessary cursors and cursor/raw conversions in the emitted Rust.

This design retains the offset analysis's direct negative-offset seeds and
requirement edges, then solves those constraints a second time after the existing
forced-raw/signature compatibility processing has stabilized. The late solver is
representation-aware:

- a finalized cursor carries demand to the pointer that supplies it;
- a finalized raw pointer absorbs demand because it can perform negative pointer
  arithmetic directly;
- a representation-less MIR temporary transparently carries demand;
- an unsupported or unresolved boundary makes its connected component
  ineligible for demotion.

The late stage may make exactly two changes:

```text
SliceCursor(false) -> Slice(false)
SliceCursor(true)  -> Slice(true)
```

It does not rerun general pointer decision-making and cannot change rawness,
ownership, nullability, mutability, borrow promotion, or lifetime policy.

## Motivation

### Redundant cursors after raw normalization

In the translated `merge_sort` case, recursive helper parameters remain raw and
perform the negative-offset operations. Wrapper parameters are nevertheless
emitted as `SliceCursorMut` and immediately converted back to raw pointers for
the helper calls. The original sign closure has propagated the helper's demand
to the wrappers without knowing that the helper's final raw representation is
an adequate endpoint for that demand.

The late solution should behave as follows:

```text
negative-offset seed on recursive helper parameter
    -> helper parameter is finally Raw
    -> demand stops at the raw barrier
    -> wrapper parameters have no active cursor demand
    -> wrapper parameters demote to mutable slices
```

### Necessary cursor propagation

In the translated `fallcalc` case, reverse traversal is performed through a
parameter that remains a cursor. Its callers must preserve the original base and
current position. The late solution therefore continues through that parameter
and retains the cursor-providing callers:

```text
negative-offset seed on reverse-traversal parameter
    -> parameter is finally Cursor
    -> demand continues to caller arguments
    -> the cursor chain is retained
```

The distinction is final representation, not merely the syntactic presence of
a negative offset.

## Goals

- Remove cursors justified only by paths that now terminate at raw pointers.
- Reduce redundant cursor-to-raw and raw-to-cursor adaptation.
- Preserve cursors that still carry active negative-offset demand.
- Keep the existing initial offset-sign result and decision pipeline unchanged.
- Make the late solver independently testable and deterministic.
- Fail closed when final ownership or representation cannot be mapped reliably.
- Apply all demotions atomically after the last decision recollection.
- Let C-exposed inputs participate in late demotion; the existing interface pass
  restores their raw-pointer C ABI from either a final slice or cursor.

## Non-goals

- Improving the precision of the sign abstract domain itself.
- Promoting a slice, reference, box, or raw pointer to a cursor.
- Converting any cursor or slice to raw.
- Re-solving ownership, nullability, mutability, borrow promotion, or lifetimes.
- Changing struct field representations.
- Changing return representations.
- Changing the externally visible C ABI.
- Changing signature-locked functions.
- Changing functions that participate in function-pointer groups.
- Proving which non-raw representations can serve as cursor anchors.
- Using the pointer-flow graph or offset-annotated provenance as a prerequisite.
- Removing every cursor/raw adapter in the first stage.

Fields, returns, function-pointer groups, and richer anchor classification are
possible later stages with separate validation.

## Current pipeline and failure mode

The relevant pipeline is currently:

```text
offset-sign analysis
    -> direct negative seeds and requirement graph
    -> transitive closure into access_signs / field_access_signs
    -> source-variable group widening
    -> initial SigDecisions and ptr_kinds
    -> forced-raw/signature compatibility fixpoint
    -> field-source raw downgrades
    -> final collect_diffs and raw/owning normalization
    -> field lifetime injection and bridge collection
    -> AST rewrite
```

`OffsetSignResult` retains only the closed `access_signs` and
`field_access_signs`. Once a requirement has propagated through a node, the
rewriter cannot distinguish a direct negative-offset seed from an inherited
requirement. It therefore cannot remove demand when that node later becomes raw.

The existing `downgrade_cursor_inputs_from_unanchored_raw_callers` remains in
the compatibility fixpoint. It solves a different problem: a cursor signature
that cannot be constructed from a particular raw caller. The new late solver
removes cursor requirements that became stale after all such raw decisions were
made.

## Architecture

The change has three deliberately narrow parts:

1. The offset-sign analysis builds a complete retained constraint graph for
   late resolution while continuing to compute the legacy closed results from
   separate private graphs with exactly the current collection behavior. The
   retained graph completes source-order-sensitive direct-call argument and
   return coverage without feeding either completion into the legacy closure.
2. A rewriter-side `FinalCursorDecisionView` maps MIR graph nodes to their
   emitted owners and finalized representations.
3. A cursor-only resolver computes a validated demotion delta, which the
   transform constructor applies once.

The resolver belongs under `rewriter`, not `analyses`, because it consumes
`PtrKind` and `SigDecisions`. The offset-sign constraint representation remains
under `analyses::offset_sign` and has no dependency on rewriting policy.

Proposed file ownership:

| Location | Responsibility |
| --- | --- |
| `analyses/offset_sign/sign.rs` | Preserve private legacy closure graphs and retain complete late constraints and boundaries |
| `analyses/mir_variable_grouping.rs` | Expose source-group representatives and members |
| `rewriter/collector.rs` | Retain bindings whose cursor kind came from `CursorFieldOffsetAlias` |
| `rewriter/cursor_resolution.rs` | Final decision view, component policy, solver, and result validation |
| `rewriter/decision.rs` | Narrow cursor-input-to-slice mutation |
| `rewriter/transform/mod.rs` | Invoke the solver and atomically apply its delta |
| `rewriter/diagnostics.rs` | Record late-demotion events |

## Retained cursor constraints

The offset analysis should expose direct seeds and a complete pre-closure graph
for late solving:

```rust
pub(crate) type CursorLocalNode = (LocalDefId, Local);

pub(crate) enum CursorFieldNode {
    Local(LocalDefId, Local),
    Field(StructFieldSlot),
}

pub(crate) struct CursorConstraints {
    local_seeds: FxHashSet<CursorLocalNode>,
    local_edges: FxHashMap<CursorLocalNode, FxHashSet<CursorLocalNode>>,
    return_edges: FxHashMap<CursorLocalNode, FxHashSet<CursorLocalNode>>,
    unmodeled_call_nodes: FxHashSet<CursorLocalNode>,
    field_seeds: FxHashSet<CursorFieldNode>,
    field_edges: FxHashMap<CursorFieldNode, FxHashSet<CursorFieldNode>>,
}
```

`OffsetSignResult` gains a `cursor_constraints` field. Its existing fields remain
and are still produced by the existing SCC-based closure over separate,
ephemeral `legacy_local_edges` and `legacy_field_edges`. Those private graphs
preserve the current sequential initialization and collection behavior exactly.
Initial pointer decisions continue to consume only the existing closed fields,
so retaining complete constraints cannot alter output.

`local_edges` is the complete non-return local constraint graph. It includes
assignment, cast, conservative memory, and every modeled direct-local-call
argument edge independent of source order. `return_edges` remains narrowly the
complete direct-local-call return graph. The late directed graph is the union of
`local_edges` and `return_edges`; neither complete graph participates in the
initial SCC closure.

This split closes two known order-sensitive coverage gaps without changing the
legacy answer. All function/local nodes are established in the complete graphs
before bodies are visited. Every modeled direct local call records its existing
`callee_parameter -> caller_argument` constraints in `local_edges`, and a call
with a pointer-valued return records
`caller_destination -> callee::_0` in `return_edges`, regardless of whether the
caller or callee is visited first. Collection into the ephemeral legacy graphs
keeps the current visitation and insertion behavior for result parity.

Call-boundary classification first excludes `is_pointer_offset_like_call` and
any future primitive handled by a dedicated constraint rule. Among the remaining
calls, every pointer-valued argument or destination of a call that is not a
modeled direct local `FnDef` is recorded in `unmodeled_call_nodes`, except a
recognized buffer argument of a resolved direct foreign call whose existing HIR
adapter policy treats that argument as borrow-only and non-escaping. The shared
name/argument-position policy covers the buffer arguments of `memcpy`, `memmove`,
`memchr`, `memset`, and `strncpy`. Pointer-valued destinations, unknown foreign
calls, and indirect calls remain unmodeled boundaries.

The existing edge direction is preserved. An edge `A -> B` means:

> If `A` requires cursor semantics, `B` must preserve the information needed to
> provide them.

Examples are assignment destination to source, callee parameter to caller
argument, and caller destination to callee return. Edge-kind and MIR-location
metadata may be retained for diagnostics, but stage-one solving must not assign
different semantics to different edge kinds.

The retained local and field graphs remain separate. Complete `field_edges` are
used by the late stage only to identify protected components; only the private
legacy field graph feeds `field_access_signs`.

Stage one does not infer argument constraints for indirect or foreign calls.
Instead, every recorded `unmodeled_call_nodes` entry protects its undirected
safety component. Freezing only the possible callees is insufficient because no
directed edge connects those callees to the caller-side arguments.

## Source-variable ownership

`SourceVarGroups` is currently used to widen closed results and then discarded.
It should instead be retained in the rewriter's `Analysis` value and expose
read-only queries:

```rust
fn representative(&self, did: LocalDefId, local: Local) -> Option<Local>;
fn members(&self, did: LocalDefId, representative: Local) -> &[Local];
```

All MIR locals for one emitted source binding map to one cursor owner. Reaching
one member activates the outgoing constraints of all members. A demotion is
therefore made once per owner and applied to the entire source representation,
never to individual MIR temporaries.

Parameter identity takes precedence over general binding identity. If a group
representative is an input local, every group member maps to the same `Param`;
the parameter HIR binding must never appear as an independent `Binding`
candidate. Eligibility requires exactly one reverse HIR mapping for that input.
Missing or ambiguous mappings are frozen.

## Final representation view

The final view is a read-only adapter over `SigDecisions`, `ptr_kinds`,
`forced_raw_bindings`, source groups, HIR/MIR mappings, function-pointer groups,
collector cursor provenance, and constraint boundary facts. It does not run an
analysis or rewrite decisions.

```rust
enum CursorOwner {
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

enum CursorFlow {
    Transparent,
    Cursor(CursorOwner),
    RawBarrier,
    UnsupportedBoundary,
}

enum DemotionEligibility {
    Eligible,
    Frozen(FreezeReason),
}
```

Representation and eligibility are intentionally independent. A frozen cursor
still propagates demand; freezing only prevents changing its representation.

### Node-to-owner mapping

Mapping is performed in this order:

1. MIR input locals map to `Param`; their final class comes from the matching
   signature input decision.
2. MIR `_0` maps to `Return` and is frozen in stage one.
3. A local in a non-parameter `SourceVarGroups` group maps through its
   representative to one HIR `Binding` owner.
4. A directly mapped HIR local maps to `Binding` even if it has no larger group.
5. A non-input local with neither debug ownership nor an HIR binding is a proven
   compiler temporary and is `Transparent`.
6. A debug-visible or otherwise source-visible local that cannot be mapped is
   `UnsupportedBoundary`, not `Transparent`.

For an emitted pointer owner, `SliceCursor(m)` is `Cursor`, explicit `Raw(m)` or
an unchanged original raw-pointer decision is `RawBarrier`, and every other
final `PtrKind` is `UnsupportedBoundary`. Stage one does not claim that slices,
references, or boxes preserve the base/position relationship required by a
downstream cursor.

For parameters, the view compares the emitted signature kind with the effective
binding kind after `forced_raw_bindings` normalization. A missing signature
decision means the original raw-pointer type is retained. Stage-one eligibility
requires one concrete HIR binding and exact agreement between the two kinds. A
forced-raw/body decision that disagrees with a cursor signature, a missing
binding, or an ambiguous reverse mapping is unresolved and freezes the component
rather than selecting one side silently.

### Candidate provenance

A final cursor is eligible only if its cursor representation is backed by the
offset-sign analysis. At least one canonical MIR member must occur in the legacy
postprocessed `access_signs`; this check happens after `SourceVarGroups`
widening.

The final `collect_diffs` invocation must also retain the HIR bindings whose
cursor kind was introduced by `CursorFieldOffsetAlias`. Those bindings are
protected in stage one because their field-origin dependency is HIR-only and is
not represented completely by the local demand graph.

A final cursor without sign provenance, with only collector-specific cursor
provenance, or without a complete MIR-member mapping is retained with an
explicit freeze reason. It must never enter the eligible set merely because no
directed seed reaches it.

### C-exposed inputs and the final interface adapter

Here, “C-exposed” means a function selected by `Config::c_exposed_fns`, using
the existing item-name or `export_name` match shared by Pointer and Interface.
This guarantee does not extend to an arbitrary `extern "C"` or `no_mangle`
function omitted from that configuration.

C exposure alone is not a protection reason. Pointer already permits a selected
raw-pointer input to become either a slice or a cursor. Later in the standard
pipeline, Interface recognizes `&[T]`, `&mut [T]`, `SliceCursor<T>`, and
`SliceCursorMut<T>`, renames the Rust implementation, and emits the original
exported symbol with its raw-pointer parameter.

A late cursor-to-slice demotion only changes which of those two supported
adapters the interface pass emits. It does not change the final exported symbol
or raw-pointer C signature. This exception is input-only: returns remain frozen,
struct fields remain governed by the existing field/ABI protections, and a
C-exposed function that is also signature-locked or in a function-pointer group
is still protected for those independent reasons. Output immediately after the
pointer pass is an intermediate representation; a C-facing pipeline must still
run the interface pass.

### Protected components

The resolver builds two graph views. The directed demand graph is the union of
`local_edges` and `return_edges`; source-owner fan-out activates all member
successors without erasing edge direction or representation barriers.

The separate undirected safety graph contains every constraint endpoint and
every final cursor candidate. It treats local demand edges as undirected,
incorporates all field-graph edges through their shared local nodes, and adds
equality edges between every source-group member. Thus a candidate with no flow
edge has a singleton component, and different MIR temporaries for one binding
can never receive different protection policy.

The resolver computes weakly connected components of the safety graph. A
component is ineligible for demotion if it touches:

- a struct field through the field constraint graph;
- a function in a function-pointer group;
- a signature-locked function;
- a cursor-valued return owner;
- a pointer argument or destination in `unmodeled_call_nodes`;
- a binding introduced as a cursor by `CursorFieldOffsetAlias`;
- an unresolved source-level owner;
- a final cursor with no legacy sign provenance or complete MIR membership.

For field protection, first find weak field-graph components containing a
`Field` node. Every local node in such a field component protects its component
in the undirected safety graph.

The whole component is frozen rather than only the protected owner. This first
stage avoids introducing new adapters or compatibility assumptions at
unadapted exact-signature and storage boundaries.

## Late cursor solver

The worklist starts from direct negative-offset seeds. Final cursor decisions
are never seeds. Only sign-derived cursors in eligible safety components are
demotion candidates; seeding from current cursors would make demotion
impossible.

Conceptually:

```rust
queue = direct_negative_seeds

while let Some(node) = queue.pop() {
    if !visited.insert(node) {
        continue;
    }

    match view.classify(node) {
        Transparent => enqueue_successors(node),

        Cursor(owner) => {
            required_owners.insert(owner);
            enqueue_all_owner_members_and_their_successors(owner);
        }

        RawBarrier => {
            raw_barriers.insert(node);
            // This branch is satisfied and stops here.
        }

        UnsupportedBoundary => {
            poisoned_components.insert(weak_component(node));
            // Nothing in this component may be demoted.
        }
    }
}
```

A cursor owner propagates regardless of whether it is eligible for demotion. A
raw owner is the only representation that absorbs an active requirement.
Encountering an unsupported representation or unresolved mapping fails closed
by poisoning the component.

After traversal:

```text
demotions = eligible sign-derived cursor owners
          - required cursor owners
          - owners in components poisoned during demand traversal
```

The solver also records one deterministic predecessor chain for every required
owner. Stable seed and successor ordering makes witnesses reproducible, while
the required/demoted sets themselves remain order-independent.

Every final cursor owner is accounted for exactly once: either it appears in the
delta or it has a retained reason such as `Required(witness)`, `Protected`,
`Poisoned`, `NotSignDerived`, or `UnresolvedMapping`. Every eligible owner not
reached by demand must appear in the delta. A final cursor with no mapped MIR
member freezes individually instead of disappearing from candidate accounting.

The graph is finite and every node and owner fan-out is processed once. Demand
must be solved node by node and must not be compressed into legacy SCCs. A raw
node inside a directed cycle still stops the branch; SCC-wide propagation would
incorrectly cross that barrier. SCC or union-find machinery may be used only to
construct the undirected safety components.

## Important flow cases

### Seed on a finalized raw parameter

```text
seed -> Raw
```

The raw parameter absorbs demand. Cursor candidates beyond it are not reached
and may demote. This is the `merge_sort` case.

### Seed on a finalized cursor parameter

```text
seed -> Cursor A -> Cursor B
```

Both owners are required and retained. This is the `fallcalc` case.

### Cursor followed by raw

```text
seed -> Cursor A -> Raw B
```

`A` remains required; demand stops at `B`. Stage one does not attempt to replace
`A` with raw or remove the existing bridge.

### Frozen cursor

```text
seed -> Frozen Cursor A -> Cursor B
```

`A` cannot demote, but demand continues and retains `B`. Frozen is never an
absorbing representation.

### Unsupported or unresolved boundary

```text
seed -> Unsupported
```

The boundary's weak component is excluded from demotion. This sacrifices some
opportunities rather than assuming an unproved adapter preserves position.

## Integration point

The resolver runs in `TransformVisitor::new` after the last
`collect_diffs`, `normalize_forced_raw_bindings`, and
`normalize_owning_call_result_bindings`, and before
`apply_field_storage_input_lifetimes` and bridge collection:

```rust
normalize_forced_raw_bindings(...);
normalize_owning_call_result_bindings(...);

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
    &resolution,
    &mut diagnostics,
);

apply_field_storage_input_lifetimes(...);
```

There must be no `collect_diffs` call after application. `collect_diffs` consults
the original closed sign result for ordinary locals and would recreate their
cursor decisions.

The view borrows decisions immutably and is dropped before application. The
resolution therefore describes one stable snapshot.

## Atomic application

Application first validates every planned write against the snapshot, then
commits all writes. A validation mismatch is an internal invariant failure and
must occur before any mutation.

Each `CursorDemotion` stores its owner, expected old kind, and replacement kind.
Validation checks every signature target, every binding target, their mutual
agreement for parameters, and the expected old kinds for the entire delta before
the first write.

- A `Binding` demotion updates its `ptr_kinds` entry.
- A `Param` demotion updates its `SigDecision` input and its required concrete
  HIR binding entry in `ptr_kinds`.
- Returns and fields can never appear in a stage-one demotion.

The signature update uses a narrow operation rather than the general
`SigDecision::set_input_dec`:

```rust
fn demote_cursor_input(&mut self, index: usize) -> bool {
    let replacement = match self.input_decs[index] {
        Some(PtrKind::SliceCursor(m)) => Some(PtrKind::Slice(m)),
        _ => return false,
    };
    self.input_decs[index] = replacement;
    true
}
```

This operation deliberately leaves input lifetime metadata untouched. It also
preserves mutability by construction.

A further compatibility iteration is unnecessary. Cursor-to-slice is a
one-directional weakening, and exact-signature consumers are frozen. Existing
unanchored raw callers have already been handled by the compatibility fixpoint.

## Diagnostics

Add a decision stage ordered before `AstRewriteFallback`:

```rust
DecisionStage::LateCursorResolution
```

An actual demotion records one reason:

```rust
DecisionReason::NoReachableCursorDemandAfterNormalization
```

Normal diagnostics should record changes, not non-events. The resolution object
may retain freeze reasons, reached raw barriers, and predecessor witnesses for
tests and verbose debugging. Development report-only runs must report candidate,
required, frozen, poisoned, demoted, and reached-raw counts by reason.

AST visitation can still force a local raw when an expression-level rewrite
fallback is discovered. The late event therefore describes the validated
constructor snapshot, not necessarily the final emitted representation. A later
`AstRewriteFallback` event must supersede it in the existing final diagnostic
summary.

## Invariants and failure policy

The implementation must enforce these invariants:

- Every delta is `SliceCursor(m) -> Slice(m)` with the same `m`.
- No protected or poisoned component changes.
- All MIR members of one source owner observe one representation decision.
- Every required cursor has a witness path from a direct seed.
- Every retained final cursor has either a demand witness or an explicit
  protected, poisoned, provenance, or mapping reason.
- Every eligible, unrequired cursor in an unpoisoned component is in the delta.
- Existing raw, ownership, nullability, mutability, and lifetime decisions are
  unchanged by the late delta.
- The resolver is idempotent: solving the post-delta state yields no new delta.
- The initial legacy `access_signs` and `field_access_signs` are unchanged by
  the separate complete retained graphs.
- Results and witnesses are deterministic.

Mapping uncertainty is handled locally by freezing its component. Snapshot
validation failures during application are programming errors; validation must
finish before any write so the result cannot be partially applied.

## Testing

### Constraint extraction

- Pin the legacy closed local and field results with characterization fixtures
  and ensure closure consumes only the private legacy graphs. In particular,
  prove that complete retained call-argument edges coexist with the current
  source-order-sensitive legacy results and that `_0` remains omitted from
  `access_signs`.
- Distinguish direct seeds from transitively reached nodes.
- Exercise assignment, cast, call-argument, return, recursion, and field edges.
- Exercise source-variable groups whose temporary, rather than representative,
  receives the seed.
- Build identical retained call-argument and return edges with
  caller-before-callee and callee-before-caller function order while preserving
  the characterized legacy outputs.
- Mark caller arguments and destinations protected for indirect calls through
  local and struct-field function pointers, and for unknown foreign calls.
- Exclude only the recognized borrow-only buffer arguments of resolved direct
  foreign calls from unmodeled protection; keep pointer-valued destinations
  protected and prove the corresponding HIR raw-pointer adapters still compile.
- Assert that a negative pointer-offset operation creates a direct seed without
  marking its receiver or safety component as unmodeled.

### Pure resolver

Use small synthetic graphs for:

- a seed directly on raw, allowing an upstream cursor candidate to demote;
- a seed on cursor, retaining its cursor suppliers;
- a cursor followed by raw, retaining only the cursor already encountered;
- transparent temporaries;
- owner/group fan-out;
- directed cycles and deterministic witnesses;
- a seed on a temporary grouped with a finalized raw parameter, stopping at that
  parameter;
- a mixed raw/cursor directed cycle without SCC-wide propagation;
- one branch stopped by raw while a second active branch reaches and retains the
  same cursor;
- source-group equality crossing into a field-protected safety component;
- frozen cursor propagation;
- protected components;
- unsupported and unresolved boundaries poisoning a component;
- shared and mutable cursor demotions;
- idempotence.

### Rewriter integration

- A signature parameter and its HIR binding update together.
- Parameter signature/binding disagreement, forced-raw disagreement, and a
  missing or ambiguous parameter binding all freeze without a partial write.
- An orphan final cursor with no complete MIR mapping is retained explicitly.
- A `CursorFieldOffsetAlias` cursor not backed by local `access_signs` remains
  protected.
- A local binding changes only in `ptr_kinds`.
- Lifetime metadata is unchanged by signature demotion.
- Rawness, ownership, nullability, and mutability are unchanged.
- No later collection step restores a demoted local.
- Fields, returns, function-pointer groups, and locked signatures remain
  unchanged.
- C exposure alone does not freeze an input; after a demotion, the interface
  pass still emits the original raw-pointer wrapper around the internal slice.
- Every retained cursor has a witness or explicit retention reason.
- A later AST rewrite fallback records `AstRewriteFallback` and supersedes the
  earlier late-demotion event in the final summary.

### Repository and corpus validation

From the `crat` repository, run:

```text
cargo fmt
cargo clippy --workspace --all-targets
cargo test --workspace
```

Use the already translated corpus and write transformed candidates to a new
output directory. Do not run `translate.py` or `translate_all.py`.

Targeted corpus checks:

- `merge_sort`: recursive helpers remain raw; wrapper parameters become slices;
  redundant cursor/raw conversions disappear.
- `fallcalc`: reverse-traversal cursors and their propagation remain intact.
- representative field and function-pointer cases: protected decisions do not
  change;
- a C-exposed demoted input: the interface pass preserves the exported raw
  pointer signature and adapts it to the internal slice.

After targeted cases compile and pass their vectors, transform and test the full
public corpus and compare it with the current transformed baseline.

## Acceptance criteria

- All unit, workspace, targeted corpus, and full public-corpus tests pass.
- The late pass produces only cursor-to-same-mutability-slice changes.
- Immediately before and after applying the late delta, exact raw-owner sets and
  mutability agree in both `SigDecisions` and `ptr_kinds`; later adapter syntax
  or AST fallbacks are compared separately.
- Protected components have no representation changes.
- After the interface pass, every affected C-exposed function retains its
  original exported raw-pointer signature, while Rust callers target the
  internal slice-taking function.
- The report-only run counts freezes by reason and confirms that the intended
  `merge_sort` wrapper candidates are not swallowed by component protection.
- Global cursor count does not increase.
- `merge_sort` exhibits the intended cursor and conversion reduction.
- `fallcalc` retains its required cursors.
- A second solve produces an empty delta.
- Repeated runs emit identical code and diagnostic witnesses.

## Delivery order

1. Split private legacy closure graphs from complete retained constraints and
   prove legacy-result parity and source-order-independent late coverage.
2. Retain `SourceVarGroups` and add its read-only owner queries.
3. Implement the final decision view and pure resolver with synthetic tests.
4. Run the resolver report-only during development and inspect targeted deltas;
   do not add a permanent public configuration flag.
5. Add atomic application and diagnostics.
6. Validate `merge_sort`, `fallcalc`, and protected-boundary cases.
7. Run formatting, linting, workspace tests, and the full public corpus.

Later stages may classify additional anchor representations or jointly solve
cursor/raw compatibility, but they are not prerequisites for this stage and
must not expand its implementation scope.
