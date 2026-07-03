//! §8 BB3-a — malloc-source slot identification (`Ref ⇒ loan`).
//!
//! A pointer that receives a heap allocation (`malloc`/`calloc`/`realloc`/`strdup`) OWNS
//! that memory — it is not a borrow, so it must never be classified `Ref` (a reference to
//! owned heap is unsound). This module finds those source slots by scanning each
//! function's MIR for allocator `Call`s with a **bare-local** destination, then propagating
//! through kind-preserving rvalues (cast / copy / move) so the canonical C2Rust shape
//! `let p = malloc(n) as *mut T` (`_tmp = malloc()`, `_p = _tmp as *mut T`) flags BOTH the
//! call destination AND the cast target. §NB0: `emit_crate_ownership_constraints` asserts
//! `¬ref` on every source slot EAGERLY at emission time (the hoisted BB3-a invariant), so
//! no model at any stage can mark a source `Ref`.
//!
//! Allocator recognition mirrors the ownership boundary EXACTLY: a callee is a source only
//! if it is an extern `Node::ForeignItem` whose `ident` is a `boundary_table` ForeignC source
//! (`infer.rs` routes only `ForeignItem` callees to `libc_call`; a crate-local fn named
//! `malloc` emits no source, so it must not be flagged here either — matching by bare name
//! would over-demote it). COUPLING INVARIANT: this gate is exactly the ownership source set
//! ONLY because the boundary's other arms (`Item`→`Boundary::call`, `ImplItem` TODO,
//! `library_call`/`unknown_call`) emit `borrow`, never `source`. If a future boundary change
//! sources a non-`ForeignItem` callee, this gate would under-match (an unsound `Ref` could
//! survive) — revisit it then.
//!
//! Scope / known misses (deferred; sound — none over-demote):
//! - **Bare-local call destinations** only. A PROJECTED destination (`*out = malloc()`,
//!   base local `out` often a *param*) is skipped — flagging `destination.local` there
//!   would wrongly demote the param. The stored pointee is a deferred miss.
//! - Struct-field stores and interprocedural (callee-returned) allocations into caller
//!   slots are not covered (depth>0 / cross-fn gaps).
//!
//! §NB0: allocator recognition now reads the unified `boundary_table` (the ForeignC
//! `Source` rows) instead of a module-local list. The table's contents still mirror
//! `infer/boundary/libc.rs` (production `ownership/` must stay byte-unchanged, so it
//! cannot be the shared source), and the `nb0_consistency_libc_dispatch` test enforces
//! that mirroring. NOTE `call_graph.rs` intentionally omits `strdup` (it ranks
//! alloc/dealloc *monotonicity* only) — the lists need not be identical.

use rustc_hash::FxHashSet;
use rustc_middle::{
    mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use super::{boundary_table, crate_slots::CrateSlots, solver::SlotRef};

/// Whether `func` resolves to an extern allocator declaration — gated on `Node::ForeignItem`
/// exactly like the ownership boundary (`infer.rs`), so a crate-local fn merely *named*
/// `malloc` (a wrapper / user fn) is NOT treated as a source. The name set is the
/// boundary table's ForeignC `Source` rows (§NB0).
fn is_allocator_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some((def_id, _)) = func.const_fn_def() else {
        return false;
    };
    let Some(local) = def_id.as_local() else {
        return false; // library / non-local callee — never a libc source
    };
    matches!(
        tcx.hir_node_by_def_id(local),
        rustc_hir::Node::ForeignItem(fi)
            if boundary_table::sources_foreign().any(|name| name == fi.ident.as_str())
    )
}

/// Depth-0 slots of locals that hold a heap allocation: bare-local allocator-call
/// destinations, plus everything reachable from them through kind-preserving rvalues
/// (cast / copy / move). See the module docs for the (sound) scope limits.
///
/// §NB0: takes `(tcx, functions)` instead of `&RustProgram` so the emission path
/// (which holds a `CrateCtxt`, not a `RustProgram`) can compute the set for the
/// hoisted eager `¬ref(source)` constraints.
pub(crate) fn collect_malloc_source_slots(
    tcx: TyCtxt<'_>,
    functions: &[rustc_span::def_id::LocalDefId],
    slots: &CrateSlots,
) -> FxHashSet<SlotRef> {
    let mut sources = FxHashSet::default();
    for &fn_did in functions {
        let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();

        // Seed: bare-local allocator-call destinations.
        let mut source_locals: FxHashSet<Local> = FxHashSet::default();
        for bbdata in body.basic_blocks.iter() {
            if let Some(term) = &bbdata.terminator
                && let TerminatorKind::Call {
                    func, destination, ..
                } = &term.kind
                && is_allocator_call(tcx, func)
                && let Some(local) = destination.as_local()
            {
                source_locals.insert(local);
            }
        }

        // Fixpoint: propagate through kind-preserving rvalues so a cast/copy/move of a
        // source (e.g. `let p = malloc() as *mut T`) is itself a source. Non-pointer cast
        // targets (`as usize`) have no depth-0 slot and are dropped at the slot lookup.
        let mut changed = true;
        while changed {
            changed = false;
            for bbdata in body.basic_blocks.iter() {
                for stmt in &bbdata.statements {
                    let StatementKind::Assign(assign) = &stmt.kind else {
                        continue;
                    };
                    let (dest, rvalue) = &**assign;
                    let Some(dest_local) = dest.as_local() else {
                        continue;
                    };
                    if source_locals.contains(&dest_local) {
                        continue;
                    }
                    let rhs_local = match rvalue {
                        Rvalue::Cast(_, op, _) | Rvalue::Use(op) => op.place(),
                        Rvalue::CopyForDeref(place) => Some(*place),
                        _ => None,
                    }
                    .and_then(|place| place.as_local());
                    if rhs_local.is_some_and(|src| source_locals.contains(&src)) {
                        source_locals.insert(dest_local);
                        changed = true;
                    }
                }
            }
        }

        for local in source_locals {
            if let Some(slot_id) = universe.slot_for_local_depth(local, 0) {
                sources.insert(SlotRef::Local(fn_did, slot_id));
            }
        }
    }
    sources
}
