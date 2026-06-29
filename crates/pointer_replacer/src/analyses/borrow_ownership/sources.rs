//! §8 BB3-a — malloc-source slot identification (`Ref ⇒ loan`).
//!
//! A pointer that receives a heap allocation (`malloc`/`calloc`/`realloc`/`strdup`) OWNS
//! that memory — it is not a borrow, so it must never be classified `Ref` (a reference to
//! owned heap is unsound). This module finds those source slots by scanning each
//! function's MIR for allocator `Call`s with a **bare-local** destination, then propagating
//! through kind-preserving rvalues (cast / copy / move) so the canonical C2Rust shape
//! `let p = malloc(n) as *mut T` (`_tmp = malloc()`, `_p = _tmp as *mut T`) flags BOTH the
//! call destination AND the cast target. `verify_to_fixpoint` then commits `¬ref` on any
//! source slot the model still marks `Ref`.
//!
//! Allocator recognition mirrors the ownership boundary EXACTLY: a callee is a source only
//! if it is an extern `Node::ForeignItem` whose `ident` is in `ALLOCATOR_NAMES`
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
//! The allocator-name list is duplicated from `borrow_ownership/infer/boundary/libc.rs`
//! (production `ownership/` must stay byte-unchanged, so it cannot be the shared source).
//! NOTE three lists exist in this crate and need not be identical: this one and
//! `infer/boundary/libc.rs` carry all four; `call_graph.rs` intentionally omits `strdup`
//! (it ranks alloc/dealloc *monotonicity* only). Keep this list ⊆ the libc boundary's.

use rustc_hash::FxHashSet;
use rustc_middle::{
    mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use super::{crate_slots::CrateSlots, solver::SlotRef};
use crate::utils::rustc::RustProgram;

/// Allocator callees whose result is an owned-heap source. Mirrors the libc boundary
/// (`malloc`/`calloc`/`realloc`/`strdup` are sources; `free` is a sink, `memset` a transfer).
const ALLOCATOR_NAMES: &[&str] = &["malloc", "calloc", "realloc", "strdup"];

/// Whether `func` resolves to an extern allocator declaration — gated on `Node::ForeignItem`
/// exactly like the ownership boundary (`infer.rs`), so a crate-local fn merely *named*
/// `malloc` (a wrapper / user fn) is NOT treated as a source.
fn is_allocator_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some((def_id, _)) = func.const_fn_def() else {
        return false;
    };
    let Some(local) = def_id.as_local() else {
        return false; // library / non-local callee — never a libc source
    };
    matches!(
        tcx.hir_node_by_def_id(local),
        rustc_hir::Node::ForeignItem(fi) if ALLOCATOR_NAMES.contains(&fi.ident.as_str())
    )
}

/// Depth-0 slots of locals that hold a heap allocation: bare-local allocator-call
/// destinations, plus everything reachable from them through kind-preserving rvalues
/// (cast / copy / move). See the module docs for the (sound) scope limits.
pub(crate) fn collect_malloc_source_slots(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
) -> FxHashSet<SlotRef> {
    let mut sources = FxHashSet::default();
    for &fn_did in &program.functions {
        let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
            continue;
        };
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();

        // Seed: bare-local allocator-call destinations.
        let mut source_locals: FxHashSet<Local> = FxHashSet::default();
        for bbdata in body.basic_blocks.iter() {
            if let Some(term) = &bbdata.terminator
                && let TerminatorKind::Call {
                    func, destination, ..
                } = &term.kind
                && is_allocator_call(program.tcx, func)
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
