//! **wave-6l — the extent prover** (design record
//! `agents/plan/2026-09-28-extent-analysis-design.md`, approved as the build
//! plan by R645-5; steps 1–3 started by R666-2).
//!
//! For a pointer parameter `p` of `f` and an integer parameter `n` licensed
//! as its length, the claim is **(E)**: every access `f` makes through `p`, or
//! through a pointer derived from `p`, touches only elements `[0, n)` of `p`.
//! Too short a proof is a panic where C read on; too long a licence is
//! §77's out-of-scope slice-length class. So the prover owes exactly
//! reads ⊆ `[0, n)`.
//!
//! Step 1 (this file): the MIR domain and the access check.
//!
//! **The domain.** A forward dataflow over MIR holds difference-bound facts
//! (`x − y ≤ c`) between the constant zero, integer locals, and the offset
//! (in elements) of each pointer local derived from `p`. Facts come from:
//! - assignments (copies, constants, `± c`, value-preserving casts);
//! - dominating branch conditions, which hold on the edge that takes them;
//! - loop heads, which widen to the facts that survive every back edge.
//!
//! **What is lost:** a local whose address is taken, a truncating cast, a
//! sign change without a proven lower bound, and every write to the
//! companion, which is refused outright since `n` must be the caller's
//! argument.
//!
//! **The access check.** `*q`, with `q = p + off`, is proven when the facts
//! entail `0 ≤ off` and `off + 1 ≤ n`. Everything else is refused, and the
//! first refusing access is named. A derived pointer handed to a callee is
//! refused until step 3's summaries; one cast to another pointee is refused
//! until step 2's C7.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

/// Why a proof failed: the first refusing access or operation, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Refusal {
    pub reason: String,
    pub span: rustc_span::Span,
}

/// **(E)** for parameter `pointer` of `function` against the length
/// parameter `length` (both indices into the function's parameters).
pub(crate) fn prove_parameter_extent(
    _tcx: TyCtxt<'_>,
    _function: LocalDefId,
    _pointer: usize,
    _length: usize,
) -> Result<(), Refusal> {
    Err(Refusal {
        reason: "unbuilt".to_owned(),
        span: rustc_span::DUMMY_SP,
    })
}
