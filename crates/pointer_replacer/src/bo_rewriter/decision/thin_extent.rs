//! Thin references at multi-element foreign positions (seat rulings R272-1 and
//! R280-1, route (A)).
//!
//! A thin `&T` carries provenance for exactly ONE element. A foreign position
//! whose contract consumes more than one — `strlen(s)` reading to the NUL,
//! `strncpy(dest, src, n)` reading up to `n`, `snprintf(buf, len, ..)` writing
//! up to `len` — is handed that one-element claim and accesses past it. That is
//! the same Stacked-Borrows violation `&c_void` commits, with a typed pointee
//! instead of an opaque one: the retag covers one element and the callee reads
//! or writes beyond it. Miri confirms it on the `strlen` shape (R272-1(d)).
//!
//! **The predicate is the contract's extent, not a symbol list.** The counted
//! family this started as — `memcpy`, `strncpy`, `snprintf` — is four of the 88
//! census sites; 80 are NUL-terminated, where no length exists at the call at
//! all. Both are the same defect, so both are held, and the classification
//! lives in ONE place: the extent column of the pinned contract table
//! (`raw_boundary_contracts::ArgumentExtent`). A symbol list here would be a
//! second table that could drift from the first.
//!
//! What is deliberately NOT held:
//!
//! - **Slices and Options of slices.** A slice carries `len · size_of::<T>()`,
//!   which is an extent; the rule is about extent, not about references. The
//!   hold therefore sits at the thin-`Ref` return, below every arm that yields
//!   a form carrying its own extent, and below the owning arm for the reason
//!   R271-1 recorded (a void allocation becomes `Box<[u8]>` with a real byte
//!   count).
//! - **`one-element` and `lifecycle` positions.** One element is exactly what a
//!   thin reference carries; a lifecycle position accesses no elements.
//! - **Unmodeled foreign positions.** No contract row means no extent claim,
//!   and inventing one would hold on absence of evidence.
//! - **Local callees.** `foreign_call_args` carries foreign positions only, and
//!   a local callee's parameter is a subject in its own right.

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{emitability::EmitabilityFacts, raw_boundary_contracts::classify_contract};

/// Does this exact foreign position consume more than one element?
///
/// Answered by the pinned contract table, so a position's extent is stated once
/// and read here. A position with no row, or one whose row does not apply at
/// this target type, answers `false`: absence of a contract is not evidence of
/// a multi-element access.
pub(crate) fn position_consumes_many_elements(
    callee: &super::raw_boundary::ForeignSymbolKey,
    argument_index: usize,
    target: &super::raw_boundary::RawTargetType,
) -> bool {
    classify_contract(callee, argument_index, target)
        .is_ok_and(|contract| !contract.extent.fits_one_element())
}

/// Subjects that reach such a position. A subject in this set may not take a
/// THIN reference form.
pub(crate) fn collect(facts: &EmitabilityFacts) -> FxHashSet<(LocalDefId, HirId)> {
    let mut out = FxHashSet::default();
    for fact in &facts.foreign_call_args {
        if !position_consumes_many_elements(&fact.callee, fact.argument_index, &fact.target) {
            continue;
        }
        let root = fact
            .direct_storage
            .map(|(storage, _)| storage)
            .or(fact.root);
        if let Some(root) = root {
            out.insert((fact.caller, root));
        }
    }
    out
}
