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

/// A byte count that spells the pointee's OWN size — `memset(p, 0,
/// size_of::<T>())` on a `*mut T` — is exactly one element: the claim a thin
/// reference carries. Read from the count operand's spelling beneath its
/// casts, against the operand's own pointee (a `c_void` position types the
/// argument, not the row). Anything else at a `ByteCount` position keeps the
/// row's multi-element extent.
///
/// The two forms are compared on the type's FINAL PATH SEGMENT, which is all
/// they can share: the pointee is a printed type, carrying the path from the
/// crate root (`src::libtree::small_vec_u64_t`), while the count is the source
/// text of `size_of::<..>()`, which names the type as the call's own module
/// sees it (`small_vec_u64_t`). Measured at batch 8: with a whole-path
/// comparison the refinement missed every corpus site and libtree's
/// `small_vec_u64_init::v#1` lost its delivery.
pub(crate) fn byte_count_is_one_element(fact: &super::raw_boundary::ForeignCallArgFact) -> bool {
    let Some(count) = &fact.contract_count else { return false };
    let pointee = fact.operand_pointee.trim().trim_start_matches("::");
    if pointee.is_empty() || pointee == "c_void" || pointee.ends_with("::c_void") {
        return false;
    }
    let pointee = pointee.rsplit("::").next().unwrap_or(pointee);
    let mut spelling = count.expression.split_whitespace().collect::<String>();
    // Peel the trailing `as <ty>` casts and grouping parentheses C2Rust
    // wraps a `size_of` in.
    loop {
        if let Some((head, _)) = spelling.rsplit_once("as")
            && head.ends_with(')')
        {
            spelling = head.to_owned();
        } else if spelling.starts_with('(') && spelling.ends_with(')') && spelling.len() > 2 {
            spelling = spelling[1..spelling.len() - 1].to_owned();
        } else {
            break;
        }
    }
    let spelling = spelling.as_str();
    [
        "::std::mem::size_of::<",
        "std::mem::size_of::<",
        "::core::mem::size_of::<",
        "core::mem::size_of::<",
        "size_of::<",
    ]
    .iter()
    .any(|prefix| {
        spelling
            .strip_prefix(prefix)
            .and_then(|rest| rest.strip_suffix(">()"))
            .is_some_and(|argument| {
                let argument = argument.trim_start_matches("::");
                !argument.is_empty() && argument.rsplit("::").next().unwrap_or(argument) == pointee
            })
    })
}

/// Subjects that reach such a position. A subject in this set may not take a
/// THIN reference form.
pub(crate) fn collect(facts: &EmitabilityFacts) -> FxHashSet<(LocalDefId, HirId)> {
    let mut out = FxHashSet::default();
    for fact in &facts.foreign_call_args {
        if !position_consumes_many_elements(&fact.callee, fact.argument_index, &fact.target)
            || byte_count_is_one_element(fact)
        {
            continue;
        }
        if let Some(root) = fact.direct_subject_root() {
            out.insert((fact.caller, root));
        }
    }
    out
}
