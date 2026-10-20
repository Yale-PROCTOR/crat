//! Type-derived io-domain subjects (seat ruling R261-3).
//!
//! The permanent io-domain boundary was previously reached two ways: a pinned
//! libc contract intercepts a stdio *stream argument position*
//! (`PointeeAccess::Stream`), and a pinned identity list holds specific
//! subjects. Neither reaches a subject that merely *has* a stream type — a
//! `FILE*` parameter promoted to `&mut FILE` by the ordinary decision claims
//! exclusive access to a handle libc holds its own pointer to.
//!
//! This module closes that by type. The rule has to be transitive to be the
//! superset R261-3 requires: reading the sealed 109-identity set against the
//! corpus source shows its named subjects carry `*mut FILE` (21) but also
//! `*mut Context` (5, brotli), `*mut BitStream` (3) and `*mut bzFile` (3) —
//! program-defined wrappers that are io-domain only because each holds a
//! `*mut FILE` field. A rule keyed on the stream type names alone would miss
//! all eleven.

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, Node, def_id::LocalDefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::Subject;

/// The stream handle types themselves. Everything else reaches the domain by
/// holding one of these, which is what makes the rule a superset rather than a
/// second identity list.
pub(crate) const IO_DOMAIN_TYPE_NAMES: &[&str] = &["FILE", "_IO_FILE", "__sFILE", "_IO_FILE_plus"];

/// How far the wrapper walk descends before conceding.
///
/// Each pointer hop and each field hop spends one, so the observed corpus
/// wrappers -- a struct holding `*mut FILE` behind a `*mut` -- need four, and a
/// wrapper of a wrapper needs six. Six is the budget, matching the returned-child
/// carrier walk, and it is what bounds self-referential shapes such as
/// `_IO_FILE::_chain: *mut _IO_FILE`.
pub(crate) const IO_DOMAIN_WALK_DEPTH: u32 = 6;

/// What a walk of one type concluded, and whether it ran out of budget while
/// doing so.
///
/// The second bit is the seat's rider (addendum 264): a `false` answer reached
/// by exhausting the depth budget is not the same as a `false` answer reached
/// by deciding, and a nonzero count of the former at Phase N reopens the depth
/// decision rather than the rule.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct WalkOutcome {
    pub(crate) io_domain: bool,
    pub(crate) budget_exhausted: bool,
}

impl WalkOutcome {
    fn decided(io_domain: bool) -> Self {
        Self {
            io_domain,
            budget_exhausted: false,
        }
    }

    fn exhausted() -> Self {
        Self {
            io_domain: false,
            budget_exhausted: true,
        }
    }

    /// Fold a child's answer into this one. A positive answer ends the walk;
    /// exhaustion anywhere below a still-negative answer is carried up, because
    /// that is exactly the case where the negative may be wrong.
    fn or(self, other: Self) -> Self {
        Self {
            io_domain: self.io_domain || other.io_domain,
            budget_exhausted: self.budget_exhausted || other.budget_exhausted,
        }
    }
}

/// Is this a stream handle, or an aggregate that holds one?
///
/// Unlike the returned-child carrier walk this one fails **open**: an unknown
/// type is not io-domain. The boundary is a hold, so a false positive costs
/// delivery on an unrelated subject, and the sealed identity pin remains the
/// authority on what must be held regardless. That is also why exhausting the
/// budget is counted rather than treated as a hold.
pub(crate) fn walk_io_domain_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> WalkOutcome {
    if depth == 0 {
        return WalkOutcome::exhausted();
    }
    match ty.kind() {
        TyKind::RawPtr(pointee, _) => walk_io_domain_ty(tcx, *pointee, depth - 1),
        TyKind::Ref(_, pointee, _) => walk_io_domain_ty(tcx, *pointee, depth - 1),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => walk_io_domain_ty(tcx, *inner, depth - 1),
        TyKind::Adt(definition, arguments) => {
            let name = tcx.item_name(definition.did());
            if IO_DOMAIN_TYPE_NAMES.contains(&name.as_str()) {
                return WalkOutcome::decided(true);
            }
            let mut outcome = WalkOutcome::default();
            for field in definition.all_fields() {
                outcome = outcome.or(walk_io_domain_ty(tcx, field.ty(tcx, arguments), depth - 1));
                if outcome.io_domain {
                    return outcome;
                }
            }
            outcome
        }
        _ => WalkOutcome::decided(false),
    }
}

/// The plain answer, for callers that do not report the budget.
pub(crate) fn is_io_domain_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> bool {
    walk_io_domain_ty(tcx, ty, depth).io_domain
}

/// Every subject whose own declared type reaches the io-domain, and how many
/// subjects the walk could not decide within its budget.
pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
) -> (FxHashSet<(LocalDefId, HirId)>, usize) {
    let mut held = FxHashSet::default();
    let mut budget_exhausted = 0;
    for subject in subjects {
        let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { continue };
        let ty = tcx.typeck(subject.fn_did).pat_ty(pattern);
        let outcome = walk_io_domain_ty(tcx, ty, IO_DOMAIN_WALK_DEPTH);
        if outcome.io_domain {
            held.insert((subject.fn_did, subject.hir_id));
        } else if outcome.budget_exhausted {
            budget_exhausted += 1;
        }
    }
    (held, budget_exhausted)
}
