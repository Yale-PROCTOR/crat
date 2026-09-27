//! **R586-2 (main 118) — a formal that is the sole origin of a mutable scalar return
//! is decided mutable.**
//!
//! A scalar return keeps its declared C mutability (`return_interface::plan`'s
//! fallback, `Ref { mutable: declared }`), and the seam refuses to hand a shared
//! source to a mutable return (`SeamBlock::SharedToMut`). avl's `#[no_mangle]`
//! `minValueNode(node: *mut Node) -> *mut Node` only reads through `node`, so
//! `node` decides shared while the return stays `&mut Node`, and the class holds
//! (`dropped-site:seam-shared-to-mut`, main 116 §1). A shared return would hand
//! C a write-capable `*mut` derived from a shared reference, so the only sound
//! direction is up: when the return borrows from exactly one argument (the
//! lifetime plan's return sources) and hands that formal back, and the formal is
//! the function's only pointer subject, it is decided mutable. A read through
//! `&mut` is a read; the model checked the formal as a shared borrow, so the
//! sole-subject condition is what keeps `&mut`'s uniqueness from meeting another
//! pointer of the function. An in-program caller that passes a shared argument
//! into the formal meets the call-site shared-to-mut gate and holds as before.
//!
//! The origin is known only once the lifetime plan is settled, and the field
//! transactions that render a view's mutability (`as_deref_mut`) are finalized
//! before it, so the driver runs this as a fixpoint: `targets` after the return
//! interfaces, and when it names a subject not yet upgraded the stage re-derives
//! with `apply` on the freshly decided table. The set only grows.

use std::collections::BTreeSet;

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Decision, DecisionTable, SubjectKind,
    emitability::EmitabilityFacts,
    lifetime::{FnSignatureRoot, FnSignatureSlot},
    seam::Form,
};

/// The one argument (its MIR local, `_1 ..= arg_count`) every return source
/// borrows from, at any depth; `None` for no source, a second argument, or the
/// return itself.
pub(crate) fn sole_origin(sources: &BTreeSet<FnSignatureSlot>) -> Option<u32> {
    let mut arguments = BTreeSet::new();
    for source in sources {
        match source.root {
            FnSignatureRoot::Arg(local) => {
                arguments.insert(local);
            }
            FnSignatureRoot::Return => return None,
        }
    }
    (arguments.len() == 1)
        .then(|| arguments.into_iter().next())
        .flatten()
}

/// The formal of every function whose return interface is the mutable scalar
/// fallback, whose return borrows from that one formal and returns it, and
/// which has no other pointer subject: the subjects to decide mutable. Read
/// after the lifetime plan and the return interfaces are settled.
pub(crate) fn targets(
    table: &DecisionTable,
    facts: &EmitabilityFacts,
) -> FxHashSet<(LocalDefId, HirId)> {
    let mut targets = FxHashSet::default();
    for (&function, interface) in &table.return_interfaces.functions {
        if interface.form != (Form::Ref { mutable: true }) {
            continue;
        }
        let Some(plan) = table.lifetime_plan.function(function) else {
            continue;
        };
        let Some(origin) = sole_origin(&plan.return_sources()) else {
            continue;
        };
        let Some(formal) = table.entries.iter().find_map(|(subject, _)| {
            (subject.fn_did == function
                && matches!(subject.kind, SubjectKind::Param { .. })
                && subject.local.as_u32() == origin)
                .then_some(subject.hir_id)
        }) else {
            continue;
        };
        // The formal is the function's only pointer subject (its merged locals
        // share it). The model checked it as a shared borrow; as `&mut` it
        // asserts uniqueness, so no other pointer of the function may alias it:
        // not a second formal (`pick(p, p)` from C), not a local loaded through
        // it (`let p = (*img).data; return p`).
        let sole_subject = table
            .entries
            .iter()
            .all(|(subject, _)| subject.fn_did != function || subject.hir_id == formal);
        // Every return hands back that formal as a bare local (`return node`):
        // the shape whose shared found form the return seam refuses.
        let mut sites = facts
            .return_sites
            .iter()
            .filter(|site| site.owner == function)
            .peekable();
        let returns_formal = sites.peek().is_some()
            && sites.all(|site| site.source_shape == "bare-local" && site.root == Some(formal));
        let decided_ref = table.entries.iter().any(|(subject, decision)| {
            subject.fn_did == function && subject.hir_id == formal && is_ref(decision)
        });
        if sole_subject && returns_formal && decided_ref {
            targets.insert((function, formal));
        }
    }
    targets
}

/// Decide the targets' shared `Ref`s mutable, on a freshly decided table, so
/// every later pass (field transactions, seams, the lifetime plan) reads the
/// mutable form. Returns the upgraded subjects' labels, for the record.
pub(crate) fn apply(
    table: &mut DecisionTable,
    targets: &FxHashSet<(LocalDefId, HirId)>,
) -> Vec<String> {
    let mut upgraded = Vec::new();
    for (subject, decision) in &mut table.entries {
        if !targets.contains(&(subject.fn_did, subject.hir_id)) {
            continue;
        }
        match decision {
            Decision::Ref { mutable } if !*mutable => {
                *mutable = true;
                upgraded.push(subject.label.clone());
            }
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::NestedSlice { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => {}
        }
    }
    upgraded.sort();
    upgraded
}

/// A plain `Ref` decision (exhaustive by rule, `import_denylist`).
fn is_ref(decision: &Decision) -> bool {
    match decision {
        Decision::Ref { .. } => true,
        Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::NestedSlice { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arg(local: u32, deref_depth: u8) -> FnSignatureSlot {
        FnSignatureSlot {
            root: FnSignatureRoot::Arg(local),
            deref_depth,
            depth: 0,
        }
    }

    /// **R586-2 witness (the selection).** `minValueNode`'s return borrows from its
    /// one formal `_1`, at the formal itself and through its pointee (`node =
    /// (*node).left`): one origin.
    #[test]
    fn r586_2_a_return_borrowing_from_one_formal_has_that_formal_as_sole_origin() {
        assert_eq!(sole_origin(&BTreeSet::from([arg(1, 0)])), Some(1));
        assert_eq!(
            sole_origin(&BTreeSet::from([arg(1, 0), arg(1, 1)])),
            Some(1)
        );
    }

    /// **R586-2 fault's control (the selection).** Two formals, the return itself,
    /// or no source: no sole origin, so no formal is upgraded.
    #[test]
    fn r586_2_two_origins_or_none_select_no_formal() {
        assert_eq!(sole_origin(&BTreeSet::from([arg(1, 0), arg(2, 0)])), None);
        assert_eq!(
            sole_origin(&BTreeSet::from([arg(1, 0), FnSignatureSlot::RETURN])),
            None
        );
        assert_eq!(sole_origin(&BTreeSet::new()), None);
    }
}
