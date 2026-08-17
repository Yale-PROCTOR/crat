//! classifies pointer parameters as demotable from `SliceCursor` to a plain
//! slice: no definitely-negative movement reaches the param and its function
//! is not reachable through a function pointer, so every call site's
//! rebase-to-pos-0 construction is behavior-preserving and the body can
//! re-materialize the cursor with a pos-0 prologue.
//!
//! rewriter-agnostic: knows nothing about pointer-kind decisions. consumers
//! intersect `is_demotable` with the params they decide to make cursors.

use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Local;

use crate::{
    analyses::{fn_ptr_groups::FnPtrGroups, offset_sign::sign::OffsetSignResult},
    utils::rustc::RustProgram,
};

pub struct CursorDemotion {
    /// params safe to take as `&[T]` with a pos-0 cursor prologue
    demotable: FxHashSet<(LocalDefId, Local)>,
}

impl CursorDemotion {
    pub fn compute(
        input: &RustProgram<'_>,
        offset_signs: &OffsetSignResult,
        fn_ptr_groups: &FnPtrGroups,
    ) -> Self {
        let mut demotable = FxHashSet::default();
        for &did in &input.functions {
            if fn_ptr_groups.fn_to_group.contains_key(&did) {
                continue;
            }
            let body = input.tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let definite = offset_signs.definite_signs.get(&did);
            for local in body.args_iter() {
                if !definite.is_some_and(|d| d.contains(local)) {
                    demotable.insert((did, local));
                }
            }
        }
        Self { demotable }
    }

    pub fn is_demotable(&self, did: LocalDefId, local: Local) -> bool {
        self.demotable.contains(&(did, local))
    }
}
