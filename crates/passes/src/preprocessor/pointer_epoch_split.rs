use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

// the finished plan consumed by `AstVisitor`. see the design spec's
// "Soundness Invariant" section for what may appear here.
pub(crate) struct PointerEpochSplitPlan {
    // per-occurrence rename: HIR id of a path expr -> epoch local name.
    pub path_renames: FxHashMap<HirId, Symbol>,
    // HIR id of a base-changing assignment expr -> the `let` to emit in its place.
    pub assignment_replacements: FxHashMap<HirId, EpochLetIntro>,
    // `let`-stmt HIR ids of dead scratch inits to delete.
    pub original_inits_to_remove: FxHashSet<HirId>,
}

pub(crate) struct EpochLetIntro {
    pub new_name: Symbol,
    pub ty_string: String,
}

impl PointerEpochSplitPlan {
    fn empty() -> Self {
        PointerEpochSplitPlan {
            path_renames: FxHashMap::default(),
            assignment_replacements: FxHashMap::default(),
            original_inits_to_remove: FxHashSet::default(),
        }
    }
}

// entry point. `exclude` holds local binding HIR ids already claimed by other
// preprocessor rewrites. filled in by later tasks; empty for now.
pub(crate) fn analyze(_tcx: TyCtxt<'_>, _exclude: &FxHashSet<HirId>) -> PointerEpochSplitPlan {
    PointerEpochSplitPlan::empty()
}
