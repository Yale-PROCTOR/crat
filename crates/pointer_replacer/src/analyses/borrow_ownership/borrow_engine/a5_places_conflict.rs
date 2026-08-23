//! A5 context at the distinct-local place-conflict seam.

use std::collections::BTreeSet;

use rustc_middle::{
    mir::{Body, Local, Place},
    ty::TyCtxt,
};

use super::places_conflict::{AccessDepth, PlaceConflictBias, places_conflict};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LocalPair {
    first: Local,
    second: Local,
}

impl LocalPair {
    fn new(left: Local, right: Local) -> Option<Self> {
        (left != right).then(|| Self {
            first: left.min(right),
            second: left.max(right),
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ParameterOverlap {
    pairs: BTreeSet<LocalPair>,
}

impl ParameterOverlap {
    pub(crate) fn from_pairs(pairs: impl IntoIterator<Item = (Local, Local)>) -> Self {
        Self {
            pairs: pairs
                .into_iter()
                .filter_map(|(left, right)| LocalPair::new(left, right))
                .collect(),
        }
    }

    pub(crate) fn contains(&self, left: Local, right: Local) -> bool {
        LocalPair::new(left, right).is_some_and(|pair| self.pairs.contains(&pair))
    }

    pub(crate) fn partners(&self, local: Local) -> Vec<Local> {
        self.pairs
            .iter()
            .filter_map(|pair| {
                if pair.first == local {
                    Some(pair.second)
                } else if pair.second == local {
                    Some(pair.first)
                } else {
                    None
                }
            })
            .collect()
    }

    pub(crate) fn has_local(&self, local: Local) -> bool {
        self.pairs
            .iter()
            .any(|pair| pair.first == local || pair.second == local)
    }
}

pub(crate) fn places_conflict_with_parameter_overlap<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_place: Place<'tcx>,
    access_place: Place<'tcx>,
    access_depth: AccessDepth,
    bias: PlaceConflictBias,
    parameter_overlap: Option<&ParameterOverlap>,
) -> bool {
    if borrow_place.local == access_place.local
        || !parameter_overlap
            .is_some_and(|context| context.contains(borrow_place.local, access_place.local))
    {
        return places_conflict(tcx, body, borrow_place, access_place, access_depth, bias);
    }

    if body.local_decls[borrow_place.local].ty != body.local_decls[access_place.local].ty {
        return true;
    }
    let normalized_access = Place {
        local: borrow_place.local,
        projection: access_place.projection,
    };
    places_conflict(
        tcx,
        body,
        borrow_place,
        normalized_access,
        access_depth,
        bias,
    )
}

#[cfg(test)]
mod tests {
    use rustc_abi::FieldIdx;
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{
        mir::{Local, Place, PlaceElem},
        ty::TyCtxt,
    };
    use rustc_span::def_id::LocalDefId;

    use super::*;
    use crate::analyses::borrow_ownership::borrow_engine::places_conflict::places_conflict;

    fn run(code: &str, check: impl for<'tcx> FnOnce(TyCtxt<'tcx>, LocalDefId) + Send) {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let function = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|owner| owner.as_owner())
                .find_map(|owner| {
                    let OwnerNode::Item(item) = owner.node() else {
                        return None;
                    };
                    matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
                })
                .expect("fixture function");
            check(tcx, function);
        })
        .unwrap();
    }

    fn deref<'tcx>(tcx: TyCtxt<'tcx>, local: usize) -> Place<'tcx> {
        Place::from(Local::from_usize(local)).project_deeper(&[PlaceElem::Deref], tcx)
    }

    #[test]
    fn w1_distinct_mutable_formals_conflict_only_with_effective_overlap() {
        run(
            "unsafe fn f(x: *mut i32, y: *mut i32) { *x = *y + 1; }",
            |tcx, function| {
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let x = deref(tcx, 1);
                let y = deref(tcx, 2);
                let overlap = ParameterOverlap::from_pairs([(x.local, y.local)]);
                assert!(!places_conflict(
                    tcx,
                    &body,
                    x,
                    y,
                    AccessDepth::Deep,
                    PlaceConflictBias::Overlap,
                ));
                assert!(places_conflict_with_parameter_overlap(
                    tcx,
                    &body,
                    x,
                    y,
                    AccessDepth::Deep,
                    PlaceConflictBias::Overlap,
                    Some(&overlap),
                ));
            },
        );
    }

    #[test]
    fn w2_projection_disjoint_fields_remain_disjoint() {
        run(
            "struct S { a: i32, b: i32 } unsafe fn f(x: *mut S, y: *mut S) { \
             (*x).a = (*y).b; }",
            |tcx, function| {
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let x = deref(tcx, 1).project_deeper(
                    &[PlaceElem::Field(FieldIdx::from_usize(0), tcx.types.i32)],
                    tcx,
                );
                let y = deref(tcx, 2).project_deeper(
                    &[PlaceElem::Field(FieldIdx::from_usize(1), tcx.types.i32)],
                    tcx,
                );
                let overlap = ParameterOverlap::from_pairs([(x.local, y.local)]);
                assert!(!places_conflict_with_parameter_overlap(
                    tcx,
                    &body,
                    x,
                    y,
                    AccessDepth::Deep,
                    PlaceConflictBias::Overlap,
                    Some(&overlap),
                ));
            },
        );
    }

    #[test]
    fn w3_offset_actuals_are_not_dismissed_as_distinct_formal_bases() {
        run(
            "unsafe fn f(x: *mut i32, y: *mut i32) { *x = *y; }",
            |tcx, function| {
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let x = deref(tcx, 1);
                let y = deref(tcx, 2);
                let overlap = ParameterOverlap::from_pairs([(x.local, y.local)]);
                assert!(places_conflict_with_parameter_overlap(
                    tcx,
                    &body,
                    x,
                    y,
                    AccessDepth::Deep,
                    PlaceConflictBias::Overlap,
                    Some(&overlap),
                ));
            },
        );
    }
}
