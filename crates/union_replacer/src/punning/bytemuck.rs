use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
pub use utils::bytemuck::{
    BytemuckDerive, BytemuckDerivePlan, BytemuckDeriveVisitor, BytemuckTypeClassifier,
    FieldTypeClass,
};

use super::raw_struct::UnionFieldClassification;

/// This function must be called after the analysis.
pub fn build_bytemuck_derive_plan<'tcx>(
    tcx: TyCtxt<'tcx>,
    punning_tys: &[LocalDefId],
    field_classes: &FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
) -> BytemuckDerivePlan {
    let mut classifier = BytemuckTypeClassifier::new(tcx);
    let mut plan = BytemuckDerivePlan::default();

    for &union_ty in punning_tys {
        let Some(fields) = field_classes.get(&union_ty) else {
            continue;
        };
        for field in fields {
            if !field.class.is_other() {
                plan.collect_from_ty(tcx, &mut classifier, field.field_ty);
            }
        }
    }

    plan
}
