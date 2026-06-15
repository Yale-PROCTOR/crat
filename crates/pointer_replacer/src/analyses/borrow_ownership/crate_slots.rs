use rustc_hash::FxHashMap;
use rustc_middle::ty::{Ty, TyKind};
use rustc_span::def_id::LocalDefId;

use super::slots::{SlotUniverse, StructFieldSlot};
use crate::utils::rustc::RustProgram;

pub const MAX_SLOT_DEPTH: u8 = 3;

pub fn ptr_chain_depth(mut ty: Ty<'_>) -> u8 {
    let mut depth = 0;
    while depth < MAX_SLOT_DEPTH {
        let Some(pointee) = pointer_pointee_ty(ty) else {
            break;
        };
        depth += 1;
        ty = pointee;
    }

    depth
}

pub struct CrateSlots {
    pub field_slots: SlotUniverse,
    pub fn_local_slots: FxHashMap<LocalDefId, SlotUniverse>,
}

impl CrateSlots {
    pub fn build(program: &RustProgram<'_>) -> Self {
        let tcx = program.tcx;
        let mut field_slots = SlotUniverse::default();

        for &did in &program.structs {
            let ty = tcx.type_of(did).skip_binder();
            let TyKind::Adt(adt_def, substs) = ty.kind() else {
                continue;
            };

            for (field_index, field_def) in adt_def.all_fields().enumerate() {
                let field_ty = field_def.ty(tcx, substs);
                if matches!(field_ty.kind(), TyKind::RawPtr(..)) {
                    field_slots.register_field(
                        StructFieldSlot {
                            struct_did: did,
                            field_index,
                        },
                        ptr_chain_depth(field_ty),
                    );
                }
            }
        }

        let mut fn_local_slots = FxHashMap::default();
        fn_local_slots.reserve(program.functions.len());

        for &f in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let mut universe = SlotUniverse::default();
            for (local, local_decl) in body.local_decls.iter_enumerated() {
                let depth = ptr_chain_depth(local_decl.ty);
                if depth > 0 {
                    universe.register_local(local, depth);
                }
            }
            fn_local_slots.insert(f, universe);
        }

        CrateSlots {
            field_slots,
            fn_local_slots,
        }
    }
}

fn pointer_pointee_ty(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::RawPtr(inner, _) => Some(*inner),
        TyKind::Ref(_, inner, _) => Some(*inner),
        _ => None,
    }
}
