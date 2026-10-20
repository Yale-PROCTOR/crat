//! Compiler type observations for G-FOLD. These are not ownership or effect proofs.

use std::collections::BTreeSet;

use rustc_hash::FxHashSet;
use rustc_middle::{
    mir::{
        Body, Location, Place,
        visit::{PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use serde::{Deserialize, Serialize};

use super::super::{ownership_access::PlaceSyntax, slot_key};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum PointerFlavor {
    RawConst,
    RawMut,
    SharedReference,
    MutableReference,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct PlaceType {
    pub(crate) function: String,
    pub(crate) place: PlaceSyntax,
    pub(crate) value_type: String,
    pub(crate) value_struct: Option<String>,
    pub(crate) pointer: Option<PointerFlavor>,
    pub(crate) pointee_struct: Option<String>,
    /// Declaration identity alone cannot distinguish different generic arguments.
    pub(crate) pointee_type: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct Field {
    pub(crate) index: u32,
    pub(crate) name: String,
    pub(crate) field_key: Option<String>,
    pub(crate) value_type: String,
    pub(crate) value_struct: Option<String>,
    pub(crate) pointer: Option<PointerFlavor>,
    pub(crate) pointee_struct: Option<String>,
    pub(crate) pointee_type: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct Structure {
    pub(crate) identity: String,
    pub(crate) declared_type: String,
    /// All declarations, including nonpointer fields, preserve MIR field indices.
    pub(crate) fields: Vec<Field>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Inputs {
    pub(crate) places: Vec<PlaceType>,
    pub(crate) structures: Vec<Structure>,
}

/// R339-5 D4: an operation the fold vocabulary need not represent, because it
/// moves no token — an integer branch predicate such as `key < (*node).key`.
///
/// The rule is read off what the occurrence records, never off its debug
/// description: the destination is a place the type table says is not a
/// pointer, and no operand resolves to a slot. A pointer operand is recorded
/// `Present`, so `p < q` over pointers still refuses, which is K-D4.
pub(crate) fn moves_no_token(
    inputs: &Inputs,
    function: &str,
    occurrence: &super::super::origin_evidence::SourceOccurrence,
) -> bool {
    use super::super::{
        origin_evidence::OriginAvailability::Present, ownership_access::Expression,
    };
    if !matches!(
        occurrence.syntax.expression,
        Expression::Unrepresented { .. }
    ) {
        return false;
    }
    if matches!(occurrence.destination, Present(_))
        || occurrence.arguments.iter().any(|a| matches!(a, Present(_)))
    {
        return false;
    }
    // An unknown destination type is not evidence of a non-pointer.
    inputs
        .places
        .iter()
        .find(|row| row.function == function && row.place == occurrence.syntax.destination)
        .is_some_and(|row| row.pointer.is_none())
}

fn type_name<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> String {
    rustc_middle::ty::print::with_no_trimmed_paths!(format!("{:?}", tcx.erase_regions(ty)))
}

fn structure(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<String> {
    match ty.kind() {
        TyKind::Adt(adt, _) if adt.is_struct() && adt.did().is_local() => {
            Some(tcx.def_path_str(adt.did()))
        }
        _ => None,
    }
}

fn pointer(ty: Ty<'_>) -> Option<(Ty<'_>, PointerFlavor)> {
    use rustc_hir::Mutability;
    match ty.kind() {
        TyKind::RawPtr(inner, Mutability::Not) => Some((*inner, PointerFlavor::RawConst)),
        TyKind::RawPtr(inner, Mutability::Mut) => Some((*inner, PointerFlavor::RawMut)),
        TyKind::Ref(_, inner, Mutability::Not) => Some((*inner, PointerFlavor::SharedReference)),
        TyKind::Ref(_, inner, Mutability::Mut) => Some((*inner, PointerFlavor::MutableReference)),
        _ => None,
    }
}

impl Inputs {
    pub(crate) fn collect(program: &RustProgram<'_>) -> Self {
        let tcx = program.tcx;
        let mut result = Self::default();
        let mut places = BTreeSet::new();
        let mut types = Vec::new();
        struct Places<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            body: &'a Body<'tcx>,
            function: &'a str,
            places: &'a mut BTreeSet<PlaceType>,
            types: &'a mut Vec<Ty<'tcx>>,
        }
        impl<'tcx> Places<'_, 'tcx> {
            fn record(&mut self, place: Place<'tcx>) {
                let ty = place.ty(self.body, self.tcx).ty;
                let pointer = pointer(ty);
                if self.places.insert(PlaceType {
                    function: self.function.into(),
                    place: place.into(),
                    value_type: type_name(self.tcx, ty),
                    value_struct: structure(self.tcx, ty),
                    pointer: pointer.map(|(_, flavor)| flavor),
                    pointee_struct: pointer.and_then(|(inner, _)| structure(self.tcx, inner)),
                    pointee_type: pointer.map(|(inner, _)| type_name(self.tcx, inner)),
                }) {
                    self.types.push(ty);
                }
            }
        }
        impl<'tcx> Visitor<'tcx> for Places<'_, 'tcx> {
            fn visit_place(
                &mut self,
                place: &Place<'tcx>,
                context: PlaceContext,
                location: Location,
            ) {
                self.record(*place);
                self.super_place(place, context, location);
            }
        }
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let name = tcx.def_path_str(function);
            let mut visitor = Places {
                tcx,
                body: &body,
                function: &name,
                places: &mut places,
                types: &mut types,
            };
            for local in body.local_decls.indices() {
                visitor.record(Place::from(local));
            }
            visitor.visit_body(&body);
        }
        // Discover declarations through types, even when program.structs is empty.
        // Definition identity bounds recursive generic declarations without unfolding them.
        let mut seen = FxHashSet::default();
        while let Some(ty) = types.pop() {
            if let Some((inner, _)) = pointer(ty) {
                types.push(inner);
                continue;
            }
            match ty.kind() {
                TyKind::Array(inner, _) | TyKind::Slice(inner) => types.push(*inner),
                TyKind::Tuple(elements) => types.extend(elements.iter()),
                TyKind::Adt(adt, args) if adt.is_struct() && adt.did().is_local() => {
                    types.extend(args.iter().filter_map(|argument| argument.as_type()));
                    if !seen.insert(adt.did()) {
                        continue;
                    }
                    let did = adt.did().expect_local();
                    let declared = tcx.type_of(did).skip_binder();
                    let TyKind::Adt(_, args) = declared.kind() else { continue };
                    let mut fields = Vec::new();
                    for (index, field) in adt.non_enum_variant().fields.iter_enumerated() {
                        let ty = field.ty(tcx, args);
                        let pointer = pointer(ty);
                        types.push(ty);
                        fields.push(Field {
                            index: index.as_u32(),
                            name: field.name.to_string(),
                            field_key: pointer
                                .map(|_| slot_key::field_key(tcx, did, index.as_usize(), 0)),
                            value_type: type_name(tcx, ty),
                            value_struct: structure(tcx, ty),
                            pointer: pointer.map(|(_, flavor)| flavor),
                            pointee_struct: pointer.and_then(|(inner, _)| structure(tcx, inner)),
                            pointee_type: pointer.map(|(inner, _)| type_name(tcx, inner)),
                        });
                    }
                    result.structures.push(Structure {
                        identity: tcx.def_path_str(did),
                        declared_type: type_name(tcx, declared),
                        fields,
                    });
                }
                _ => {}
            }
        }
        result.places = places.into_iter().collect();
        result.structures.sort();
        result.structures.dedup();
        result
    }
}
