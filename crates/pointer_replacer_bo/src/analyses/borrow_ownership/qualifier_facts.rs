//! Exact existing qualifier transport and explicit unavailable levels.

use super::{crate_slots::CrateSlots, mutability_facts::MutFacts, nullability::NullabilityFacts};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "state", content = "value", rename_all = "kebab-case")]
pub(crate) enum Availability<T> {
    Present(T),
    Missing(MissingFact),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum MissingFact {
    NotCollected,
    ProducerMissing,
    InnerSignNotRepresented,
    ReturnSignNotExported,
    FieldSignCoverageNotExported,
    InnerMutabilityNotRepresented,
    FieldMutabilityNotRepresented,
    PointerLevelUnrepresented,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum FatnessFact {
    ArrayLike,
    PtrDefault,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum SignFact {
    Nonnegative,
    NegOrUnknown,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum PointerLevel {
    Raw,
    Reference,
}
/// The supplied outer replay summary; never an exact per-level qualifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MutabilityFact {
    pub(crate) mutable: bool,
    pub(crate) defaulted: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct SlotFacts {
    pub(crate) slot: String,
    pub(crate) depth: u8,
    pub(crate) level: Option<PointerLevel>,
    pub(crate) qualifier_offset: usize,
    pub(crate) fatness: Availability<FatnessFact>,
    pub(crate) sign: Availability<SignFact>,
    pub(crate) mutability: Availability<MutabilityFact>,
    pub(crate) null_use: bool,
    pub(crate) null_literal: bool,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct QualifierFacts {
    pub(crate) rows: Vec<SlotFacts>,
}

impl QualifierFacts {
    pub(crate) fn canonical_json(&self) -> String {
        let mut rows = self.rows.clone();
        rows.sort_by(|a, b| a.slot.cmp(&b.slot));
        assert!(
            rows.windows(2).all(|pair| pair[0].slot != pair[1].slot),
            "duplicate qualifier key"
        );
        serde_json::json!({
            "schema": "era5a-qualifiers-v1",
            "fatness_producer": "foster",
            "sign_producer": "offset-sign",
            "mutability_semantics": "supplied-outer-replay-summary",
            "nullability_semantics": "recorded-evidence-not-nonnull-proof",
            "rows": rows,
        })
        .to_string()
    }
}

fn level_at(mut ty: rustc_middle::ty::Ty<'_>, depth: u8) -> Option<PointerLevel> {
    use rustc_middle::ty::TyKind;
    let mut seen = 0;
    loop {
        match ty.kind() {
            // Wrapper selection is not a pointer dereference. Only registered
            // BO depths are requested; extra producer levels create no slots.
            TyKind::Array(element, _) | TyKind::Slice(element) => ty = *element,
            TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => {
                if seen == depth {
                    return Some(if matches!(ty.kind(), TyKind::RawPtr(..)) {
                        PointerLevel::Raw
                    } else {
                        PointerLevel::Reference
                    });
                }
                seen += 1;
                ty = *inner;
            }
            _ => return None,
        }
    }
}

fn fat(
    value: Option<crate::analyses::type_qualifier::foster::fatness::Fatness>,
) -> Availability<FatnessFact> {
    use crate::analyses::type_qualifier::foster::fatness::Fatness;
    match value {
        Some(Fatness::Arr) => Availability::Present(FatnessFact::ArrayLike),
        Some(Fatness::Ptr) => Availability::Present(FatnessFact::PtrDefault),
        None => Availability::Missing(MissingFact::ProducerMissing),
    }
}

pub(crate) fn collect(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mutability: &MutFacts,
    nullability: &NullabilityFacts,
) -> QualifierFacts {
    collect_impl(program, slots, Some(mutability), nullability)
}

/// Diagnostic constructions without a supplied replay provider must not
/// manufacture an inferred or forced mutability fact.
pub(crate) fn collect_without_mutability(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    nullability: &NullabilityFacts,
) -> QualifierFacts {
    collect_impl(program, slots, None, nullability)
}

fn collect_impl(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mutability: Option<&MutFacts>,
    nullability: &NullabilityFacts,
) -> QualifierFacts {
    use Availability::{Missing, Present};
    use rustc_middle::{mir::RETURN_PLACE, ty::TyKind};

    use super::{
        slot_key,
        slots::{SlotId, SlotOwner},
        solver::SlotRef,
    };
    let tcx = program.tcx;
    // Existing producers, one invocation each. No new inference or use of the
    // results by any kind/ownership/borrow constraint is introduced here.
    let fatness = crate::analyses::type_qualifier::foster::fatness::fatness_analysis(program);
    let signs = crate::analyses::offset_sign::sign::offset_sign_analysis(program);
    let mut rows = Vec::new();
    for (&function, universe) in &slots.fn_local_slots {
        let represented = program.functions.contains(&function);
        let body = represented.then(|| {
            tcx.mir_drops_elaborated_and_const_checked(function)
                .borrow()
        });
        for index in 0..universe.len() {
            let id = SlotId::from_usize(index);
            let descriptor = universe.slot(id);
            let SlotOwner::Local(local) = descriptor.owner else { unreachable!() };
            let reference = SlotRef::Local(function, id);
            let depth = descriptor.depth;
            let level = body
                .as_ref()
                .and_then(|body| body.local_decls.get(local))
                .and_then(|decl| level_at(decl.ty, depth));
            let available = represented && level.is_some();
            let missing = if represented {
                MissingFact::PointerLevelUnrepresented
            } else {
                MissingFact::ProducerMissing
            };
            let sign = if !available {
                Missing(missing)
            } else if depth > 0 {
                Missing(MissingFact::InnerSignNotRepresented)
            } else if local == RETURN_PLACE {
                Missing(MissingFact::ReturnSignNotExported)
            } else {
                signs
                    .access_signs
                    .get(&function)
                    .map(|bits| {
                        Present(if bits.contains(local) {
                            SignFact::NegOrUnknown
                        } else {
                            SignFact::Nonnegative
                        })
                    })
                    .unwrap_or(Missing(MissingFact::ProducerMissing))
            };
            let mutable = if !available {
                Missing(missing)
            } else if depth > 0 {
                Missing(MissingFact::InnerMutabilityNotRepresented)
            } else {
                mutability
                    .map(|facts| {
                        Present(MutabilityFact {
                            mutable: facts.is_mutable(function, local),
                            defaulted: facts.is_defaulted(function, local),
                        })
                    })
                    .unwrap_or(Missing(MissingFact::ProducerMissing))
            };
            rows.push(SlotFacts {
                slot: slot_key::local_key(tcx, function, local.as_usize(), depth),
                depth,
                level,
                qualifier_offset: depth as usize,
                fatness: if available {
                    fat(fatness.function_body_fact(function, local.as_usize(), depth as usize))
                } else {
                    Missing(missing)
                },
                sign,
                mutability: mutable,
                null_use: nullability.is_null_use.contains(&reference),
                null_literal: nullability.null_literal.contains(&reference),
            });
        }
    }
    for index in 0..slots.field_slots.len() {
        let id = SlotId::from_usize(index);
        let descriptor = slots.field_slots.slot(id);
        let SlotOwner::Field(field) = descriptor.owner else { unreachable!() };
        let reference = SlotRef::Field(id);
        let depth = descriptor.depth;
        let represented = program.structs.contains(&field.struct_did);
        let ty = represented.then(|| tcx.type_of(field.struct_did).skip_binder());
        let level = ty.and_then(|ty| {
            let TyKind::Adt(adt, args) = ty.kind() else {
                return None;
            };
            adt.all_fields()
                .nth(field.field_index)
                .and_then(|definition| level_at(definition.ty(tcx, args), depth))
        });
        let available = represented && level.is_some();
        let missing = if represented {
            MissingFact::PointerLevelUnrepresented
        } else {
            MissingFact::ProducerMissing
        };
        let sign = if !available {
            Missing(missing)
        } else if depth > 0 {
            Missing(MissingFact::InnerSignNotRepresented)
        } else if signs
            .field_access_signs
            .contains(&crate::analyses::borrow::StructFieldSlot {
                struct_did: field.struct_did,
                field_index: field.field_index,
            })
        {
            Present(SignFact::NegOrUnknown)
        } else {
            Missing(MissingFact::FieldSignCoverageNotExported)
        };
        rows.push(SlotFacts {
            slot: slot_key::field_key(tcx, field.struct_did, field.field_index, depth),
            depth,
            level,
            qualifier_offset: depth as usize,
            fatness: if available {
                fat(fatness.struct_field_fact(field.struct_did, field.field_index, depth as usize))
            } else {
                Missing(missing)
            },
            sign,
            mutability: Missing(if !available {
                missing
            } else if depth > 0 {
                MissingFact::InnerMutabilityNotRepresented
            } else {
                MissingFact::FieldMutabilityNotRepresented
            }),
            null_use: nullability.is_null_use.contains(&reference),
            null_literal: nullability.null_literal.contains(&reference),
        });
    }
    rows.sort_by(|a, b| a.slot.cmp(&b.slot));
    assert!(
        rows.windows(2).all(|pair| pair[0].slot != pair[1].slot),
        "duplicate qualifier slot identity"
    );
    QualifierFacts { rows }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod export_tests;
