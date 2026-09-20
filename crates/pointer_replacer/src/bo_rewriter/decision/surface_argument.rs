//! Owned constructors for already-admitted borrowed parameters of raw wrappers.
//! Exposure and decision tables supply admission; this module adds no proof.

use std::collections::BTreeSet;

use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{
    Arm, Decision, DecisionTable, SubjectKind,
    exposure::{ExposurePolicy, ExposureSurfacePlan},
    seam::{self, Form, GlueSpec},
};
use crate::bo_rewriter::{
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan, SignatureClassId,
    },
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, CanonicalSiteKey, FALLBACK_EXTENT_RECEIPT,
        MechanicalEvidence, MechanicalExtent, MechanicalFamily, MechanicalMechanism,
        MechanicalObligationEvent, MechanicalObligationKey, MechanicalObligationPlan,
        MechanicalRetention, MechanicalStage, MechanicalState, MechanicalSubjectKey,
        SLICE_EXTENT_WAIVER_ID, UnsafeContextPresentation,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SurfaceArgumentPlan {
    pub(crate) owner_class: SignatureClassId,
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) parameter_index: usize,
    pub(crate) parameter_name: String,
    /// **R473-3** — the expression the glue is rendered over: the parameter
    /// itself, or the parameter cast to the delivered element type where the C
    /// ABI handed the wrapper a `c_void` pointer. See [`wrapper_base`].
    pub(crate) base: String,
    pub(crate) atom_ids: Vec<String>,
    pub(crate) form: Form,
    pub(crate) spec: GlueSpec,
    pub(crate) bridge: BridgeSitePlan,
    pub(crate) obligation: MechanicalObligationPlan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SurfaceArgumentFailure {
    pub(crate) owner_class: SignatureClassId,
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) parameter_index: usize,
    pub(crate) reason: &'static str,
}

/// **R473-3 — the wrapper's base.** The generated wrapper keeps the C ABI's own
/// signature, so its parameter is whatever C declared: for brotli's hasher
/// accessors, `extra: *mut libc::c_void`. The inner function's parameter is
/// delivered `&mut [u32]` / `&mut [u8]`, and the slice the wrapper builds for
/// it has no element type to infer from a `c_void` base —
/// `__crat_safe_AddrH40(core::slice::from_raw_parts_mut(extra,
/// crate::FALLBACK_SLICE_EXTENT))` is `expected *mut u32, found *mut
/// libc::c_void` at nine wrappers in brotli's first failing verify tree, and
/// those wrappers then revert.
///
/// The element type is the one the converted signature was written from — the
/// void region's own `element`, not a guess — so the cast is a retyping of the
/// base and nothing else. The extent is untouched: no receipt moves and no
/// waiver widens (§77). A base that is not `c_void`, a form that is not a
/// slice, or a region that carries no element leaves the parameter alone.
pub(crate) fn wrapper_base(
    parameter_name: &str,
    form: Form,
    void_pointee: bool,
    delivered_element: Option<&str>,
) -> String {
    match (form, void_pointee, delivered_element) {
        (Form::Slice { .. } | Form::Opt { slice: true, .. }, true, Some(element)) => {
            format!("{parameter_name}.cast::<{element}>()")
        }
        _ => parameter_name.to_owned(),
    }
}

/// **R477-3 — the element the CONVERTED parameter carries, which is the one
/// the call must type-check against.** A void region's parameter becomes a
/// BYTE slice — wave-6b states it in their module header, "the parameter
/// becomes a byte slice (`&mut [u8]` / `&[u8]`)" — while `Region::element` is
/// the width the BODY reinterprets at (`u32` for `AddrH40`, `u16` for
/// `HeadH42`). Casting to the region's element passed only where the two
/// agree: batch 20 verified the six `TinyHashH4x` wrappers (`u8` both ways)
/// and kept `AddrH4{0,1,2}` at `expected *mut u8, found *mut u32` and
/// `HeadH42` at `found *mut u16`.
///
/// A byte view is a LOCAL's region, not a parameter's, so no wrapper argument
/// is built from it.
pub(crate) fn delivered_element(region: &super::void_region::Region) -> Option<&'static str> {
    match region.shape {
        super::void_region::Shape::Accessor | super::void_region::Shape::WidthRead => Some("u8"),
        super::void_region::Shape::ByteView => None,
    }
}

/// The base for a wrapper parameter that may carry a void region: the two
/// questions above asked together, so the WIRING is witnessed and not only the
/// pieces. The planner calls this and nothing else.
pub(crate) fn wrapper_base_for_region(
    parameter_name: &str,
    form: Form,
    void_pointee: bool,
    region: Option<&super::void_region::Region>,
) -> String {
    wrapper_base(
        parameter_name,
        form,
        void_pointee,
        region.and_then(delivered_element),
    )
}

/// Whether the raw parameter's pointee is `c_void` — the C ABI's untyped
/// region, which carries no element type of its own.
fn void_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let TyKind::RawPtr(pointee, _) = ty.kind() else {
        return false;
    };
    matches!(pointee.kind(), TyKind::Adt(definition, _)
        if tcx.lang_items().c_void() == Some(definition.did()))
}

pub(crate) fn plan(
    tcx: TyCtxt<'_>,
    exposure: &ExposurePolicy,
    table: &DecisionTable,
) -> (Vec<SurfaceArgumentPlan>, Vec<SurfaceArgumentFailure>) {
    let mut plans = Vec::new();
    let mut failures = Vec::new();
    for function in exposure.functions() {
        if !matches!(
            function.plan,
            ExposureSurfacePlan::PositiveSeedShim | ExposureSurfacePlan::FnPtrRawWrapper
        ) {
            continue;
        }
        let owner_class = SignatureClassId::of(function.did);
        let signature = tcx
            .fn_sig(function.did.to_def_id())
            .skip_binder()
            .skip_binder();
        let unsafe_fn = signature.safety.is_unsafe();
        for (subject, decision) in &table.entries {
            if subject.fn_did != function.did {
                continue;
            }
            let SubjectKind::Param {
                hir_index: parameter_index,
            } = subject.kind
            else {
                continue;
            };
            let form = match decision {
                Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
                    Form::Ref { mutable: *mutable }
                }
                Decision::Slice { mutable, .. } => Form::Slice { mutable: *mutable },
                Decision::Cursor { mutable, plan } if plan.wrapper && plan.parameter => {
                    if plan.optional {
                        Form::Opt {
                            mutable: *mutable,
                            slice: true,
                        }
                    } else {
                        Form::Slice { mutable: *mutable }
                    }
                }
                Decision::Opt { mutable, slice, .. } => Form::Opt {
                    mutable: *mutable,
                    slice: *slice,
                },
                Decision::Box(_)
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. }
                | Decision::Degraded(_) => continue,
            };
            let node = (subject.fn_did, subject.hir_id);
            let built = (|| -> Result<SurfaceArgumentPlan, &'static str> {
                let parameter_name = subject
                    .param_name
                    .clone()
                    .ok_or("surface-argument-name-unavailable")?;
                let original_type = *signature
                    .inputs()
                    .get(parameter_index)
                    .ok_or("surface-argument-input-position-unavailable")?;
                let TyKind::RawPtr(_, original_mutability) = *original_type.kind() else {
                    return Err("surface-argument-original-input-not-raw");
                };
                let mutable = match form {
                    Form::Ref { mutable } | Form::Slice { mutable } | Form::Opt { mutable, .. } => {
                        mutable
                    }
                    Form::NestedSlice { .. } => return Err("surface-argument-nested-unbuilt"),
                    Form::Cursor { .. } => return Err("surface-argument-cursor-unbuilt"),
                    Form::Raw => {
                        unreachable!("only admitted borrowed parameters reach the constructor")
                    }
                };
                if mutable && !original_mutability.is_mut() {
                    return Err("surface-argument-const-raw-to-mutable-unbuilt");
                }
                let Some((mut spec, _)) = seam::glue(form, Form::Raw, None)
                    .map_err(|_| "surface-argument-glue-unavailable")?
                else {
                    return Err("surface-argument-glue-absent");
                };
                if matches!(form, Form::Opt { slice: true, .. }) {
                    spec = spec.with_checked_binding_type(super::declaration::pointee_source(
                        tcx,
                        original_type,
                    ));
                }
                if spec.render_in_context(&parameter_name, unsafe_fn).is_none() {
                    return Err("surface-argument-render-unavailable");
                }
                let fallback = matches!(form, Form::Slice { .. } | Form::Opt { slice: true, .. });
                let unsafe_context = spec.requires_unsafe().then_some(UnsafeContextPresentation {
                    unsafe_fn,
                    wrapper_inserted: !unsafe_fn,
                    edition: 2018,
                    requires_unsafe: true,
                });
                let position = format!("generated-wrapper-arg{parameter_index}");
                let bridge = BridgeSitePlan {
                    caller: function.did,
                    callee: BridgeCalleeId::Local(function.did),
                    arm: Arm::Surface.key().into(),
                    position: position.clone(),
                    bridge_kind: "surface-unsafe-context-parameter".into(),
                    expected_form: form.key().into(),
                    found_form: Form::Raw.key().into(),
                    argument_kind: "generated-wrapper-argument".into(),
                    extent: if fallback {
                        BridgeExtentKind::Fallback
                    } else {
                        BridgeExtentKind::None
                    },
                    retention: BridgeRetentionTier::T1,
                    waiver_id: None,
                    unsafe_context,
                };
                let obligation = MechanicalObligationPlan {
                    planned: MechanicalObligationEvent {
                        key: MechanicalObligationKey {
                            owner_class,
                            subject: MechanicalSubjectKey::Local {
                                owner: subject.fn_did,
                                mir_local: subject.local.as_u32(),
                                slot_depth: 0,
                            },
                            site: CanonicalSiteKey {
                                owner: function.did,
                                location: CanonicalLocation::Generated {
                                    defining_class: owner_class,
                                    key: position,
                                },
                                callee: Some(CanonicalCallee::Generated {
                                    owner: function.did,
                                    key: "safe-inner".into(),
                                }),
                                argument_index: Some(
                                    u32::try_from(parameter_index)
                                        .map_err(|_| "surface-argument-index-overflow")?,
                                ),
                                slot_depth: 0,
                            },
                            family: MechanicalFamily::CallSiteNotAdapted,
                        },
                        owner_path: function.path.clone(),
                        prior_reason: MechanicalFamily::CallSiteNotAdapted.key().into(),
                        expected_form: form.key().into(),
                        found_form: Form::Raw.key().into(),
                        argument_kind: "generated-wrapper-argument".into(),
                        source_shape: "generated-wrapper-argument".into(),
                        required_arms: Arm::Surface.key().into(),
                        mechanism: MechanicalMechanism::RawParameterView,
                        composition_parent: None,
                        dependency_classes: BTreeSet::new(),
                        evidence: MechanicalEvidence {
                            extent: if fallback {
                                MechanicalExtent::Fallback {
                                    receipt: FALLBACK_EXTENT_RECEIPT.into(),
                                    waiver_id: SLICE_EXTENT_WAIVER_ID.into(),
                                }
                            } else {
                                MechanicalExtent::None
                            },
                            retention: MechanicalRetention::T1,
                            unsafe_context,
                            ..MechanicalEvidence::default()
                        },
                        stage: MechanicalStage::Plan,
                        state: MechanicalState::Planned,
                        terminal_reason: None,
                    },
                    intended_terminal_state: MechanicalState::Applied,
                    intended_terminal_reason: None,
                };
                let mut atom_ids = table
                    .seams
                    .raw_boundary_atom_groups
                    .get(&node)
                    .into_iter()
                    .flatten()
                    .map(|atom| atom.id.clone())
                    .collect::<Vec<_>>();
                atom_ids.sort();
                atom_ids.dedup();
                Ok(SurfaceArgumentPlan {
                    owner_class,
                    node,
                    parameter_index,
                    base: wrapper_base(
                        &parameter_name,
                        form,
                        void_pointee(tcx, original_type),
                        table
                            .void_region
                            .get(&node)
                            .map(|region| region.element.as_str()),
                    ),
                    parameter_name,
                    atom_ids,
                    form,
                    spec,
                    bridge,
                    obligation,
                })
            })();
            match built {
                Ok(plan) => plans.push(plan),
                Err(reason) => failures.push(SurfaceArgumentFailure {
                    owner_class,
                    node,
                    parameter_index,
                    reason,
                }),
            }
        }
    }
    plans.sort_by_key(|plan| (plan.owner_class.order_key(), plan.parameter_index));
    failures.sort_by_key(|failure| (failure.owner_class.order_key(), failure.parameter_index));
    (plans, failures)
}
