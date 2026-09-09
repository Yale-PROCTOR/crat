//! Borrowed return presentations licensed by the existing native lifetime plan.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Decision, DecisionTable,
    emitability::EmitabilityFacts,
    lifetime::{FnSignatureSlot, LifetimeEligibility},
    seam::{Form, form_of},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnInterface {
    pub(crate) form: Form,
    pub(crate) pointee: String,
    pub(crate) lifetime: String,
    pub(crate) lifetime_plan_digest: String,
}

impl ReturnInterface {
    pub(crate) fn temporary_type(&self) -> String {
        let (mutable, slice, optional) = match self.form {
            Form::Raw => unreachable!("return lifetime plans contain borrowed interfaces"),
            Form::Ref { mutable } => (mutable, false, false),
            Form::Slice { mutable } => (mutable, true, false),
            Form::Opt { mutable, slice } => (mutable, slice, true),
        };
        let pointee = if slice {
            format!("[{}]", self.pointee)
        } else {
            self.pointee.clone()
        };
        let borrowed = format!("&{}{}", if mutable { "mut " } else { "" }, pointee);
        if optional {
            format!("Option<{borrowed}>")
        } else {
            borrowed
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ReturnInterfaces {
    pub(crate) functions: FxHashMap<LocalDefId, ReturnInterface>,
    pub(crate) failures: FxHashMap<LocalDefId, &'static str>,
}

pub(crate) fn plan(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    facts: &EmitabilityFacts,
    eligibility: &LifetimeEligibility,
    enabled_families: &FxHashSet<LocalDefId>,
) -> ReturnInterfaces {
    let mut result = ReturnInterfaces::default();
    let decisions = table
        .entries
        .iter()
        .map(|(s, d)| ((s.fn_did, s.hir_id), d))
        .collect::<FxHashMap<_, _>>();
    for (function, lifetime_plan) in table.lifetime_plan.functions() {
        let Some(lifetime) = lifetime_plan.lifetime_for(FnSignatureSlot::RETURN) else { continue };
        let signature = tcx.fn_sig(function).skip_binder().skip_binder();
        let TyKind::RawPtr(pointee, mutability) = *signature.output().kind() else { continue };
        let sites = facts
            .return_sites
            .iter()
            .filter(|site| site.owner == function)
            .collect::<Vec<_>>();
        let has_null = sites.iter().any(|site| site.source_shape == "null-lit");
        let new_family = enabled_families.contains(&function)
            && (has_null
                || sites.iter().filter_map(|site| site.root).any(|root| {
                    match decisions.get(&(function, root)) {
                        Some(Decision::Slice { .. } | Decision::Opt { .. }) => true,
                        Some(
                            Decision::Ref { .. }
                            | Decision::InferredRef { .. }
                            | Decision::Box(_)
                            | Decision::Degraded(_),
                        )
                        | None => false,
                    }
                }));
        let form = if new_family {
            let forms = sites
                .iter()
                // Null is the empty Option branch; it contributes no origin.
                // Every non-null branch still needs its real native permit.
                .filter(|site| site.source_shape != "null-lit")
                .map(|site| {
                    let node = (function, site.root?);
                    if eligibility.return_permit(node).is_none() {
                        return None;
                    }
                    let decision = decisions.get(&node)?;
                    let form = match decision {
                        Decision::Ref { .. }
                        | Decision::InferredRef { .. }
                        | Decision::Slice { .. }
                        | Decision::Opt { .. } => Some(form_of(decision)),
                        Decision::Box(_) | Decision::Degraded(_) => None,
                    }?;
                    let supported = match site.expression_shape {
                        super::emitability::ReturnExprShape::Other => site.source_shape == "bare-local",
                        super::emitability::ReturnExprShape::ConstantReslice { .. } =>
                            matches!(form, Form::Slice { .. }),
                    };
                    supported.then_some(form)
                })
                .collect::<Option<Vec<_>>>();
            let Some(forms) = forms else {
                result
                    .failures
                    .insert(function, "return-interface-unbuilt-source");
                continue;
            };
            let bases = forms
                .iter()
                .map(|form| match *form {
                    Form::Opt {
                        mutable,
                        slice: false,
                    } => Form::Ref { mutable },
                    Form::Opt {
                        mutable,
                        slice: true,
                    } => Form::Slice { mutable },
                    Form::Ref { .. } | Form::Slice { .. } | Form::Raw => *form,
                })
                .collect::<Vec<_>>();
            let Some(&base) = bases
                .first()
                .filter(|base| bases.iter().all(|other| other == *base))
            else {
                result
                    .failures
                    .insert(function, "return-interface-unbuilt-mixed-forms");
                continue;
            };
            let optional = has_null || forms.iter().any(|form| matches!(form, Form::Opt { .. }));
            if optional {
                match base {
                    Form::Ref { mutable } => Form::Opt {
                        mutable,
                        slice: false,
                    },
                    Form::Slice { mutable } => Form::Opt {
                        mutable,
                        slice: true,
                    },
                    Form::Raw | Form::Opt { .. } => {
                        result
                            .failures
                            .insert(function, "return-interface-unbuilt-raw-source");
                        continue;
                    }
                }
            } else {
                base
            }
        } else {
            // Preserve the established scalar return interface, including its
            // existing shared-to-mutable gate in seam synthesis.
            Form::Ref {
                mutable: mutability.is_mut(),
            }
        };
        result.functions.insert(
            function,
            ReturnInterface {
                form,
                pointee: super::declaration::pointee_source(tcx, pointee),
                lifetime: lifetime.to_owned(),
                lifetime_plan_digest: lifetime_plan.digest(),
            },
        );
    }
    result
}
