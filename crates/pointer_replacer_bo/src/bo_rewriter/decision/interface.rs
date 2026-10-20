//! Original compiler-observed pointer interfaces. These forms precede every
//! family profile and contain no decision, placement, model or retention facts.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, Node, def_id::LocalDefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{Subject, seam::Form};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct InputInterfaces {
    pub(crate) subject_forms: FxHashMap<(LocalDefId, HirId), Form>,
    /// Signature argument positions are zero-based, including any receiver.
    pub(crate) parameter_forms: FxHashMap<(LocalDefId, usize), Form>,
    pub(crate) return_forms: FxHashMap<LocalDefId, Form>,
}

fn observed_form(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<Form> {
    match ty.kind() {
        TyKind::RawPtr(..) => Some(Form::Raw),
        TyKind::Ref(_, pointee, mutability) => {
            let mutable = mutability.is_mut();
            Some(if matches!(pointee.kind(), TyKind::Slice(_)) {
                Form::Slice { mutable }
            } else {
                Form::Ref { mutable }
            })
        }
        TyKind::Adt(definition, arguments)
            if tcx.lang_items().option_type() == Some(definition.did()) =>
        {
            let payload = arguments.get(0)?.as_type()?;
            let TyKind::Ref(_, pointee, mutability) = payload.kind() else { return None };
            Some(Form::Opt {
                mutable: mutability.is_mut(),
                slice: matches!(pointee.kind(), TyKind::Slice(_)),
            })
        }
        // A same-spelled user Option and optional raw/owning pointers are not
        // optional borrowed interfaces. An absent entry is not invented Raw.
        _ => None,
    }
}

pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    functions: &[LocalDefId],
) -> InputInterfaces {
    let mut interfaces = InputInterfaces::default();
    for subject in subjects {
        let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { continue };
        let ty = tcx.typeck(subject.fn_did).pat_ty(pattern);
        if let Some(form) = observed_form(tcx, ty) {
            interfaces
                .subject_forms
                .insert((subject.fn_did, subject.hir_id), form);
        }
    }
    // A function can have supported input/return types without contributing
    // any rewrite subject. Observe every supplied signature independently.
    for &function in functions {
        let signature = tcx.fn_sig(function).skip_binder().skip_binder();
        for (index, &ty) in signature.inputs().iter().enumerate() {
            if let Some(form) = observed_form(tcx, ty) {
                interfaces.parameter_forms.insert((function, index), form);
            }
        }
        if let Some(form) = observed_form(tcx, signature.output()) {
            interfaces.return_forms.insert(function, form);
        }
    }
    interfaces
}
