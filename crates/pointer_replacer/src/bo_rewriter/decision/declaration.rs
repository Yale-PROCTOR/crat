//! Compiler-resolved pointees for alias-spelled declarations. The binding's
//! own type supplies this carrier; no call target or model result is consulted.

use rustc_hash::FxHashMap;
use rustc_hir::{
    HirId, Node,
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{
    ConstKind, GenericArg, GenericArgKind, Ty, TyCtxt, TyKind,
    print::{CratePrefixGuard, NoTrimmedGuard},
};

use super::{Decision, DeclShape, Subject};

pub(crate) type DeclarationPointees = FxHashMap<(LocalDefId, HirId), ResolvedPointee>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResolvedPointee {
    pub(crate) original_alias: String,
    pub(crate) input_type: String,
    pub(crate) pointee: String,
}

pub(crate) fn collect(tcx: TyCtxt<'_>, subjects: &[Subject]) -> DeclarationPointees {
    let mut pointees = DeclarationPointees::default();
    for subject in subjects {
        if subject.decl_shape != DeclShape::Alias {
            continue;
        }
        let Some(span) = subject.ty_span else { continue };
        let Ok(original_alias) = tcx.sess.source_map().span_to_snippet(span) else { continue };
        let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { continue };
        let input_type = tcx.typeck(subject.fn_did).pat_ty(pattern);
        let TyKind::RawPtr(pointee, _) = input_type.kind() else { continue };
        if !pointee_is_nameable(tcx, subject.fn_did, *pointee) {
            continue;
        }
        pointees.insert(
            (subject.fn_did, subject.hir_id),
            ResolvedPointee {
                original_alias,
                input_type: pointee_source(tcx, input_type),
                pointee: pointee_source(tcx, *pointee),
            },
        );
    }
    pointees
}

fn definition_path_is_accessible(tcx: TyCtxt<'_>, owner: LocalDefId, definition: DefId) -> bool {
    if tcx.lang_items().c_void() == Some(definition) {
        return true; // rendered through its public core::ffi spelling
    }
    if !tcx
        .visibility(definition)
        .is_accessible_from(owner.to_def_id(), tcx)
    {
        return false;
    }
    let mut next = tcx.opt_parent(definition);
    while let Some(parent) = next {
        next = tcx.opt_parent(parent);
        if next.is_none() {
            break; // the crate root adds no private path component
        }
        match tcx.def_kind(parent) {
            DefKind::Mod => {
                if !tcx
                    .visibility(parent)
                    .is_accessible_from(owner.to_def_id(), tcx)
                {
                    return false;
                }
            }
            DefKind::ForeignMod => {} // an extern block adds no source path segment
            // Function/impl-local definitions have no supported absolute type
            // path here. Do not guess an unqualified name from their DefId.
            _ => return false,
        }
    }
    true
}

/// A sufficient nameability check before admitting an alias declaration.
/// Public reexports of inaccessible definition paths remain conservatively
/// outside this carrier; proving a different visible path is a separate step.
pub(crate) fn pointee_is_nameable<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    pointee: Ty<'tcx>,
) -> bool {
    let root: GenericArg<'tcx> = pointee.into();
    for argument in root.walk() {
        let ty = match argument.kind() {
            GenericArgKind::Type(ty) => ty,
            GenericArgKind::Lifetime(_) => continue,
            GenericArgKind::Const(value) => {
                if !matches!(value.kind(), ConstKind::Value(_) | ConstKind::Param(_)) {
                    return false;
                }
                continue;
            }
        };
        let definition = match ty.kind() {
            TyKind::Adt(definition, _) => Some(definition.did()),
            TyKind::Foreign(definition) => Some(*definition),
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never
            | TyKind::Param(_)
            | TyKind::RawPtr(..)
            | TyKind::Ref(..)
            | TyKind::Array(..)
            | TyKind::Slice(_)
            | TyKind::Tuple(_)
            | TyKind::FnPtr(..) => None,
            // Projections, opaque/inferred/bound types, closures and trait
            // objects need additional naming evidence, not a debug fallback.
            _ => return false,
        };
        if let Some(definition) = definition
            && !definition_path_is_accessible(tcx, owner, definition)
        {
            return false;
        }
    }
    true
}

/// Print compiler type structure with local paths rooted at `crate::` and all
/// generic arguments retained. Collection checks nameability before this
/// spelling can license a declaration; the printer itself grants no visibility.
pub(crate) fn pointee_source<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> String {
    if let TyKind::RawPtr(pointee, mutability) = ty.kind() {
        return format!(
            "*{} {}",
            if mutability.is_mut() { "mut" } else { "const" },
            pointee_source(tcx, *pointee)
        );
    }
    if let TyKind::Adt(definition, _) = ty.kind()
        && tcx.lang_items().c_void() == Some(definition.did())
    {
        return "core::ffi::c_void".to_owned();
    }
    let _crate_prefix = CratePrefixGuard::new();
    let _untrimmed = NoTrimmedGuard::new();
    ty.to_string()
}

/// Render only the borrowed forms licensed for the declaration family. The
/// source pointee is already resolved, and lifetime selection remains owned
/// by the existing lifetime planner.
pub(crate) fn emitted_type(
    decision: &Decision,
    pointee: &str,
    lifetime: Option<&str>,
) -> Option<String> {
    let (mutable, slice, optional) = match decision {
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
            (*mutable, false, false)
        }
        Decision::Slice { mutable, .. } => (*mutable, true, false),
        Decision::Opt { mutable, slice, .. } => (*mutable, *slice, true),
        Decision::Box(_) | Decision::Degraded(_) => return None,
    };
    let pointee = if slice {
        format!("[{pointee}]")
    } else {
        pointee.to_owned()
    };
    let lifetime = lifetime.map_or_else(String::new, |name| {
        format!("'{} ", name.trim_start_matches('\''))
    });
    let borrowed = format!("&{lifetime}{}{pointee}", if mutable { "mut " } else { "" });
    Some(if optional {
        format!("Option<{borrowed}>")
    } else {
        borrowed
    })
}
