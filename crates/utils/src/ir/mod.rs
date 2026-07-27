//! utils for working with HIR and MIR

use rustc_ast as ast;
use rustc_hir::definitions::DefPathData;
use rustc_middle::{
    mir::{Body, TerminatorKind},
    query::IntoQueryParam,
    ty,
    ty::TyCtxt,
};
use rustc_span::{Symbol, def_id::DefId, sym};

#[inline]
pub fn def_id_to_symbol(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<Symbol> {
    let key = tcx.def_key(id);
    let (DefPathData::ValueNs(name) | DefPathData::TypeNs(name)) = key.disambiguated_data.data
    else {
        return None;
    };
    Some(name)
}

#[inline]
pub fn is_option(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    def_id_to_symbol(id, tcx).is_some_and(|name| name == sym::Option)
}

#[inline]
pub fn with_tcx<R, F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> R>(f: F) -> R {
    ty::tls::with_opt(|tcx| f(tcx.unwrap()))
}

pub fn ty_size<'tcx>(
    ty: ty::Ty<'tcx>,
    def_id: impl IntoQueryParam<DefId>,
    tcx: TyCtxt<'tcx>,
) -> u64 {
    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
    let layout = tcx.layout_of(typing_env.as_query_input(ty)).unwrap();
    layout.size.bytes()
}

pub fn array_of_as_ptr<'e, 'tcx>(
    e: &'e ast::Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<(&'e ast::Expr, ty::Ty<'tcx>)> {
    if let rustc_ast::ExprKind::MethodCall(call) = &crate::ast::unwrap_cast_and_paren(e).kind
        && let name = call.seg.ident.name.as_str()
        && (name == "as_mut_ptr" || name == "as_ptr")
        && let Some(hir_e) = ast_to_hir.get_expr(call.receiver.id, tcx)
    {
        let typeck = tcx.typeck(hir_e.hir_id.owner);
        let ty = typeck.expr_ty(hir_e).peel_refs();
        let ty = match ty.kind() {
            ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => *ty,
            ty::TyKind::Adt(adt_def, gargs) if tcx.item_name(adt_def.did()) == sym::Vec => {
                let ty::GenericArgKind::Type(ty) = gargs[0].kind() else { panic!() };
                ty
            }
            _ => return None,
        };
        Some((&call.receiver, ty))
    } else {
        None
    }
}

#[inline]
pub fn mir_ty_to_string<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    let mut buf = String::new();
    format_mir_ty(&mut buf, ty, tcx).unwrap();
    buf
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MirTypeFormatError {
    Formatting,
    Unsupported(String),
    Nominal(String),
}

impl From<std::fmt::Error> for MirTypeFormatError {
    fn from(_: std::fmt::Error) -> Self {
        Self::Formatting
    }
}

pub fn format_mir_ty<'tcx, W: std::fmt::Write>(
    out: &mut W,
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> std::fmt::Result {
    let mut nominal_path = |def_id| Ok(legacy_nominal_path(def_id, tcx));
    format_mir_ty_with_policy(out, ty, tcx, &mut nominal_path, MirTypeFormatPolicy::Legacy)
        .map_err(|_| std::fmt::Error)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirTypeFormatPolicy {
    Legacy,
    SourceValid,
}

pub fn format_mir_ty_with_policy<'tcx, W, F>(
    out: &mut W,
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    nominal_path: &mut F,
    policy: MirTypeFormatPolicy,
) -> Result<(), MirTypeFormatError>
where
    W: std::fmt::Write,
    F: FnMut(DefId) -> Result<String, MirTypeFormatError>,
{
    use ty::*;
    match ty.kind() {
        TyKind::Bool => write!(out, "bool").map_err(Into::into),
        TyKind::Char => write!(out, "char").map_err(Into::into),
        TyKind::Int(IntTy::Isize) => write!(out, "isize").map_err(Into::into),
        TyKind::Int(IntTy::I8) => write!(out, "i8").map_err(Into::into),
        TyKind::Int(IntTy::I16) => write!(out, "i16").map_err(Into::into),
        TyKind::Int(IntTy::I32) => write!(out, "i32").map_err(Into::into),
        TyKind::Int(IntTy::I64) => write!(out, "i64").map_err(Into::into),
        TyKind::Int(IntTy::I128) => write!(out, "i128").map_err(Into::into),
        TyKind::Uint(UintTy::Usize) => write!(out, "usize").map_err(Into::into),
        TyKind::Uint(UintTy::U8) => write!(out, "u8").map_err(Into::into),
        TyKind::Uint(UintTy::U16) => write!(out, "u16").map_err(Into::into),
        TyKind::Uint(UintTy::U32) => write!(out, "u32").map_err(Into::into),
        TyKind::Uint(UintTy::U64) => write!(out, "u64").map_err(Into::into),
        TyKind::Uint(UintTy::U128) => write!(out, "u128").map_err(Into::into),
        TyKind::Float(FloatTy::F16) => write!(out, "f16").map_err(Into::into),
        TyKind::Float(FloatTy::F32) => write!(out, "f32").map_err(Into::into),
        TyKind::Float(FloatTy::F64) => write!(out, "f64").map_err(Into::into),
        TyKind::Float(FloatTy::F128) => write!(out, "f128").map_err(Into::into),
        TyKind::Adt(adt_def, args) => {
            write!(out, "{}", nominal_path(adt_def.did())?)?;
            if !args.is_empty() {
                write!(out, "<")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(out, ", ")?;
                    }
                    match arg.kind() {
                        GenericArgKind::Type(ty) => {
                            format_mir_ty_with_policy(out, ty, tcx, nominal_path, policy)?
                        }
                        GenericArgKind::Const(cnst) => write!(out, "{cnst}")?,
                        GenericArgKind::Lifetime(region) => {
                            write_region(out, region, policy, false)?
                        }
                    }
                }
                write!(out, ">")?;
            }
            Ok(())
        }
        TyKind::Foreign(def_id) => write!(out, "{}", nominal_path(*def_id)?).map_err(Into::into),
        TyKind::Str => write!(out, "str").map_err(Into::into),
        TyKind::Array(ty, cnst) => {
            write!(out, "[")?;
            format_mir_ty_with_policy(out, *ty, tcx, nominal_path, policy)?;
            let cnst = tcx
                .try_normalize_erasing_regions(TypingEnv::fully_monomorphized(), *cnst)
                .unwrap_or(*cnst);
            if let Some(length) = cnst.try_to_target_usize(tcx) {
                write!(out, "; {length}]").map_err(Into::into)
            } else {
                write!(out, "; {cnst}]").map_err(Into::into)
            }
        }
        TyKind::Pat(..) => unsupported("pattern type"),
        TyKind::Slice(ty) => {
            write!(out, "[")?;
            format_mir_ty_with_policy(out, *ty, tcx, nominal_path, policy)?;
            write!(out, "]").map_err(Into::into)
        }
        TyKind::RawPtr(ty, mutability) => {
            let m = match mutability {
                Mutability::Mut => "mut",
                Mutability::Not => "const",
            };
            write!(out, "*{m} ")?;
            format_mir_ty_with_policy(out, *ty, tcx, nominal_path, policy)
        }
        TyKind::Ref(region, ty, mutability) => {
            write!(out, "&")?;
            if policy == MirTypeFormatPolicy::SourceValid {
                write_region(out, *region, policy, true)?;
                if !matches!(region.kind(), ty::RegionKind::ReErased) {
                    write!(out, " ")?;
                }
            }
            if *mutability == Mutability::Mut {
                write!(out, "mut ")?;
            }
            format_mir_ty_with_policy(out, *ty, tcx, nominal_path, policy)
        }
        TyKind::FnDef(..) => unsupported("function item type"),
        TyKind::FnPtr(ty_binder, header) => {
            if policy == MirTypeFormatPolicy::SourceValid && ty_binder.has_bound_vars() {
                return unsupported("higher-ranked function pointer binder");
            }
            if header.safety.is_unsafe() {
                write!(out, "unsafe ")?;
            }
            if !header.abi.is_rustic_abi() {
                write!(out, "extern \"{}\" ", header.abi.name())?;
            }

            write!(out, "fn")?;
            let ty = ty_binder.skip_binder();
            write!(out, "(")?;
            for (i, arg_ty) in ty.inputs().iter().enumerate() {
                if i > 0 {
                    write!(out, ", ")?;
                }
                format_mir_ty_with_policy(out, *arg_ty, tcx, nominal_path, policy)?;
            }
            if header.c_variadic {
                if !ty.inputs().is_empty() {
                    write!(out, ", ")?;
                }
                write!(out, "...")?;
            }
            write!(out, ") -> ")?;
            format_mir_ty_with_policy(out, ty.output(), tcx, nominal_path, policy)
        }
        TyKind::UnsafeBinder(..) => unsupported("unsafe binder"),
        TyKind::Dynamic(..) => unsupported("dynamic trait object"),
        TyKind::Closure(..) => unsupported("closure type"),
        TyKind::CoroutineClosure(..) => unsupported("coroutine closure type"),
        TyKind::Coroutine(..) => unsupported("coroutine type"),
        TyKind::CoroutineWitness(..) => unsupported("coroutine witness type"),
        TyKind::Never => write!(out, "!").map_err(Into::into),
        TyKind::Tuple(tys) => {
            write!(out, "(")?;
            for (i, ty) in tys.iter().enumerate() {
                if i > 0 {
                    write!(out, ", ")?;
                }
                format_mir_ty_with_policy(out, ty, tcx, nominal_path, policy)?;
            }
            if policy == MirTypeFormatPolicy::SourceValid && tys.len() == 1 {
                write!(out, ",")?;
            }
            write!(out, ")").map_err(Into::into)
        }
        TyKind::Alias(..) => unsupported("alias, projection, or opaque type"),
        TyKind::Param(..) => unsupported("type parameter"),
        TyKind::Bound(..) => unsupported("bound type"),
        TyKind::Placeholder(..) => unsupported("placeholder type"),
        TyKind::Infer(..) => unsupported("inference type"),
        TyKind::Error(..) => unsupported("error type"),
    }
}

fn legacy_nominal_path(def_id: DefId, tcx: TyCtxt<'_>) -> String {
    let path = tcx.def_path_str(def_id);
    if path.starts_with("std") {
        let item_name = tcx.item_name(def_id);
        let name = item_name.as_str();
        if matches!(name, "Option" | "Result" | "Vec" | "String" | "Box") {
            name.to_owned()
        } else {
            path
        }
    } else {
        format!("crate::{path}")
    }
}

fn unsupported<T>(shape: &str) -> Result<T, MirTypeFormatError> {
    Err(MirTypeFormatError::Unsupported(shape.to_owned()))
}

fn write_region<W: std::fmt::Write>(
    out: &mut W,
    region: ty::Region<'_>,
    policy: MirTypeFormatPolicy,
    elide_erased: bool,
) -> Result<(), MirTypeFormatError> {
    if policy == MirTypeFormatPolicy::Legacy {
        return write!(out, "'_").map_err(Into::into);
    }
    match region.kind() {
        ty::RegionKind::ReStatic => write!(out, "'static").map_err(Into::into),
        ty::RegionKind::ReEarlyParam(param) => write!(out, "'{}", param.name).map_err(Into::into),
        ty::RegionKind::ReLateParam(param) => match param.kind {
            ty::LateParamRegionKind::Named(_, name) => write!(out, "'{name}").map_err(Into::into),
            _ => unsupported("anonymous late-bound region"),
        },
        ty::RegionKind::ReErased if elide_erased => Ok(()),
        ty::RegionKind::ReErased => write!(out, "'_").map_err(Into::into),
        ty::RegionKind::ReBound(..) => unsupported("higher-ranked bound region"),
        ty::RegionKind::ReVar(..) => unsupported("inference region"),
        ty::RegionKind::RePlaceholder(..) => unsupported("placeholder region"),
        ty::RegionKind::ReError(..) => unsupported("error region"),
    }
}

#[inline]
pub fn fmt_def_id(
    f: &mut std::fmt::Formatter<'_>,
    key: impl IntoQueryParam<DefId>,
) -> std::fmt::Result {
    let def_id = key.into_query_param();
    rustc_middle::ty::tls::with_opt(|opt_tcx| {
        if let Some(tcx) = opt_tcx {
            write!(f, "{}", tcx.def_path_str(def_id))
        } else {
            write!(f, "{}", def_id.index.index())
        }
    })
}

pub fn body_to_str(body: &Body<'_>) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "{:?} {{", body.source.instance.def_id()).unwrap();
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        writeln!(s, "    {bb:?}:").unwrap();
        for stmt in &bbd.statements {
            writeln!(s, "        {stmt:?}").unwrap();
        }
        if !matches!(
            bbd.terminator().kind,
            TerminatorKind::Return | TerminatorKind::Assert { .. }
        ) {
            writeln!(s, "        {:?}", bbd.terminator().kind).unwrap();
        }
    }
    writeln!(s, "}}").unwrap();
    s
}

pub fn body_size(body: &Body<'_>) -> usize {
    body.basic_blocks
        .iter()
        .map(|bbd| bbd.statements.len() + 1)
        .sum()
}

pub mod ast_to_hir;
pub mod hir_to_thir;
pub mod thir_to_mir;

pub use ast_to_hir::*;
pub use hir_to_thir::*;
pub use thir_to_mir::*;

#[cfg(test)]
mod tests;
