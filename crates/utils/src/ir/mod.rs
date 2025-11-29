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
        && let hir_e = ast_to_hir.get_expr(call.receiver.id, tcx).unwrap()
        && let typeck = tcx.typeck(hir_e.hir_id.owner)
        && let ty = typeck.expr_ty(hir_e).peel_refs()
        && let ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) = ty.kind()
    {
        Some((&call.receiver, *ty))
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

pub fn format_mir_ty<'tcx, W: std::fmt::Write>(
    out: &mut W,
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> std::fmt::Result {
    use ty::*;
    match ty.kind() {
        TyKind::Bool => write!(out, "bool"),
        TyKind::Char => write!(out, "char"),
        TyKind::Int(IntTy::Isize) => write!(out, "isize"),
        TyKind::Int(IntTy::I8) => write!(out, "i8"),
        TyKind::Int(IntTy::I16) => write!(out, "i16"),
        TyKind::Int(IntTy::I32) => write!(out, "i32"),
        TyKind::Int(IntTy::I64) => write!(out, "i64"),
        TyKind::Int(IntTy::I128) => write!(out, "i128"),
        TyKind::Uint(UintTy::Usize) => write!(out, "usize"),
        TyKind::Uint(UintTy::U8) => write!(out, "u8"),
        TyKind::Uint(UintTy::U16) => write!(out, "u16"),
        TyKind::Uint(UintTy::U32) => write!(out, "u32"),
        TyKind::Uint(UintTy::U64) => write!(out, "u64"),
        TyKind::Uint(UintTy::U128) => write!(out, "u128"),
        TyKind::Float(FloatTy::F16) => write!(out, "f16"),
        TyKind::Float(FloatTy::F32) => write!(out, "f32"),
        TyKind::Float(FloatTy::F64) => write!(out, "f64"),
        TyKind::Float(FloatTy::F128) => write!(out, "f128"),
        TyKind::Adt(adt_def, args) => {
            let path_str = tcx.def_path_str(adt_def.did());
            if path_str.starts_with("std") {
                let name = tcx.item_name(adt_def.did());
                let name = name.as_str();
                if name == "Option"
                    || name == "Result"
                    || name == "Vec"
                    || name == "String"
                    || name == "Box"
                {
                    write!(out, "{name}",)?;
                } else {
                    write!(out, "{path_str}",)?;
                }
            } else {
                write!(out, "crate::{}", tcx.def_path_str(adt_def.did()))?;
            }
            if !args.is_empty() {
                write!(out, "<")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(out, ", ")?;
                    }
                    match arg.kind() {
                        GenericArgKind::Type(ty) => format_mir_ty(out, ty, tcx)?,
                        GenericArgKind::Const(cnst) => write!(out, "{cnst}")?,
                        GenericArgKind::Lifetime(_) => write!(out, "'_")?,
                    }
                }
                write!(out, ">")?;
            }
            Ok(())
        }
        TyKind::Foreign(def_id) => write!(out, "crate::{}", tcx.def_path_str(*def_id)),
        TyKind::Str => write!(out, "str"),
        TyKind::Array(ty, cnst) => {
            write!(out, "[")?;
            format_mir_ty(out, *ty, tcx)?;
            write!(out, "; {cnst}]")
        }
        TyKind::Pat(..) => todo!(),
        TyKind::Slice(ty) => {
            write!(out, "[")?;
            format_mir_ty(out, *ty, tcx)?;
            write!(out, "]")
        }
        TyKind::RawPtr(ty, mutability) => {
            let m = match mutability {
                Mutability::Mut => "mut",
                Mutability::Not => "const",
            };
            write!(out, "*{m} ")?;
            format_mir_ty(out, *ty, tcx)
        }
        TyKind::Ref(_, ty, mutability) => {
            write!(out, "&")?;
            if *mutability == Mutability::Mut {
                write!(out, "mut ")?;
            }
            format_mir_ty(out, *ty, tcx)
        }
        TyKind::FnDef(..) => todo!(),
        TyKind::FnPtr(ty_binder, header) => {
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
                format_mir_ty(out, *arg_ty, tcx)?;
            }
            if header.c_variadic {
                if !ty.inputs().is_empty() {
                    write!(out, ", ")?;
                }
                write!(out, "...")?;
            }
            write!(out, ") -> ")?;
            format_mir_ty(out, ty.output(), tcx)
        }
        TyKind::UnsafeBinder(..) => todo!(),
        TyKind::Dynamic(..) => todo!(),
        TyKind::Closure(..) => todo!(),
        TyKind::CoroutineClosure(..) => todo!(),
        TyKind::Coroutine(..) => todo!(),
        TyKind::CoroutineWitness(..) => todo!(),
        TyKind::Never => todo!(),
        TyKind::Tuple(tys) => {
            write!(out, "(")?;
            for (i, ty) in tys.iter().enumerate() {
                if i > 0 {
                    write!(out, ", ")?;
                }
                format_mir_ty(out, ty, tcx)?;
            }
            write!(out, ")")
        }
        TyKind::Alias(..) => todo!(),
        TyKind::Param(..) => todo!(),
        TyKind::Bound(..) => todo!(),
        TyKind::Placeholder(..) => todo!(),
        TyKind::Infer(..) => todo!(),
        TyKind::Error(..) => panic!(),
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
