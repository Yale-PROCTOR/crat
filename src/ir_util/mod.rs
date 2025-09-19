//! utils for working with HIR and MIR

use rustc_hir::definitions::DefPathData;
use rustc_middle::{
    mir::{Body, TerminatorKind},
    query::IntoQueryParam,
    ty::TyCtxt,
};
use rustc_span::{Symbol, def_id::DefId};

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
pub fn with_tcx<R, F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> R>(f: F) -> R {
    rustc_middle::ty::tls::with_opt(|tcx| f(tcx.unwrap()))
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
