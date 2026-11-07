use rustc_middle::{
    mir::{Operand, Place, Terminator, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
    source_map::Spanned,
};
use rustc_type_ir::TyKind::FnDef;

pub struct MirFunctionCall<'call, 'tcx> {
    pub func: CallKind,
    pub args: &'call [Spanned<Operand<'tcx>>],
    pub destination: Place<'tcx>,
}

pub trait TerminatorExt<'tcx> {
    fn as_call<'a>(&'a self, tcx: TyCtxt<'tcx>) -> Option<MirFunctionCall<'a, 'tcx>>;
}

impl<'tcx> TerminatorExt<'tcx> for Terminator<'tcx> {
    fn as_call<'a>(&'a self, tcx: TyCtxt<'tcx>) -> Option<MirFunctionCall<'a, 'tcx>> {
        match &self.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => Some(MirFunctionCall {
                func: CallKind::new(tcx, func),
                args,
                destination: *destination,
            }),
            TerminatorKind::TailCall { func, args, .. } => Some(MirFunctionCall {
                func: CallKind::new(tcx, func),
                args,
                destination: Place::return_place(),
            }),
            _ => None,
        }
    }
}

pub enum CallKind {
    FreeStanding(LocalDefId),
    /// Foreign C functions, identified by their linker symbol.
    LibC(Symbol),
    /// Library calls mostly come from _stdlib_
    RustLib(DefId),
    Impl(LocalDefId),
    Closure,
    Dynamic,
}

pub fn foreign_c_symbol(tcx: TyCtxt<'_>, callee: DefId) -> Option<Symbol> {
    (tcx.is_foreign_item(callee)
        && matches!(
            tcx.fn_sig(callee)
                .instantiate_identity()
                .skip_binder()
                .abi
                .name(),
            "C" | "C-unwind" | "system" | "system-unwind"
        ))
    .then(|| {
        tcx.codegen_fn_attrs(callee)
            .link_name
            .unwrap_or_else(|| tcx.item_name(callee))
    })
}

impl CallKind {
    pub fn new<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> CallKind {
        if let Some(func) = func.constant() {
            let ty = func.ty();
            let &FnDef(callee, _) = ty.kind() else { unreachable!() };

            if let Some(symbol) = foreign_c_symbol(tcx, callee) {
                return CallKind::LibC(symbol);
            }

            if let Some(local_did) = callee.as_local() {
                match tcx.hir_node_by_def_id(local_did) {
                    rustc_hir::Node::Item(_) => CallKind::FreeStanding(local_did),
                    rustc_hir::Node::ForeignItem(_) => CallKind::RustLib(callee),
                    rustc_hir::Node::ImplItem(_) => CallKind::Impl(local_did),
                    rustc_hir::Node::TraitItem(_) => CallKind::Dynamic,
                    _ => unreachable!(),
                }
            } else {
                CallKind::RustLib(callee)
            }
        } else {
            CallKind::Closure
        }
    }

    pub fn did(&self) -> Option<DefId> {
        match self {
            CallKind::FreeStanding(def_id) => Some(def_id.to_def_id()),
            CallKind::LibC(_) => None,
            CallKind::RustLib(def_id) => Some(*def_id),
            CallKind::Impl(def_id) => Some(def_id.to_def_id()),
            CallKind::Closure => None,
            CallKind::Dynamic => None,
        }
    }
}
