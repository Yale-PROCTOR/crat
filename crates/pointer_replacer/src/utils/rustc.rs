use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

/// [`RustProgram`] contains constructs we care about in the
/// Rust program. Right now, we only care about user defined
/// struct type and free-standing functions.
pub struct RustProgram<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub functions: Vec<LocalDefId>,
    pub structs: Vec<LocalDefId>,
}
