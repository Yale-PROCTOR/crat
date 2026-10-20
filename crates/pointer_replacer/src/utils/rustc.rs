use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::LocalDefId, sym};

/// [`RustProgram`] contains constructs we care about in the
/// Rust program. Right now, we only care about user defined
/// struct type and free-standing functions.
pub struct RustProgram<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub functions: Vec<LocalDefId>,
    pub structs: Vec<LocalDefId>,
}

/// a function is c-exposed if its rust item name or its `#[export_name]`
/// (c2rust emits this when the c symbol differs from the rust item name)
/// is in the cli-supplied c-visible symbol set
pub(crate) fn is_c_exposed_fn(
    tcx: TyCtxt<'_>,
    did: LocalDefId,
    c_exposed_fns: &FxHashSet<String>,
) -> bool {
    let name = tcx.item_name(did.to_def_id());
    c_exposed_fns.contains(name.as_str())
        || tcx
            .get_attrs(did.to_def_id(), sym::export_name)
            .any(|attr| {
                attr.value_str()
                    .is_some_and(|s| c_exposed_fns.contains(s.as_str()))
            })
}
