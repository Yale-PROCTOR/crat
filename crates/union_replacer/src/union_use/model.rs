use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArgEffectKind {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArgEffect {
    pub arg_index: usize,
    pub kind: ArgEffectKind,
    /// Number of implicit dereferences before applying the effect.
    /// 0 means the argument place itself, 1 means pointee, etc.
    pub deref_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RetAlias {
    Arg(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FnModel {
    /// Effects over pointee memory of arguments.
    pub arg_effects: &'static [ArgEffect],
    /// Return value alias relation.
    pub ret_alias: Option<RetAlias>,
}

const MEMCPY_EFFECTS: [ArgEffect; 2] = [
    ArgEffect {
        arg_index: 0,
        kind: ArgEffectKind::Write,
        deref_count: 1,
    },
    ArgEffect {
        arg_index: 1,
        kind: ArgEffectKind::Read,
        deref_count: 1,
    },
];

const MEMCPY_MODEL: FnModel = FnModel {
    arg_effects: &MEMCPY_EFFECTS,
    ret_alias: Some(RetAlias::Arg(0)),
};

/// Return a modeled summary for known external/library functions.
///
/// Current coverage:
/// - memcpy
pub fn lookup_fn_model(tcx: TyCtxt<'_>, callee: DefId) -> Option<FnModel> {
    let name: Vec<_> = tcx
        .def_path(callee)
        .data
        .into_iter()
        .map(|data| data.to_string())
        .collect();

    let seg = |i: usize| name.get(i).map(|s| s.as_str()).unwrap_or_default();
    let name = (seg(0), seg(1), seg(2), seg(3));
    match name {
        (_, _, _, "memcpy") => Some(MEMCPY_MODEL),
        _ => None,
    }
}
