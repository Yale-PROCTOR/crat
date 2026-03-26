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
pub struct CopyEffect {
    pub dst_arg_index: usize,
    pub src_arg_index: usize,
    /// Number of implicit dereferences before applying the copy.
    /// 0 means the argument place itself, 1 means pointee, etc.
    pub deref_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FnModel {
    /// Effects over pointee memory of arguments.
    pub arg_effects: &'static [ArgEffect],
    /// Value-copy relations between arguments.
    pub copy_effects: &'static [CopyEffect],
    /// Return value alias relation.
    pub ret_alias: Option<RetAlias>,
}

macro_rules! read_effect {
    ($arg_index:expr, $deref_count:expr) => {
        ArgEffect {
            arg_index: $arg_index,
            kind: ArgEffectKind::Read,
            deref_count: $deref_count,
        }
    };
}

macro_rules! write_effect {
    ($arg_index:expr, $deref_count:expr) => {
        ArgEffect {
            arg_index: $arg_index,
            kind: ArgEffectKind::Write,
            deref_count: $deref_count,
        }
    };
}

macro_rules! copy_effect {
    ($dst_arg_index:expr, $src_arg_index:expr, $deref_count:expr) => {
        CopyEffect {
            dst_arg_index: $dst_arg_index,
            src_arg_index: $src_arg_index,
            deref_count: $deref_count,
        }
    };
}

/// Return a modeled summary for known external/library functions.
///
/// Notes:
/// - Effects are memory-level summaries over pointer arguments.
pub fn lookup_fn_model(tcx: TyCtxt<'_>, callee: DefId) -> Option<FnModel> {
    let path: Vec<_> = tcx
        .def_path(callee)
        .data
        .into_iter()
        .map(|data| data.to_string())
        .collect();

    let fn_name = path.last().map(|s| s.as_str()).unwrap_or_default();
    match fn_name {
        // memory/string primitives
        "memcpy" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[copy_effect!(0, 1, 1)],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "memset" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "memmove" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[copy_effect!(0, 1, 1)],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "memchr" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "memrchr" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "memcmp" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "strcmp" | "strncmp" | "strcasecmp" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "strlen" | "strnlen" | "strspn" | "strtol" | "strtoul" | "strtod" | "atoi" => {
            Some(FnModel {
                arg_effects: &[read_effect!(0, 1)],
                copy_effects: &[],
            ret_alias: None,
            })
        }
        "strstr" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "strcpy" | "strncpy" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "snprintf" | "vsnprintf" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(2, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "strchr" | "strrchr" | "strchrnul" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "strerror_r" => Some(FnModel {
            arg_effects: &[write_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "strdup" | "strndup" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "strcat" | "strncat" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: Some(RetAlias::Arg(0)),
        }),
        "strtok_r" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), read_effect!(1, 1), write_effect!(2, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "sprintf" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "sscanf" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),

        // i/o
        "read" | "tape_buffered_read" => Some(FnModel {
            arg_effects: &[write_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "write" | "tape_buffered_write" => Some(FnModel {
            arg_effects: &[read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "fread" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "fwrite" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "readlink" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), write_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),

        // others
        "htable_insert" => Some(FnModel {
            arg_effects: &[write_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "htable_find" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), read_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "qsort" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), write_effect!(0, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        "to_ascii" | "from_ascii" => Some(FnModel {
            arg_effects: &[read_effect!(0, 1), write_effect!(1, 1)],
            copy_effects: &[],
            ret_alias: None,
        }),
        _ => None,
    }
}
