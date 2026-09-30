//! **wave-6l relay 071 (R697-7): the field-carried allocation length.**
//!
//! A struct's pointer field `P` whose every non-null write is an allocation
//! plus a literal offset, made in a function that also writes an integer field
//! `C` of the same object so that the allocation's elements past the offset
//! are `C + k`, holds `C + k` elements wherever it is read (brotli's
//! `RingBufferInitBuffer`: `data_ = alloc(2 + buflen + 7)`, `cur_size_ =
//! buflen`, `buffer_ = data_ + 2`, so `buffer_` holds `cur_size_ + 7`). The
//! seam renders that length where a construction's argument is `P` read from
//! an object (receipted `len-field-alloc`), before the fallback.

use rustc_hir::{Expr, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

/// One licence: `(*x).pointer` holds `(*x).length + slack` elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Licence {
    pub(crate) strukt: String,
    pub(crate) pointer: String,
    pub(crate) length: String,
    pub(crate) slack: u128,
}

/// Every licence of the program, and the functions that may write a licensed
/// field (directly or through a call).
#[derive(Default)]
pub(crate) struct Licences {
    pub(crate) licences: Vec<Licence>,
}

impl Licences {
    pub(crate) fn infer(_tcx: TyCtxt<'_>) -> Self {
        Self::default()
    }

    /// The rendered length of the argument `arg` of a call in `caller`, when
    /// it is a licensed field read (directly, or through a local defined only
    /// from one).
    pub(crate) fn length_of(
        &self,
        _tcx: TyCtxt<'_>,
        _caller: LocalDefId,
        _arg: &Expr<'_>,
    ) -> Option<String> {
        None
    }
}
