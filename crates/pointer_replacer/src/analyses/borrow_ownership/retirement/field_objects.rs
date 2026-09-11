//! R304-7 row (b): bounded field-object identity.
//!
//! `ObjectRoot::Field { base, field }` denotes *the object pointed to by the
//! pointer stored in field `field` of the object `base`*. `FieldBase` has no
//! field variant, so the field path is exactly one step: the wave-1 bound is
//! enforced by the type rather than by a length check, and interning is not
//! needed to keep `ObjectRoot` `Copy`. A deeper path, an aggregate element, or
//! any base that is not a single known root simply mints nothing and the load
//! stays Unknown, exactly as before this row.
//!
//! The root names the object that was in that cell AT THE LOAD, so every write
//! that may reach the cell must kill it. Two writers exist:
//!
//!   * a store to a projected place, which already raises `unknown` on the
//!     whole state (`objects::write`), covering every field store; and
//!   * a callee-scoped clobber, where wave 1 has no reachability relation
//!     between a callee and a base object and therefore kills every field root
//!     (`names_field` below). Row (a)'s own preservation is unaffected: the
//!     cell keeps its pointer VALUE, it just stops being exact evidence.

use rustc_middle::mir::{Local, Location};
use rustc_span::def_id::LocalDefId;

use super::objects::{ObjectRoot, ObjectSet};
use crate::analyses::borrow_ownership::export::ProjKey;

/// The base object of a field root. Deliberately carries no field variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FieldBase {
    Input {
        function: LocalDefId,
        parameter: Local,
        depth: u8,
    },
    Fresh {
        frame: LocalDefId,
        site: Location,
    },
    Stack {
        function: LocalDefId,
        local: Local,
    },
}

impl FieldBase {
    /// `None` for a root that is itself a field root: that is the bound.
    pub(crate) fn of(root: ObjectRoot) -> Option<Self> {
        match root {
            ObjectRoot::Input {
                function,
                parameter,
                depth,
            } => Some(Self::Input {
                function,
                parameter,
                depth,
            }),
            ObjectRoot::Fresh { frame, site } => Some(Self::Fresh { frame, site }),
            ObjectRoot::Stack { function, local } => Some(Self::Stack { function, local }),
            ObjectRoot::Field { .. } => None,
        }
    }
}

/// `Some((base_depth, field))` exactly when this place is a bounded field load:
/// one or more `Deref`s, then one `Field`, then nothing, with no extra depth
/// asked for. `base_depth` is the depth of the CONTAINING object.
pub(crate) fn field_step(proj: &[ProjKey], extra_depth: u8) -> Option<(usize, u32)> {
    if extra_depth != 0 {
        return None;
    }
    let (last, head) = proj.split_last()?;
    let ProjKey::Field(field) = *last else {
        return None;
    };
    if head.is_empty()
        || !head
            .iter()
            .all(|projection| matches!(projection, ProjKey::Deref))
    {
        return None;
    }
    Some((head.len() - 1, field))
}

/// Mint the bounded root for a field load out of its containing object. A MAY
/// base is never named: only a single known root yields identity.
pub(crate) fn mint(base: &ObjectSet, field: u32) -> ObjectSet {
    if base.unknown {
        return ObjectSet::default();
    }
    let mut roots = base.roots.iter();
    let (Some(&root), None) = (roots.next(), roots.next()) else {
        return ObjectSet::default();
    };
    match FieldBase::of(root) {
        Some(base) => ObjectSet::root(ObjectRoot::Field { base, field }),
        None => ObjectSet::default(),
    }
}

/// True when this set names a field object, i.e. depends on a field cell whose
/// content a writer may replace.
pub(crate) fn names_field(objects: &ObjectSet) -> bool {
    objects
        .roots
        .iter()
        .any(|root| matches!(root, ObjectRoot::Field { .. }))
}
