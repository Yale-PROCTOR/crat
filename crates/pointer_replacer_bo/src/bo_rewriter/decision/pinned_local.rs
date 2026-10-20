//! W-C3: a pinned signature gates its signature, not its locals.
//!
//! `facts.referenced` records HOW a function is referenced; a fn-pointer cast
//! or an address-taking use pins the function's SIGNATURE (`RefKind::pins`),
//! and `decide_one` degrades the owner's subjects `call-site-not-adapted`. A
//! named local's type is not part of the signature: it is declared and used
//! inside the body, and every seam it meets (a raw parameter it loads from, a
//! raw return it flows into, a raw callee it is passed to) is gated by that
//! seam's own facts exactly as in an unpinned function. Only parameters keep
//! the pin.
use super::{Subject, SubjectKind};

/// `true` when the pinned-signature gate does not apply to `subject`.
pub(crate) fn exempt(subject: &Subject) -> bool {
    matches!(subject.kind, SubjectKind::Local)
}
