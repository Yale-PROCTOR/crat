//! Thin references at multi-element LOCAL callee positions (seat addendum 364,
//! R364-2; adjudicated R365-1/2).
//!
//! [`super::thin_extent`] holds a thin `&T` that reaches a FOREIGN position
//! whose pinned contract consumes more than one element. Its own "not held"
//! list ends at local callees, on the ground that "a local callee's parameter
//! is a subject in its own right" — which is true of the CALLEE's slot and says
//! nothing about the caller's extent. [`super::void_pointee`] holds the
//! callee's `c_void` parameter and says of the other end that the caller then
//! "takes the ordinary raw-boundary bridge, whose pointer carries the caller
//! subject's own full extent". Both statements are true, and together they
//! leave exactly one hole: when the caller's subject is ITSELF thin, its "own
//! full extent" is one element, and a callee that accesses wider walks off it.
//!
//! brotli is the witness in both directions. `Hash14(data: &uint8_t)` bridges
//! into `BrotliUnalignedRead32(p: *const c_void)`, whose body is
//! `*(p as *const uint32_t)` — four bytes through a one-byte claim — and
//! `BrotliStoreMetaBlockHeader(storage: &mut uint8_t)` bridges into
//! `BrotliWriteBits(array: *mut uint8_t)`, which offsets and then calls
//! `BrotliUnalignedWrite64`: an EIGHT-byte WRITE. The class is therefore not a
//! read-extent class, which is why the hold names the ACCESS.
//!
//! **The predicate asks only "does this callee parameter access more than one
//! element", never "how many bytes versus how many".** That is the same shape
//! as both neighbours — `thin_extent` asks whether the contract's extent fits
//! one element, `void_pointee` asks whether the pointee is `c_void` — and it
//! needs no width arithmetic to be sound:
//!
//! - a `c_void` pointee carries no extent at all (R271-1), so the cast the
//!   callee performs to reach its real type is an access of unbounded width by
//!   that rule's own reasoning. The cast target is recorded in the receipt
//!   because it is the useful thing to read, not because the rule needs it;
//! - pointer arithmetic leaves a one-element claim by construction, whatever
//!   the element is.
//!
//! What is deliberately NOT held:
//!
//! - **`RawExpr` arguments.** `f(((*s).string_table.arr).offset(..))` roots at
//!   `s` under [`ArgShape::place_root`], but the pointer passed was READ OUT OF
//!   the referent and carries its own provenance; `s`'s extent does not bound
//!   it. Holding `s` would be holding on the wrong subject. Only shapes in
//!   which the argument DENOTES the subject — a bare binding, or that binding
//!   under casts — are in the class. The corpus sizing separated exactly three
//!   rows this way (one libtree, two lodepng).
//! - **`AddrOf` arguments.** `f(&mut p)` passes the ADDRESS of the subject
//!   binding, so the extent question belongs to the outer pointer, at depth 2.
//! - **`is_null` and the other observing raw-only uses.** They read the address
//!   and access nothing past it.
//! - **Slice-typed callee parameters.** A `&[T]` parameter carries its own
//!   checked extent; how that slice was CONSTRUCTED is the
//!   `FALLBACK_SLICE_EXTENT` waiver, receipted per site and out of scope by the
//!   2026-08-30 ruling (R365-2 keeps these 21 corpus rows a census item, not a
//!   hold).
//! - **Foreign callees.** They are [`super::thin_extent`]'s, decided by the
//!   pinned contract table so the classification stays in one place.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, Node, def_id::LocalDefId};
use rustc_middle::ty::{Mutability, TyCtxt, TyKind};

use super::{
    Subject, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts, SliceUses},
    void_pointee::{VOID_POINTEE_DEPTH, has_void_pointee},
};

/// Pointer arithmetic leaves a one-element claim by construction.
///
/// `is_null` and the other members of `RAW_ONLY_METHODS` observe the address
/// without accessing past it, so they are deliberately absent.
const EXTENT_LEAVING_OPS: &[&str] = &[
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
];

/// Why one local callee parameter accesses more than one element.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AccessReason {
    /// The parameter's own pointee is `c_void` and the body casts it away to
    /// the type it actually wants. Carries that cast target, for the receipt.
    VoidPointee { cast_to: String },
    /// The body offsets or indexes the parameter.
    PointerArithmetic { op: String },
    /// The parameter accesses nothing itself and hands the pointer, bare, to
    /// a callee parameter that does (W-C9, fix-2 one call deeper: a thin
    /// caller bridged into the forwarder reads wide through a one-element
    /// claim exactly as it would at the accessing callee). Carries that
    /// parameter's own detail.
    Forwarded { into: String },
}

impl AccessReason {
    fn key(&self) -> String {
        match self {
            Self::VoidPointee { cast_to } => format!("void-pointee-cast-to:{cast_to}"),
            Self::PointerArithmetic { op } => format!("pointer-arithmetic:{op}"),
            Self::Forwarded { into } => format!("forwarded-into:{into}"),
        }
    }
}

/// The typed hold: which callee, which parameter, read or write, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalCalleeAccess {
    pub(crate) callee_id: LocalDefId,
    pub(crate) parameter_index: usize,
    pub callee: String,
    pub parameter: String,
    /// `read` or `write`, from the callee parameter's own pointee mutability.
    /// Six of the twenty corpus sites are writes; a class named for reads would
    /// have mis-described them.
    pub access: &'static str,
    pub reason: AccessReason,
}

impl LocalCalleeAccess {
    /// `callee:parameter:access:reason` — the four things R365-1 requires.
    pub(crate) fn detail(&self) -> String {
        format!(
            "{}:{}:{}:{}",
            self.callee,
            self.parameter,
            self.access,
            self.reason.key()
        )
    }
}

/// Does this argument expression DENOTE the subject, so that the pointer handed
/// over is a view of the subject's own referent?
///
/// See the module note: `RawExpr` and `AddrOf` are excluded, and for reasons
/// that differ, so they are matched out explicitly rather than by falling
/// through [`ArgShape::place_root`].
fn subject_denoting_root(shape: ArgShape) -> Option<HirId> {
    match shape {
        ArgShape::BareLocal(id) | ArgShape::CastOfLocal { binding: id, .. } => Some(id),
        _ => None,
    }
}

/// How the callee's body accesses this parameter, if it accesses past one
/// element at all.
fn parameter_access(
    tcx: TyCtxt<'_>,
    param: &Subject,
    facts: &EmitabilityFacts,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
    parameters: &FxHashMap<(LocalDefId, usize), &Subject>,
    visited: &mut Vec<(LocalDefId, HirId)>,
) -> Option<LocalCalleeAccess> {
    let Node::Pat(pattern) = tcx.hir_node(param.hir_id) else {
        return None;
    };
    // **R365-2 — a slice-shaped callee parameter is out of the class.** Read
    // before anything else, because the arithmetic arm below would otherwise
    // claim exactly these: at decision time the parameter is still raw and its
    // uses are still `*p.offset(e)`, and the whole point of a slice candidate
    // is that every one of those becomes a CHECKED index on a form carrying its
    // own extent. What stays open for them is how the slice was CONSTRUCTED,
    // which is the `FALLBACK_SLICE_EXTENT` waiver, receipted per site and
    // ruled a census item rather than a hold. (W-C9 report 017 sizes the
    // THIN-caller side of this exclusion — `from_ref` into a wide reader —
    // for the seat; it is not moved here.)
    if slice_uses
        .get(&(param.fn_did, param.hir_id))
        .is_some_and(|uses| {
            uses.unsupported.is_none()
                && !uses.rewrites.is_empty()
                && !super::slice_return_evidence::needs_full_base(tcx, param, uses)
        })
    {
        return None;
    }
    let ty = tcx.typeck(param.fn_did).pat_ty(pattern);
    let key = (param.fn_did, param.hir_id);
    let reason = if has_void_pointee(tcx, ty, VOID_POINTEE_DEPTH) {
        // A `c_void` parameter is held on its own account by R271-1; what puts
        // the CALLER in this class is the cast that follows, which is the
        // evidence that the opaque address is accessed at some real width. A
        // `c_void` parameter that is only passed on or compared accesses
        // nothing and is not in scope.
        let cast = facts.address_observations.iter().find(|fact| {
            fact.op == "ptr-cast" && fact.operands.iter().any(|operand| operand.node == key)
        })?;
        AccessReason::VoidPointee {
            cast_to: cast.target_type.clone(),
        }
    } else if let Some((op, _)) = facts.raw_only_uses.get(&key).and_then(|uses| {
        uses.iter()
            .find(|(op, _)| EXTENT_LEAVING_OPS.contains(&op.as_str()))
    }) {
        AccessReason::PointerArithmetic { op: op.clone() }
    } else {
        // No access of its own: the first callee parameter it is handed to,
        // bare, that accesses wide (a cycle accesses nothing).
        if visited.contains(&key) {
            return None;
        }
        visited.push(key);
        let into = facts
            .call_args
            .iter()
            .flat_map(|(callee, sites)| sites.iter().map(move |site| (*callee, site)))
            .filter(|(_, site)| site.caller == param.fn_did)
            .flat_map(|(callee, site)| site.args.iter().map(move |arg| (callee, arg)))
            .filter(|(_, arg)| matches!(arg.shape, ArgShape::BareLocal(binding) if binding == param.hir_id))
            .find_map(|(callee, arg)| {
                let target = parameters.get(&(callee, arg.index))?;
                parameter_access(tcx, target, facts, slice_uses, parameters, visited)
            })?;
        AccessReason::Forwarded {
            into: into.detail(),
        }
    };
    let access = match ty.kind() {
        TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut) => "write",
        _ => "read",
    };
    Some(LocalCalleeAccess {
        callee_id: param.fn_did,
        parameter_index: match param.kind {
            SubjectKind::Param { hir_index } => hir_index,
            SubjectKind::Local => unreachable!("local callee access is classified on a parameter"),
        },
        callee: tcx.def_path_str(param.fn_did.to_def_id()),
        parameter: param
            .param_name
            .clone()
            .unwrap_or_else(|| "<unnamed>".to_owned()),
        access,
        reason,
    })
}

/// Caller subjects handed to such a position. A subject in this map may not
/// take a THIN reference form.
pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    facts: &EmitabilityFacts,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
) -> FxHashMap<(LocalDefId, HirId), LocalCalleeAccess> {
    let mut parameters: FxHashMap<(LocalDefId, usize), &Subject> = FxHashMap::default();
    for subject in subjects {
        if let SubjectKind::Param { hir_index } = subject.kind {
            parameters.insert((subject.fn_did, hir_index), subject);
        }
    }
    // One classification per callee parameter, reused across its call sites:
    // the body is a property of the callee, not of any one caller.
    let mut classified: FxHashMap<(LocalDefId, usize), Option<LocalCalleeAccess>> =
        FxHashMap::default();
    let mut out = FxHashMap::default();
    for (callee, sites) in &facts.call_args {
        for site in sites {
            for arg in &site.args {
                let Some(root) = subject_denoting_root(arg.shape) else {
                    continue;
                };
                let Some(parameter) = parameters.get(&(*callee, arg.index)) else {
                    continue;
                };
                let access = classified.entry((*callee, arg.index)).or_insert_with(|| {
                    parameter_access(tcx, parameter, facts, slice_uses, &parameters, &mut vec![])
                });
                if let Some(access) = access {
                    out.entry((site.caller, root))
                        .or_insert_with(|| access.clone());
                }
            }
        }
    }
    out
}
