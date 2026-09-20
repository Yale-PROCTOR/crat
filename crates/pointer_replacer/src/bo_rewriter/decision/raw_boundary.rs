//! Raw-boundary facts and decisions.
//!
//! This module is rewriter-side by design. It consumes the frozen model/MIR and
//! never contributes a solver constraint or cache field.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::{
    mir::{
        Body, Local, Location, Operand, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{Span, def_id::DefId};

use crate::{
    analyses::borrow_ownership::{
        a5_overlap::WholeProgramAttestation, origin_summary::OriginSummaries,
    },
    utils::rustc::RustProgram,
};

/// How deep a signature type is walked before the answer is conceded.
pub(crate) const CARRIER_WALK_DEPTH: u32 = 6;

/// The target pointer's width in bits, which is what an integer has to reach
/// before it can carry a whole address.
fn pointer_bits(tcx: TyCtxt<'_>) -> u64 {
    tcx.data_layout.pointer_size.bits()
}

/// A conservative compile-time walk: can a value of this type carry a pointer?
///
/// Only the scalar kinds that provably carry none answer `false`. Integers at
/// least as wide as the target pointer DO carry one, because a pointer
/// reconstructed from an address inherits the permission the outgoing view
/// created (addendum 256(2)); narrower integers cannot hold an address, and
/// reconstruction from partial values is outside the fragment. Aggregates are
/// walked field-wise through every variant, and everything opaque, generic or
/// past the depth budget is pointer-carrying: the walk fails closed.
pub(crate) fn may_carry_pointer<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> bool {
    if depth == 0 {
        return true;
    }
    match ty.kind() {
        TyKind::Int(int) => int.bit_width().is_none_or(|bits| bits >= pointer_bits(tcx)),
        TyKind::Uint(uint) => uint
            .bit_width()
            .is_none_or(|bits| bits >= pointer_bits(tcx)),
        TyKind::Bool | TyKind::Char | TyKind::Float(_) | TyKind::Never => false,
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|field| may_carry_pointer(tcx, field, depth - 1)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => may_carry_pointer(tcx, *inner, depth - 1),
        // A box owns its pointer, so it is a carrier without a field walk.
        TyKind::Adt(definition, arguments) if !definition.is_box() => definition
            .all_fields()
            .any(|field| may_carry_pointer(tcx, field.ty(tcx, arguments), depth - 1)),
        _ => true,
    }
}

/// Can this callee hand a pointer back to its caller — through its return type,
/// or by writing one into storage the caller owns?
///
/// The second half is what makes this "return **or output**" (addendum 259(2)):
/// a `*mut`/`&mut` parameter whose pointee can itself carry a pointer is output
/// storage, and a callee can stash the argument there just as it can return it.
/// A void-like FFI pointee is treated as carrying, because `*mut c_void` walks
/// to a field-free ADT that would otherwise read as provably pointer-free.
pub(crate) fn callee_may_yield_pointer(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    signature_may_yield_pointer(tcx, tcx.fn_sig(callee).skip_binder().skip_binder())
}

/// The same predicate over a SIGNATURE alone — what an indirect call (a
/// function-pointer operand) offers in place of a definition (R407-8 §2):
/// exact evidence from the pointer's type, never a default.
pub(crate) fn signature_may_yield_pointer<'tcx>(
    tcx: TyCtxt<'tcx>,
    signature: rustc_middle::ty::FnSig<'tcx>,
) -> bool {
    if may_carry_pointer(tcx, signature.output(), CARRIER_WALK_DEPTH) {
        return true;
    }
    signature.inputs().iter().any(|input| {
        let pointee = match input.kind() {
            TyKind::RawPtr(pointee, mutability) => {
                (*mutability == rustc_middle::mir::Mutability::Mut).then_some(*pointee)
            }
            TyKind::Ref(_, pointee, mutability) => {
                (*mutability == rustc_middle::mir::Mutability::Mut).then_some(*pointee)
            }
            _ => None,
        };
        pointee.is_some_and(|pointee| {
            void_like(tcx, pointee) || may_carry_pointer(tcx, pointee, CARRIER_WALK_DEPTH - 1)
        })
    })
}

/// Is this parameter type output storage a callee could stash a pointer in —
/// a `*mut` / `&mut` whose pointee is void-like or can carry a pointer? The
/// second half of [`callee_may_yield_pointer`], per position.
fn output_storage_pointee<'tcx>(tcx: TyCtxt<'tcx>, input: Ty<'tcx>) -> bool {
    let pointee = match input.kind() {
        TyKind::RawPtr(pointee, mutability) => {
            (*mutability == rustc_middle::mir::Mutability::Mut).then_some(*pointee)
        }
        TyKind::Ref(_, pointee, mutability) => {
            (*mutability == rustc_middle::mir::Mutability::Mut).then_some(*pointee)
        }
        _ => None,
    };
    pointee.is_some_and(|pointee| {
        void_like(tcx, pointee) || may_carry_pointer(tcx, pointee, CARRIER_WALK_DEPTH - 1)
    })
}

/// `c_void` and its kin walk to a field-free ADT, which the carrier walk would
/// otherwise call provably pointer-free. Output storage of unknown shape is
/// exactly the case that must fail closed.
fn void_like(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    let TyKind::Adt(definition, _) = ty.kind() else {
        return false;
    };
    tcx.def_path_str(definition.did()).ends_with("c_void")
}

/// A lifetime-free, artifact-stable call-site identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RawBoundarySiteKey {
    pub caller: String,
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub subject: String,
}

/// One exact raw-boundary edit identity.  The subject half supplies the
/// dependency group; the site half keeps two uses of the same subject
/// independently attributable until the closure is applied.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SubjectAtomKey {
    pub id: String,
    pub node: (LocalDefId, HirId),
    pub owner: String,
}

pub(crate) fn site_atom_id(key: &RawBoundarySiteKey) -> String {
    format!(
        "raw-boundary-site:{}:{}:{}:{}:{}:{}",
        key.caller,
        key.block,
        key.statement_index,
        key.callee.path,
        key.argument_index,
        key.subject
    )
}

fn address_atom_id(site: &AddressViewSite) -> String {
    format!(
        "raw-boundary-address:{}:{}:{}:{}:{}",
        site.owner,
        site.node.0.local_def_index.as_u32(),
        site.node.1.local_id.as_u32(),
        site.span.lo().0,
        site.op
    )
}

/// Resolved callee identity. `foreign` is load-bearing: a same-spelled local
/// function is not a libc contract match.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ForeignSymbolKey {
    pub symbol: String,
    pub path: String,
    pub abi: String,
    pub signature: String,
    pub foreign: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawMutability {
    Const,
    Mut,
}

impl RawMutability {
    fn key(self) -> &'static str {
        match self {
            Self::Const => "const",
            Self::Mut => "mut",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NegativeWriteEvidence {
    FosterImmutable,
    LibcReadOnly,
}

impl NegativeWriteEvidence {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::FosterImmutable => "foster-immutable",
            Self::LibcReadOnly => "libc-read-only",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawTargetType {
    pub rendered: String,
    pub pointee: String,
    pub mutability: RawMutability,
    pub depth2: Option<Depth2Target>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Depth2Target {
    pub inner_pointee: String,
    pub inner_mutability: RawMutability,
    pub thin: bool,
}

impl RawTargetType {
    pub(crate) fn is_void_pointee(&self) -> bool {
        self.pointee.rsplit("::").next() == Some("c_void")
    }
}

fn bridge_type_path(tcx: TyCtxt<'_>, ty: Ty<'_>) -> String {
    if let TyKind::RawPtr(pointee, mutability) = ty.kind() {
        return format!(
            "*{} {}",
            if mutability.is_mut() { "mut" } else { "const" },
            bridge_type_path(tcx, *pointee)
        );
    }
    let rendered = format!("{ty:?}");
    if rendered.rsplit("::").next() == Some("c_void") {
        return "core::ffi::c_void".to_owned();
    }
    let local_def = match ty.kind() {
        TyKind::Adt(def, _) => def.did().as_local(),
        TyKind::Foreign(def_id) => def_id.as_local(),
        _ => None,
    };
    let Some(local_def) = local_def else {
        return rendered;
    };
    let full_path = tcx.def_path_str(local_def.to_def_id());
    let crate_prefix = format!("{}::", tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE));
    let relative = full_path.strip_prefix(&crate_prefix).unwrap_or(&full_path);
    if rendered == relative || rendered.starts_with(&format!("{relative}<")) {
        format!("crate::{rendered}")
    } else if rendered == full_path || rendered.starts_with(&format!("{full_path}<")) {
        format!("crate::{}", &rendered[crate_prefix.len()..])
    } else {
        // A local definition must never be emitted as an apparent extern
        // crate. The DefId path is the stable, in-program fallback.
        format!("crate::{relative}")
    }
}

pub(crate) fn raw_target_type(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<RawTargetType> {
    let TyKind::RawPtr(pointee, mutability) = ty.kind() else {
        return None;
    };
    let depth2 = match pointee.kind() {
        TyKind::RawPtr(inner_pointee, inner_mutability) => Some(Depth2Target {
            inner_pointee: bridge_type_path(tcx, *inner_pointee),
            inner_mutability: if inner_mutability.is_mut() {
                RawMutability::Mut
            } else {
                RawMutability::Const
            },
            thin: !matches!(
                inner_pointee.kind(),
                TyKind::Slice(_)
                    | TyKind::Str
                    | TyKind::Dynamic(..)
                    | TyKind::Foreign(..)
                    | TyKind::Param(_)
                    | TyKind::Alias(..)
                    | TyKind::Bound(..)
                    | TyKind::Placeholder(_)
                    | TyKind::Infer(_)
                    | TyKind::Error(_)
            ),
        }),
        _ => None,
    };
    Some(RawTargetType {
        rendered: bridge_type_path(tcx, ty),
        pointee: bridge_type_path(tcx, *pointee),
        mutability: if mutability.is_mut() {
            RawMutability::Mut
        } else {
            RawMutability::Const
        },
        depth2,
    })
}

/// **wave-5d2 (b) — an A5 raw view of a raw-pointer EXPRESSION.**
///
/// The A5 fallback hoists a raw-view argument into the call's snapshot
/// (`let __crat_a5_raw_N: *T = <view>;` before the call). For a bare local or
/// an address-of the hoisted value is the binding itself; a `raw-expr`
/// argument (`buf.as_ptr()`, `(*s).field`, `(*s).field as *mut c_void`) is
/// already the raw value the callee's position takes, so the view is the
/// expression verbatim — the seam's existing `raw-passthrough` template.
///
/// Hoisting evaluates the expression BEFORE the arguments to its left, so the
/// expression must be free of effects: a syntactic allow-list of place reads,
/// projections, dereferences, casts, arithmetic and the pointer / slice
/// methods that only compute an address. Any other call, an assignment, a
/// block, a closure, `|` / `&&` (closures and short-circuits) or `?` refuses (the site keeps its typed hold). Every one
/// of the batch-6 sites this admits (65 in brotli / lodepng) is of the shape
/// `X.as_ptr()`, `(*s).f`, `(*s).f as *mut c_void` or `((*s).arr).as_mut_ptr()`.
pub(crate) fn a5_raw_expr_view_admits(source_shape: &str, argument: &str) -> bool {
    const ADDRESS_METHODS: [&str; 11] = [
        "as_ptr",
        "as_mut_ptr",
        "offset",
        "add",
        "sub",
        "wrapping_add",
        "wrapping_sub",
        "cast",
        "cast_mut",
        "cast_const",
        "len",
    ];
    if source_shape != "raw-expr" {
        return false;
    }
    let text = argument.trim();
    if text.is_empty()
        || text.contains(['{', '}', ';', '?', '|'])
        || text.contains("=>")
        || text.contains("&&")
    {
        return false;
    }
    // `=` outside `==` / `!=` / `<=` / `>=` is an assignment.
    let bytes = text.as_bytes();
    for (index, &byte) in bytes.iter().enumerate() {
        if byte != b'=' {
            continue;
        }
        let previous = index.checked_sub(1).map(|i| bytes[i]);
        let next = bytes.get(index + 1).copied();
        if !matches!(previous, Some(b'=' | b'!' | b'<' | b'>')) && next != Some(b'=') {
            return false;
        }
    }
    // Every call is a method call from the allow-list.
    let mut identifier_start = None;
    let mut chars = text.char_indices().peekable();
    while let Some((index, ch)) = chars.next() {
        if ch.is_alphanumeric() || ch == '_' {
            identifier_start.get_or_insert(index);
            continue;
        }
        if let Some(start) = identifier_start.take() {
            let name = &text[start..index];
            let rest = text[index..].trim_start();
            if rest.starts_with('(') {
                let before = text[..start].trim_end();
                let is_method = before.ends_with('.');
                if !is_method || !ADDRESS_METHODS.contains(&name) {
                    return false;
                }
            }
        }
    }
    // A trailing identifier is a place read, never a call.
    true
}

/// **wave-5d2 (relay 009 STOP 1) — a raw view's argument text over a root
/// another family delivered.** The A5 snapshot hoists the view's argument as
/// the ORIGINAL text; the AST layer's transforms of that root inside the
/// argument (a slice family's `chunk.offset(k)` rewrite, a cursor form) are
/// not in that text, so `from_ref(&*chunk.offset(4))` is emitted over
/// `chunk: &[u8]` (batch 8's composition, lodepng `lodepng_chunk_check_crc`).
/// The stale case is decidable at the terminal replay from what it already
/// knows — the root's PLACED form and the argument text:
///
/// - a root placed as a plain reference (`&T` / `&mut T`) keeps every use
///   that dereferences it first (`&*p`, `(*p).field`: the field's own type
///   whatever the root's form; wave-6f reconciles field edits separately);
///   a use of the binding itself as the pointer operand (`p.offset(..)`,
///   `p as ..`, `p[..]` — `*p.offset(k)` is `*(p.offset(k))`) is stale;
/// - a root placed as a slice, an `Option`, a cursor or a nested slice has no
///   use the original text renders: every mention is stale.
///
/// Such a view is held `nested-caller-edit`, typed, so the callee's class
/// holds instead of emitting stale text and reverting.
pub(crate) fn a5_view_argument_is_stale_over_root(
    argument: &str,
    root_name: &str,
    root_form: super::seam::Form,
) -> bool {
    use super::seam::Form;
    if root_name.is_empty() {
        return false;
    }
    let requires_operand = match root_form {
        Form::Raw => return false,
        Form::Ref { .. } => true,
        Form::Slice { .. } | Form::Opt { .. } | Form::Cursor { .. } | Form::NestedSlice { .. } => {
            false
        }
    };
    let mut from = 0usize;
    while let Some(found) = argument[from..].find(root_name) {
        let start = from + found;
        let end = start + root_name.len();
        let whole = !argument[..start]
            .chars()
            .next_back()
            .is_some_and(|c| c.is_alphanumeric() || c == '_')
            && !argument[end..]
                .chars()
                .next()
                .is_some_and(|c| c.is_alphanumeric() || c == '_');
        if whole {
            if !requires_operand {
                return true;
            }
            let previous = argument[..start].trim_end().chars().next_back();
            let rest = argument[end..].trim_start();
            let binds_tighter = rest.starts_with('.') || rest.starts_with('[');
            if previous != Some('*') || binds_tighter {
                return true;
            }
        }
        from = end;
    }
    false
}

#[cfg(test)]
mod a5_nested_caller_edit_tests {
    use super::{super::seam::Form, a5_view_argument_is_stale_over_root};

    const REF: Form = Form::Ref { mutable: false };
    const SLICE: Form = Form::Slice { mutable: false };

    #[test]
    fn a_reference_root_is_stale_only_as_the_pointer_operand() {
        for text in [
            "&*chunk.offset(4 as isize)",
            "chunk.offset(k) as *const c_void",
            "chunk as *const u8",
            "&chunk[0]",
        ] {
            assert!(
                a5_view_argument_is_stale_over_root(text, "chunk", REF),
                "{text}"
            );
        }
        for text in [
            "&*chunk",
            "&*(*chunk).start",
            "((*reader).data).offset(bytepos as isize) as *const c_void",
            "&mut (*self_0).dist_extra_",
            "(*source).iccp_name",
        ] {
            for root in ["chunk", "reader", "self_0", "source"] {
                assert!(
                    !a5_view_argument_is_stale_over_root(text, root, REF),
                    "{text} / {root}"
                );
            }
        }
    }

    #[test]
    fn a_slice_or_option_root_is_stale_at_any_mention_and_a_raw_root_never() {
        assert!(a5_view_argument_is_stale_over_root(
            "&*chunk", "chunk", SLICE
        ));
        assert!(a5_view_argument_is_stale_over_root(
            "&*chunk.offset(4)",
            "chunk",
            Form::Opt {
                mutable: false,
                slice: false
            }
        ));
        assert!(!a5_view_argument_is_stale_over_root(
            "&*chunk.offset(4)",
            "chunk",
            Form::Raw
        ));
        // Identifier boundaries: `chunk2` and `my_chunk` are not `chunk`.
        assert!(!a5_view_argument_is_stale_over_root(
            "chunk2.offset(1)",
            "chunk",
            SLICE
        ));
        assert!(!a5_view_argument_is_stale_over_root(
            "my_chunk as *const u8",
            "chunk",
            SLICE
        ));
    }
}

#[cfg(test)]
mod a5_raw_expr_view_tests {
    use super::a5_raw_expr_view_admits;

    #[test]
    fn the_batch6_shapes_are_admitted() {
        for text in [
            "dist_bits.as_ptr()",
            "histogram.as_ptr()",
            "(*self_0).block_lengths_",
            "(*self_0).literal_costs_ as *mut libc::c_void",
            "((*h).code_length_histo).as_mut_ptr()",
            "(posdata.distance_cache).as_mut_ptr()",
            "p.offset(i as isize)",
            "(*source).iccp_profile",
        ] {
            assert!(a5_raw_expr_view_admits("raw-expr", text), "{text}");
        }
    }

    #[test]
    fn effects_and_other_shapes_are_refused() {
        for text in [
            "next_line(fp)",
            "(*m).free_func.expect(\"non-null\")(p)",
            "q.unwrap()",
            "{ let t = p; t }",
            "p = q",
            "|x| x",
            "f()?",
            "",
        ] {
            assert!(!a5_raw_expr_view_admits("raw-expr", text), "{text}");
        }
        assert!(!a5_raw_expr_view_admits("bare-local", "p"));
        assert!(!a5_raw_expr_view_admits("cast", "p as *mut u8"));
        // Comparisons are not assignments.
        assert!(a5_raw_expr_view_admits("raw-expr", "(*s).a == (*s).b"));
    }
}

/// Render the already-selected same-object PAIR raw-view role.
///
/// This is intentionally distinct from [`template_for`]: PAIR has already
/// established the T2 disposition and must describe the safe source's final
/// form. Shared data still cannot produce a mutable raw pointer without the
/// negative-write evidence required by R-B.
pub(crate) fn pair_raw_view_expression(
    source: Option<&super::Decision>,
    target: &RawTargetType,
    argument: &str,
    source_shape: &str,
) -> Option<String> {
    use super::Decision;

    let pointee = &target.pointee;
    let raw_passthrough = || {
        matches!(
            source_shape,
            "bare-local" | "cast-of-local" | "raw-expr" | "cast"
        )
        .then(|| argument.to_owned())
    };
    match source {
        Some(Decision::Ref { mutable }) | Some(Decision::InferredRef { mutable, .. }) => {
            match (*mutable, target.mutability) {
                (true, RawMutability::Mut) => Some(format!("core::ptr::from_mut({argument})")),
                (true, RawMutability::Const) => Some(format!("core::ptr::from_ref(&*{argument})")),
                (false, RawMutability::Const) => Some(format!("core::ptr::from_ref({argument})")),
                (false, RawMutability::Mut) => None,
            }
        }
        Some(Decision::Slice { mutable, .. }) => match (*mutable, target.mutability) {
            (true, RawMutability::Mut) => Some(format!("{argument}.as_mut_ptr()")),
            (_, RawMutability::Const) => Some(format!("{argument}.as_ptr()")),
            (false, RawMutability::Mut) => None,
        },
        Some(Decision::Opt { mutable, slice, .. }) => match (*mutable, *slice, target.mutability) {
            (true, false, RawMutability::Mut) => Some(format!(
                "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), core::ptr::from_mut)"
            )),
            (_, false, RawMutability::Const) => Some(format!(
                "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), core::ptr::from_ref)"
            )),
            (true, true, RawMutability::Mut) => Some(format!(
                "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_mut_ptr())"
            )),
            (_, true, RawMutability::Const) => Some(format!(
                "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_ptr())"
            )),
            (false, _, RawMutability::Mut) => None,
        },
        Some(Decision::Degraded(_)) | None => match source_shape {
            "addr-of-mut" if target.mutability == RawMutability::Mut => {
                Some(format!("core::ptr::from_mut({argument})"))
            }
            "addr-of-mut" => Some(format!("core::ptr::from_ref(&*{argument})")),
            "addr-of" if target.mutability == RawMutability::Const => {
                Some(format!("core::ptr::from_ref({argument})"))
            }
            _ => raw_passthrough(),
        },
        Some(Decision::Box(_) | Decision::NestedSlice { .. } | Decision::Cursor { .. }) => None,
    }
}

/// One resolved argument to a non-body callee. This is the fact the old
/// `EscapeKind::ForeignArg` could not express: callee, position and target type
/// are captured at the HIR visitor boundary rather than reconstructed later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForeignCallArgFact {
    pub caller: LocalDefId,
    pub callee: ForeignSymbolKey,
    pub call_span: Span,
    pub argument_index: usize,
    pub argument_span: Span,
    pub root: Option<HirId>,
    /// The argument's place root was reached through `*owner`. In that shape
    /// the foreign extent belongs to a projected field/value, not to the
    /// aggregate pointer named by `root`.
    pub root_through_deref: bool,
    pub shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
    pub direct_storage: Option<(HirId, Span)>,
    pub adapter_operand_span: Span,
    pub adapter_operand_mutability: Option<RawMutability>,
    pub contract_count: Option<ContractCountOperandFact>,
    /// Wave-4 #1b: the call's return value is discarded at the call (a `;`
    /// statement or `let _ =`), so a returned alias of an argument is never
    /// retained by the caller.
    pub return_unused: bool,
    /// Wave-4 #1b: the pointee of the argument's OPERAND beneath its casts —
    /// the element the subject is a slice of at a `c_void` position.
    pub operand_pointee: String,
}

impl ForeignCallArgFact {
    /// The pointer subject whose own extent the foreign position consumes.
    /// A root reached through `*aggregate` names only the owner of a projected
    /// child place, so attributing the child's extent to it is invalid.
    pub(crate) fn direct_subject_root(&self) -> Option<HirId> {
        self.direct_storage
            .map(|(storage, _)| storage)
            .or_else(|| (!self.root_through_deref).then_some(self.root).flatten())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContractCountOperandFact {
    pub argument_index: usize,
    pub span: Span,
    pub expression: String,
    /// R451: the count is exactly `size_of::<T>()` (under its casts) with `T`
    /// the SAME TYPE as this argument's own pointee — decided on the types,
    /// never on their spellings, because the count names the type as the call's
    /// module sees it (`binn`, a C2Rust alias) while a printed pointee is the
    /// resolved item (`src::binn::binn_struct`).
    pub one_pointee: bool,
    /// The contract describes the whole range rather than an upper limit.
    /// Units and typed construction validity remain separate decision gates.
    pub exact: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoundaryDirection {
    OutgoingArgument,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFact {
    pub key: RawBoundarySiteKey,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee_local: Option<LocalDefId>,
    pub direction: BoundaryDirection,
    pub source_span: Span,
    pub call_span: Span,
    pub source_site: String,
    pub source_shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
    pub direct_storage_span: Option<Span>,
    pub adapter_operand_span: Span,
    pub adapter_operand_mutability: Option<RawMutability>,
    /// Can this callee hand a pointer back — by return or by output storage?
    /// Fails closed: an unresolved callee answers `true`.
    pub callee_may_yield_pointer: bool,
    /// wave-6v2 (R406-6): the sibling argument positions of this call whose
    /// operand is `&mut local` over a caller local that never leaves the
    /// caller's frame (`binn_counted::frame_confined`). A callee that retains
    /// the subject only by storing through one of these parameters retains it
    /// into storage that dies with the caller — T1, not positive retention.
    pub frame_confined_outputs: Vec<usize>,
    /// wave-6v2 (R406-6): every way this callee could hand a descendant of
    /// the subject back to the caller ends in the caller's own frame — its
    /// return type cannot carry a pointer and every other output-storage
    /// position (a `*mut` / `&mut` parameter whose pointee is void-like or can
    /// carry a pointer) is a frame-confined operand at this call. A shared
    /// view then needs no returned-child permission: there is no descendant
    /// the caller could write through.
    pub descendants_frame_confined: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFailure {
    pub caller: String,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub source_span: Span,
    pub source_site: String,
    pub reason: SiteMatchFailure,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFacts {
    pub forward_return_independent:
        FxHashMap<RawBoundarySiteKey, super::slice_return_evidence::ReturnIndependence>,
    pub sites: Vec<RawBoundarySiteFact>,
    pub failures: Vec<RawBoundarySiteFailure>,
}

pub(crate) fn symbol_key(
    tcx: TyCtxt<'_>,
    callee: DefId,
    body_functions: &[LocalDefId],
) -> ForeignSymbolKey {
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    let foreign = !callee
        .as_local()
        .is_some_and(|local| body_functions.contains(&local));
    ForeignSymbolKey {
        symbol: tcx.item_name(callee).to_string(),
        path: tcx.def_path_str(callee),
        abi: format!("{:?}", sig.abi),
        signature: format!("{sig:?}"),
        foreign,
    }
}

/// wave-6f (W6F-2): the key of a call through a FUNCTION POINTER. No symbol
/// and no path exist; the signature is the identity, so the HIR fact and the
/// MIR terminator meet on the pointer type alone.
pub(crate) fn indirect_symbol_key(sig: rustc_middle::ty::FnSig<'_>) -> ForeignSymbolKey {
    ForeignSymbolKey {
        symbol: "<indirect>".to_owned(),
        path: "<indirect>".to_owned(),
        abi: format!("{:?}", sig.abi),
        signature: format!("{sig:?}"),
        foreign: true,
    }
}

fn operand_callee(func: &Operand<'_>) -> Option<DefId> {
    let constant = func.constant()?;
    let TyKind::FnDef(callee, _) = *constant.ty().kind() else {
        return None;
    };
    Some(callee)
}

fn mir_candidates(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    caller: LocalDefId,
    expected: &ForeignSymbolKey,
    argument_span: Span,
) -> Vec<MirCallCandidate> {
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let argument_span = argument_span.source_callsite();
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let terminator = data.terminator();
            let func = match &terminator.kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => return None,
            };
            let (key, callee, may_yield_pointer) = match operand_callee(func) {
                Some(callee) => (
                    symbol_key(tcx, callee, functions),
                    Some(callee),
                    callee_may_yield_pointer(tcx, callee),
                ),
                // wave-6f (W6F-2): a function-pointer operand — keyed by its
                // pointer signature, no definition; the yield verdict is the
                // signature's (R407-8 §2).
                None => match func.ty(&body.local_decls, tcx).kind() {
                    TyKind::FnPtr(sig_tys, header) => {
                        let signature = sig_tys.with(*header).skip_binder();
                        (
                            indirect_symbol_key(signature),
                            None,
                            signature_may_yield_pointer(tcx, signature),
                        )
                    }
                    _ => return None,
                },
            };
            let call_span = terminator.source_info.span.source_callsite();
            (key == *expected && call_span.contains(argument_span)).then_some(MirCallCandidate {
                block: block.as_u32(),
                statement_index: data.statements.len() as u32,
                callee: key,
                did: callee,
                may_yield_pointer,
            })
        })
        .collect()
}

impl RawBoundarySiteFacts {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        emitability: &super::emitability::EmitabilityFacts,
    ) -> Self {
        let tcx = program.tcx;
        let mut out = Self::default();
        for fact in &emitability.foreign_call_args {
            let candidates = mir_candidates(
                tcx,
                &program.functions,
                fact.caller,
                &fact.callee,
                fact.argument_span,
            );
            match select_unique_site(&fact.callee, &candidates) {
                Ok((block, statement_index)) => out.sites.push(RawBoundarySiteFact {
                    key: RawBoundarySiteKey {
                        caller: tcx.def_path_str(fact.caller.to_def_id()),
                        block,
                        statement_index,
                        callee: fact.callee.clone(),
                        argument_index: fact.argument_index,
                        subject: fact
                            .direct_storage
                            .map(|(storage, _)| storage)
                            .or(fact.root)
                            .map_or_else(|| "<unrooted>".to_owned(), |root| format!("{root:?}")),
                    },
                    node: fact
                        .direct_storage
                        .map(|(storage, _)| (fact.caller, storage))
                        .or_else(|| fact.root.map(|root| (fact.caller, root))),
                    callee_local: None,
                    direction: BoundaryDirection::OutgoingArgument,
                    source_span: fact.argument_span,
                    call_span: fact.call_span,
                    source_site: tcx
                        .sess
                        .source_map()
                        .span_to_diagnostic_string(fact.argument_span),
                    source_shape: fact.shape,
                    source_type: fact.source_type.clone(),
                    target: fact.target.clone(),
                    direct_storage_span: fact.direct_storage.map(|(_, span)| span),
                    adapter_operand_span: fact.adapter_operand_span,
                    adapter_operand_mutability: fact.adapter_operand_mutability,
                    callee_may_yield_pointer: unique_candidate(&fact.callee, &candidates)
                        .is_none_or(|site| site.may_yield_pointer),
                    frame_confined_outputs: Vec::new(),
                    descendants_frame_confined: false,
                }),
                Err(reason) => out.failures.push(RawBoundarySiteFailure {
                    caller: tcx.def_path_str(fact.caller.to_def_id()),
                    node: fact
                        .direct_storage
                        .map(|(storage, _)| (fact.caller, storage))
                        .or_else(|| fact.root.map(|root| (fact.caller, root))),
                    callee: fact.callee.clone(),
                    argument_index: fact.argument_index,
                    source_span: fact.argument_span,
                    source_site: tcx
                        .sess
                        .source_map()
                        .span_to_diagnostic_string(fact.argument_span),
                    reason,
                }),
            }
        }
        for (&callee, calls) in &emitability.call_args {
            let callee_key = symbol_key(tcx, callee.to_def_id(), &program.functions);
            for call in calls {
                for argument in &call.args {
                    let Some(target) = argument.target.clone() else {
                        continue;
                    };
                    let candidates = mir_candidates(
                        tcx,
                        &program.functions,
                        call.caller,
                        &callee_key,
                        argument.span,
                    );
                    let frame_confined_outputs = call
                        .args
                        .iter()
                        .filter(|sibling| sibling.index != argument.index)
                        .filter(|sibling| {
                            sibling.direct_storage.is_some_and(|(local, _)| {
                                match super::binn_counted::frame_confined(
                                    tcx,
                                    &program.functions,
                                    call.caller,
                                    local,
                                    call.span,
                                ) {
                                    Some(super::binn_counted::Confinement::Plain) => true,
                                    // Integer fields are read out of the local:
                                    // the callee may not write an integer image
                                    // of the argument anywhere (wave-6r's scan
                                    // refuses a cast to a non-pointer).
                                    Some(super::binn_counted::Confinement::IntegerReads) => {
                                        crate::bo_rewriter::wave6r_child_access::position_is_descendant_free_modulo_output(
                                            tcx,
                                            &program.functions,
                                            callee,
                                            argument.index,
                                            sibling.index,
                                        )
                                    }
                                    None => false,
                                }
                            })
                        })
                        .map(|sibling| sibling.index)
                        .collect::<Vec<_>>();
                    match select_unique_site(&callee_key, &candidates) {
                        Ok((block, statement_index)) => out.sites.push(RawBoundarySiteFact {
                            key: RawBoundarySiteKey {
                                caller: tcx.def_path_str(call.caller.to_def_id()),
                                block,
                                statement_index,
                                callee: callee_key.clone(),
                                argument_index: argument.index,
                                subject: argument
                                    .direct_storage
                                    .map(|(storage, _)| storage)
                                    .or_else(|| argument.shape.place_root())
                                    .map_or_else(
                                        || "<unrooted>".to_owned(),
                                        |root| format!("{root:?}"),
                                    ),
                            },
                            node: argument
                                .direct_storage
                                .map(|(storage, _)| (call.caller, storage))
                                .or_else(|| {
                                    argument.shape.place_root().map(|root| (call.caller, root))
                                }),
                            callee_local: Some(callee),
                            direction: BoundaryDirection::OutgoingArgument,
                            source_span: argument.span,
                            call_span: call.span,
                            source_site: tcx
                                .sess
                                .source_map()
                                .span_to_diagnostic_string(argument.span),
                            source_shape: argument.shape.key(),
                            source_type: argument.source_type.clone(),
                            target,
                            direct_storage_span: argument.direct_storage.map(|(_, span)| span),
                            adapter_operand_span: argument.adapter_operand_span,
                            adapter_operand_mutability: argument.adapter_operand_mutability,
                            callee_may_yield_pointer: unique_candidate(&callee_key, &candidates)
                                .is_none_or(|site| site.may_yield_pointer),
                            frame_confined_outputs: frame_confined_outputs.clone(),
                            descendants_frame_confined: {
                                let signature = tcx.fn_sig(callee).skip_binder().skip_binder();
                                !may_carry_pointer(tcx, signature.output(), CARRIER_WALK_DEPTH)
                                    && signature.inputs().iter().enumerate().all(
                                        |(index, input)| {
                                            index == argument.index
                                                || !output_storage_pointee(tcx, *input)
                                                || frame_confined_outputs.contains(&index)
                                        },
                                    )
                            },
                        }),
                        Err(reason) => out.failures.push(RawBoundarySiteFailure {
                            caller: tcx.def_path_str(call.caller.to_def_id()),
                            node: argument
                                .direct_storage
                                .map(|(storage, _)| (call.caller, storage))
                                .or_else(|| {
                                    argument.shape.place_root().map(|root| (call.caller, root))
                                }),
                            callee: callee_key.clone(),
                            argument_index: argument.index,
                            source_span: argument.span,
                            source_site: tcx
                                .sess
                                .source_map()
                                .span_to_diagnostic_string(argument.span),
                            reason,
                        }),
                    }
                }
            }
        }
        out.forward_return_independent = super::slice_return_evidence::collect(program, &out);
        out.sites.sort_by(|left, right| left.key.cmp(&right.key));
        out.failures.sort_by(|left, right| {
            (&left.caller, &left.callee, left.argument_index).cmp(&(
                &right.caller,
                &right.callee,
                right.argument_index,
            ))
        });
        out
    }

    pub(crate) fn to_tsv(&self) -> String {
        let mut out = String::from(
            "status\tcaller\tblock\tstatement_index\tcallee_path\tcallee_symbol\tforeign\tabi\tsignature\targument_index\tsubject\tsource_site\tsource_lo\tsource_hi\tsource_shape\tsource_type\ttarget_type\ttarget_pointee\ttarget_mutability\treason\n",
        );
        for site in &self.sites {
            out.push_str(&format!(
                "site\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\n",
                site.key.caller,
                site.key.block,
                site.key.statement_index,
                site.key.callee.path,
                site.key.callee.symbol,
                u8::from(site.key.callee.foreign),
                site.key.callee.abi,
                site.key.callee.signature,
                site.key.argument_index,
                site.key.subject,
                site.source_site,
                site.source_span.lo().0,
                site.source_span.hi().0,
                site.source_shape,
                site.source_type,
                site.target.rendered,
                site.target.pointee,
                site.target.mutability.key(),
            ));
        }
        for failure in &self.failures {
            out.push_str(&format!(
                "failure\t{}\t-\t-\t{}\t{}\t{}\t{}\t{}\t{}\t-\t{}\t{}\t{}\t-\t-\t-\t-\t-\t{}\n",
                failure.caller,
                failure.callee.path,
                failure.callee.symbol,
                u8::from(failure.callee.foreign),
                failure.callee.abi,
                failure.callee.signature,
                failure.argument_index,
                failure.source_site,
                failure.source_span.lo().0,
                failure.source_span.hi().0,
                failure.reason.key(),
            ));
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirCallCandidate {
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
    /// The resolved callee, kept so the carrier walk can read its signature.
    /// Selection still keys on `callee`; this never participates in matching.
    /// `None` for an INDIRECT call (a function-pointer operand): there is no
    /// definition to read, and the carrier walk fails closed.
    pub did: Option<DefId>,
    /// Whether the callee can hand a pointer back (its return, or a writable
    /// carrier among its inputs) — read from the definition for a direct
    /// call and from the function-pointer signature for an indirect one.
    pub may_yield_pointer: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SiteMatchFailure {
    Missing,
    Ambiguous,
    CalleeMismatch,
}

impl SiteMatchFailure {
    fn key(self) -> &'static str {
        match self {
            Self::Missing => "site-missing",
            Self::Ambiguous => "site-ambiguous",
            Self::CalleeMismatch => "callee-mismatch",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RetentionUnknownReason {
    CalleeUnresolved,
    FnPtrWeb,
    OpenBoundary,
    MultiDef,
    NontransparentDef,
    ProjectionAmbiguous,
    OutputStorage,
    FieldOrGlobalStore,
    Return,
    LocalSummaryUnknown,
    AttestationAbsent,
    AnalysisIncomplete,
    ReturnedAliasUsed,
    ReturnedAliasUnknown,
}

impl RetentionUnknownReason {
    pub(crate) const ALL: [Self; 14] = [
        Self::CalleeUnresolved,
        Self::FnPtrWeb,
        Self::OpenBoundary,
        Self::MultiDef,
        Self::NontransparentDef,
        Self::ProjectionAmbiguous,
        Self::OutputStorage,
        Self::FieldOrGlobalStore,
        Self::Return,
        Self::LocalSummaryUnknown,
        Self::AttestationAbsent,
        Self::AnalysisIncomplete,
        Self::ReturnedAliasUsed,
        Self::ReturnedAliasUnknown,
    ];

    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::CalleeUnresolved => "retention-callee-unresolved",
            Self::FnPtrWeb => "retention-fnptr-web",
            Self::OpenBoundary => "retention-open-boundary",
            Self::MultiDef => "retention-multi-def",
            Self::NontransparentDef => "retention-nontransparent-def",
            Self::ProjectionAmbiguous => "retention-projection-ambiguous",
            Self::OutputStorage => "retention-output-storage",
            Self::FieldOrGlobalStore => "retention-field-or-global-store",
            Self::Return => "retention-return",
            Self::LocalSummaryUnknown => "retention-local-summary-unknown",
            Self::AttestationAbsent => "retention-attestation-absent",
            Self::AnalysisIncomplete => "retention-analysis-incomplete",
            Self::ReturnedAliasUsed => "retention-returned-alias-used",
            Self::ReturnedAliasUnknown => "retention-returned-alias-unknown",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RetentionEventKind {
    Transparent,
    Return,
    OutputStorage,
    FieldOrGlobalStore,
    UnknownCall,
    KnownNoRetainCall,
    LocalCall,
    DereferenceOnly,
    Free,
    MultiDef,
    Nontransparent,
    ReturnedAlias,
    ReturnedChildSink,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RetentionStep {
    pub location: String,
    pub kind: RetentionEventKind,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetentionCertificate {
    pub function: String,
    pub argument_index: usize,
    pub steps: Vec<RetentionStep>,
    pub attestation: &'static str,
    /// **R476-1 (USER, relay 045).** Present when this certificate rests on
    /// the frame-bounded discharge rather than on the absence of any retaining
    /// step: the receipt names the container and the callees it rests on.
    pub frame_bounded: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RetentionVerdict {
    NoRetain {
        certificate: RetentionCertificate,
    },
    Retains {
        sink: RetentionStep,
        path: Vec<RetentionStep>,
    },
    Unknown {
        reason: RetentionUnknownReason,
        frontier: Vec<RetentionStep>,
    },
}

/// **R476-1 (USER ruling, relay 045) — a frame-bounded field store.**
///
/// The subject is stored into a field of `container`, a stack local of THIS
/// frame that does not escape it, and the subject is dead after the store. The
/// retained pointer therefore cannot outlive the frame through this store —
/// unless a callee that receives the container's address keeps it, which
/// `evaluate_retention` decides from those callees' own certificates
/// (`unknown` or `retains` ⇒ the hold stands).
#[derive(Clone, Debug, PartialEq, Eq)]
struct FrameBoundedStore {
    step: RetentionStep,
    container: Local,
    callees: Vec<(LocalDefId, usize)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RetentionDependency {
    callee: LocalDefId,
    argument_index: usize,
    step: RetentionStep,
    /// wave-6v2 (R407-11): the callee's only positive sinks are stores
    /// through its own output parameters and every such operand at this call
    /// is a frame-confined local of this body — the dependency is discharged
    /// at this call; only the callee's RESIDUAL (its unknowns and its other
    /// dependencies) still travels.
    discharged_by_stack_storage: bool,
    /// wave-6v2 (R407-11): the callee only returns this argument and the
    /// call's destination was made a reachable alias in this body (the
    /// returned-alias continuation) — the callee's `return` sink is this
    /// body's to account for; only the callee's residual travels.
    continued_returned_alias: bool,
}

/// wave-6v2 (R407-11): what the previous derivation pass learned about every
/// local callee, consumed by the next pass of [`collect_retention_facts`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct RetentionPriorPass {
    /// `(callee, argument)` whose only positive sinks are `return` of that
    /// argument: a call's destination is then a reachable alias of the
    /// argument in the caller, and the caller's own sinks are the ones that
    /// count (the returned-alias continuation).
    returning: FxHashSet<(LocalDefId, usize)>,
    /// `(callee, argument)` whose only positive sinks are stores through the
    /// callee's own output parameters, with those parameter indices.
    output_storage_only: FxHashMap<(LocalDefId, usize), Vec<usize>>,
}

impl RetentionPriorPass {
    fn of(facts: &FxHashMap<(LocalDefId, usize), RetentionBodyFacts>) -> Self {
        let mut out = Self::default();
        for (&key, fact) in facts {
            if fact.retains.is_empty() {
                continue;
            }
            if fact
                .retains
                .iter()
                .all(|step| step.kind == RetentionEventKind::Return)
            {
                out.returning.insert(key);
            }
            if fact
                .retains
                .iter()
                .all(|step| step.kind == RetentionEventKind::OutputStorage)
                && let Some(outputs) = output_storage_positions(fact)
            {
                out.output_storage_only.insert(key, outputs);
            }
        }
        out
    }
}

/// What a call's output-storage operand denotes, through transparent copies
/// and casts: this body's own raw-pointer parameter, or a borrow of a local.
enum OutputOperand {
    Parameter(Local),
    /// The borrowed local and the location of the borrow itself.
    Borrowed(Local, Location),
}

/// The storage a call operand carries the address of: the operand local was
/// defined, before `call`, by exactly one `&mut _v` / `&raw mut _v` (through
/// transparent copies and casts) — `_v` is the storage the callee's output
/// parameter writes into — or it is (a transparent copy of) one of this
/// body's raw-pointer parameters.
fn output_operand<'tcx>(
    body: &Body<'tcx>,
    operand: Local,
    call: Location,
) -> Option<OutputOperand> {
    let mut current = operand;
    for _ in 0..8 {
        if current.as_usize() > 0
            && current.as_usize() <= body.arg_count
            && matches!(body.local_decls[current].ty.kind(), TyKind::RawPtr(..))
        {
            return Some(OutputOperand::Parameter(current));
        }
        let mut definitions = body
            .basic_blocks
            .iter_enumerated()
            .flat_map(|(block, data)| {
                data.statements
                    .iter()
                    .enumerate()
                    .map(move |(index, statement)| {
                        (
                            Location {
                                block,
                                statement_index: index,
                            },
                            statement,
                        )
                    })
            })
            .filter_map(|(location, statement)| match &statement.kind {
                StatementKind::Assign(box (lhs, rhs)) if lhs.as_local() == Some(current) => {
                    Some((location, rhs))
                }
                _ => None,
            });
        let (location, rhs) = definitions.next()?;
        if definitions.next().is_some() || !definition_before(body, location, call) {
            return None;
        }
        match rhs {
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                if let Some(local) = place.as_local() {
                    return Some(OutputOperand::Borrowed(local, location));
                }
                // `&raw mut (*_r)`: a reborrow through the reference `_r`.
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && matches!(body.local_decls[place.local].ty.kind(), TyKind::Ref(..))
                {
                    current = place.local;
                    continue;
                }
                return None;
            }
            Rvalue::Cast(_, operand, _) | Rvalue::Use(operand) => {
                current = operand.place()?.as_local()?;
            }
            _ => return None,
        }
    }
    None
}

/// wave-6v2 (R410-3): `core`'s raw-pointer methods, by what they do with the
/// receiver's provenance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CorePointerMethod {
    /// Returns a pointer derived from the receiver (`offset`, `add`, `cast`, ..).
    Derive,
    /// Observes the receiver or reads through it; retains nothing.
    Observe,
    /// Writes a VALUE through the receiver (`write`, `write_unaligned`, ..).
    Write,
}

/// The tag a modeled core-pointer-method step carries in its detail.
const CORE_POINTER_METHOD_TAG: &str = "core-pointer-method";

fn core_pointer_method(tcx: TyCtxt<'_>, callee: DefId) -> Option<CorePointerMethod> {
    let path = tcx.def_path_str(callee);
    let (prefix, name) = path.rsplit_once("::")?;
    if !(prefix.starts_with("core::ptr::") || prefix.starts_with("std::ptr::"))
        || !prefix.contains("<impl *")
    {
        return None;
    }
    Some(match name {
        "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
        | "byte_offset" | "byte_add" | "byte_sub" | "cast" | "cast_mut" | "cast_const" => {
            CorePointerMethod::Derive
        }
        "is_null" | "offset_from" | "byte_offset_from" | "read" | "read_unaligned"
        | "read_volatile" | "addr" | "align_offset" | "is_aligned" => CorePointerMethod::Observe,
        "write"
        | "write_unaligned"
        | "write_volatile"
        | "write_bytes"
        | "copy_from"
        | "copy_from_nonoverlapping"
        | "copy_to"
        | "copy_to_nonoverlapping"
        | "swap"
        | "replace" => CorePointerMethod::Write,
        _ => return None,
    })
}

/// wave-6v2 (R407-11): the ONE raw-pointer parameter this local is a
/// transparent alias of (`_p -> .. -> local` through the body's alias edges),
/// or `None` when it is rooted at no parameter or at more than one.
fn parameter_alias_root(
    body: &Body<'_>,
    aliases: &[(Local, Local, RetentionStep)],
    local: Local,
) -> Option<Local> {
    let mut roots = Vec::new();
    for parameter in 1..=body.arg_count {
        let parameter = Local::from_usize(parameter);
        if !matches!(body.local_decls[parameter].ty.kind(), TyKind::RawPtr(..)) {
            continue;
        }
        let mut reachable = FxHashSet::from_iter([parameter]);
        loop {
            let before = reachable.len();
            for (source, destination, _) in aliases {
                if reachable.contains(source) {
                    reachable.insert(*destination);
                }
            }
            if reachable.len() == before {
                break;
            }
        }
        if reachable.contains(&local) {
            roots.push(parameter);
        }
    }
    match roots.as_slice() {
        [root] => Some(*root),
        _ => None,
    }
}

/// The output-parameter positions an `OutputStorage`-only fact stores through
/// (`store _s through _p` → `p - 1`).
fn output_storage_positions(facts: &RetentionBodyFacts) -> Option<Vec<usize>> {
    let mut parameters = Vec::new();
    for step in &facts.retains {
        let local = step
            .detail
            .rsplit("through _")
            .next()?
            .parse::<usize>()
            .ok()?;
        parameters.push(local.checked_sub(1)?);
    }
    parameters.sort_unstable();
    parameters.dedup();
    Some(parameters)
}

/// wave-6v2 (R407-11): is this local of `body` FRAME-CONFINED at the MIR
/// level — storage whose contents never leave the function except through
/// reads the walk can follow? Its address may be taken only by the one borrow
/// at `call` (the operand of the certified call); a read of it is either a
/// projection whose type
/// cannot carry a pointer (or of the whole local when the local's own type
/// cannot), or a pointer-carrying FIELD copied into a local — returned, so
/// the walk continues from that local; writes to it and its fields are free.
/// `None` when any other use exists. The HIR twin,
/// `binn_counted::frame_confined`, answers the site-level question.
fn mir_frame_confined<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    call: Location,
) -> Option<Vec<(Local, Location)>> {
    use rustc_middle::mir::visit::{PlaceContext, Visitor};
    struct Uses<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        local: Local,
        call: Location,
        confined: bool,
        field_reads: Vec<(Local, Location)>,
        allowed_read: Option<Location>,
    }
    impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
        fn visit_assign(
            &mut self,
            place: &rustc_middle::mir::Place<'tcx>,
            rvalue: &Rvalue<'tcx>,
            location: Location,
        ) {
            if let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = rvalue
                && source.local == self.local
                && !source.projection.is_empty()
                && may_carry_pointer(
                    self.tcx,
                    source.ty(self.body, self.tcx).ty,
                    CARRIER_WALK_DEPTH,
                )
                && let Some(destination) = place.as_local()
            {
                self.field_reads.push((destination, location));
                self.allowed_read = Some(location);
            }
            self.super_assign(place, rvalue, location);
            self.allowed_read = None;
        }

        fn visit_place(
            &mut self,
            place: &rustc_middle::mir::Place<'tcx>,
            context: PlaceContext,
            location: Location,
        ) {
            if place.local != self.local {
                return;
            }
            use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext};
            let confined = match context {
                PlaceContext::NonUse(_) => true,
                PlaceContext::MutatingUse(MutatingUseContext::Store) => true,
                PlaceContext::MutatingUse(
                    MutatingUseContext::Borrow | MutatingUseContext::RawBorrow,
                )
                | PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::SharedBorrow
                    | NonMutatingUseContext::FakeBorrow
                    | NonMutatingUseContext::RawBorrow,
                ) => location == self.call,
                // A fake read inspects nothing.
                PlaceContext::NonMutatingUse(NonMutatingUseContext::Inspect) => true,
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Copy | NonMutatingUseContext::Move,
                ) => {
                    self.allowed_read == Some(location)
                        || !may_carry_pointer(
                            self.tcx,
                            place.ty(self.body, self.tcx).ty,
                            CARRIER_WALK_DEPTH,
                        )
                }
                PlaceContext::MutatingUse(MutatingUseContext::Drop) => true,
                _ => false,
            };
            self.confined &= confined;
        }
    }
    let mut uses = Uses {
        tcx,
        body,
        local,
        call,
        confined: true,
        field_reads: Vec::new(),
        allowed_read: None,
    };
    uses.visit_body(body);
    uses.confined.then_some(uses.field_reads)
}

/// wave-6v2 (R407-11): how one call to an output-storage-only callee is
/// discharged in the caller's own retention row, per output position: the
/// operand borrows a frame-confined local of this body (its pointer-carrying
/// field reads continue the walk), or the operand IS a raw-pointer parameter
/// of this body (the sink transposes to `store _s through _p` of this body).
#[derive(Clone, Debug, Default)]
struct OutputDischarge {
    ok: bool,
    /// `(argument local, this body's output parameter local)` transposed sinks.
    transposed: Vec<(Local, Local)>,
    /// `(argument local, field-read destination, read location)` aliases.
    field_reads: Vec<(Local, Local, Location)>,
}

fn output_discharge<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[rustc_middle::mir::Operand<'tcx>],
    argument: Local,
    outputs: &[usize],
    call: Location,
) -> OutputDischarge {
    let mut out = OutputDischarge {
        ok: true,
        ..Default::default()
    };
    for &output in outputs {
        let Some(operand) = args
            .get(output)
            .and_then(|operand| operand.place())
            .and_then(|place| place.as_local())
        else {
            out.ok = false;
            break;
        };
        match output_operand(body, operand, call) {
            Some(OutputOperand::Parameter(parameter)) => {
                out.transposed.push((argument, parameter));
            }
            Some(OutputOperand::Borrowed(referent, borrow)) => {
                match mir_frame_confined(tcx, body, referent, borrow) {
                    Some(reads) => out
                        .field_reads
                        .extend(reads.into_iter().map(|(dest, at)| (argument, dest, at))),
                    None => {
                        out.ok = false;
                        break;
                    }
                }
            }
            None => {
                out.ok = false;
                break;
            }
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RetentionBodyFacts {
    function: LocalDefId,
    function_path: String,
    /// Only parameter-rooted facts can mint a parameter certificate.
    argument_index: Option<usize>,
    steps: Vec<RetentionStep>,
    retains: Vec<RetentionStep>,
    unknowns: BTreeMap<RetentionUnknownReason, Vec<RetentionStep>>,
    dependencies: Vec<RetentionDependency>,
    /// R476-1: the retaining steps this body's own frame bounds, pending the
    /// container callees' certificates.
    frame_bounded: Vec<FrameBoundedStore>,
    /// R477-4b: the retaining steps that store the parameter's provenance into
    /// a FRESH ALLOCATION which escapes only back into the parameter's own
    /// subgraph, so a caller whose frame bounds the parameter bounds them too.
    retains_into_fresh_allocation: Vec<RetentionStep>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RetentionSummaries {
    rows: FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    facts: FxHashMap<(LocalDefId, usize), RetentionBodyFacts>,
    attested: bool,
    returned_children: FxHashMap<LocalDefId, Vec<ReturnedChildRecord>>,
    /// wave-6v2 (R453-6): the caller-level fact wave-6r's seam guard consults,
    /// recorded once the site facts exist (`record_output_storage_settlement`).
    /// The guard reads a callee ROW; this says whether that row's output-storage
    /// retention is settled by R406-6's certificate at EVERY call of the
    /// position. Absent key = not settled.
    output_storage_settled: FxHashMap<(LocalDefId, usize), bool>,
    /// K18'/OAP-CHILD-ACCESS: the same descendant evidence for callees with no
    /// pinned contract row, kept apart so the row stays the authority wherever
    /// it exists.
    type_backed_children: FxHashMap<LocalDefId, Vec<ReturnedChildRecord>>,
    /// W-C5: raw-pointer parameters whose pointee reaches no pointer.
    pointer_free_parameters: FxHashSet<(LocalDefId, usize)>,
    /// wave-6r (relay 017): the child-access receipt — one row per callee
    /// position the K18' discharge looked at, with its outcome and, where it
    /// held, the conjunct that refused. Instrument-only.
    pub(crate) child_access: String,
    /// wave-6r (relay 019): the call sites whose returned alias the caller
    /// CONSUMES where it is produced — the result is only read through in the
    /// caller's body. Keyed by (caller, block, statement index of the call).
    consumed_results: FxHashSet<(LocalDefId, u32, u32)>,
    /// wave-6r (relay 021): the (caller, callee, argument) positions whose
    /// Return-only retention is settled at EVERY call in that caller — the
    /// returned alias is discarded or consumed there. The seam reads the
    /// callee row, which cannot see this.
    settled_returned_aliases: FxHashSet<(LocalDefId, LocalDefId, usize)>,
}

#[derive(Clone, Debug)]
struct ReturnedChildRecord {
    callee: ForeignSymbolKey,
    evidence: super::returned_child::ReturnedChildEvidence,
    raw_field_parent: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnedChildSiteEvidence {
    pub(crate) child: Result<super::returned_child::ReturnedChildEvidence, &'static str>,
    pub(crate) raw_field_parent: bool,
}

fn location_label(location: Location) -> String {
    format!(
        "bb{}:s{}",
        location.block.as_u32(),
        location.statement_index
    )
}

fn retention_step(
    location: Location,
    kind: RetentionEventKind,
    detail: impl Into<String>,
) -> RetentionStep {
    RetentionStep {
        location: location_label(location),
        kind,
        detail: detail.into(),
    }
}

fn transparent_operand<'a, 'tcx>(rhs: &'a Rvalue<'tcx>) -> Option<&'a Operand<'tcx>> {
    match rhs {
        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => Some(operand),
        _ => None,
    }
}

fn plain_operand_local(operand: &Operand<'_>) -> Option<Local> {
    operand.place().and_then(|place| place.as_local())
}

/// Does `definition` precede `call` on every path (same block, or through
/// predecessors)?
fn definition_before(body: &Body<'_>, definition: Location, call: Location) -> bool {
    if definition.block == call.block {
        return definition.statement_index < call.statement_index;
    }
    let mut block = call.block;
    let mut visited = FxHashSet::default();
    while visited.insert(block) {
        let predecessors = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(candidate, data)| {
                data.terminator()
                    .successors()
                    .any(|successor| successor == block)
                    .then_some(candidate)
            })
            .collect::<Vec<_>>();
        let [predecessor] = predecessors.as_slice() else { return false };
        if *predecessor == definition.block {
            return true;
        }
        block = *predecessor;
    }
    false
}

fn returned_parent_is_raw_field_load<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    call: Location,
    mut parent: Local,
) -> bool {
    let before = definition_before;
    let mut visited = FxHashSet::default();
    while visited.insert(parent) {
        if !matches!(body.local_decls[parent].ty.kind(), TyKind::RawPtr(..)) {
            return false;
        }
        let mut definitions = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                if let StatementKind::Assign(box (lhs, rhs)) = &statement.kind
                    && lhs.as_local() == Some(parent)
                {
                    definitions.push((
                        Location {
                            block,
                            statement_index,
                        },
                        Some(rhs),
                    ));
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                && destination.as_local() == Some(parent)
            {
                definitions.push((
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    None,
                ));
            }
        }
        let [(definition, Some(rhs))] = definitions.as_slice() else { return false };
        if !before(body, *definition, call) {
            return false;
        }
        let Some(operand) = transparent_operand(rhs) else { return false };
        if !matches!(operand.ty(body, tcx).kind(), TyKind::RawPtr(..)) {
            return false;
        }
        let Some(place) = operand.place() else { return false };
        if let Some(local) = place.as_local() {
            parent = local;
        } else {
            return place
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Field(..)));
        }
    }
    false
}

/// **R476-1 clause (2)+(3) inputs.** Is `container` a stack local of this body
/// that does not escape the frame, and which callees receive its address?
///
/// Conservative by construction: the container may appear only as the base of
/// a field access (`container.f`, no `Deref` in the projection) or as the
/// operand of an address-of whose result is passed as a call argument and used
/// nowhere else. Any other appearance — a whole-value read or move, a return,
/// an address stored anywhere, an address reaching a non-call use — answers
/// `None`, and the retention hold stands.
/// **R477-4a.** Every local whose provenance the value stored from `source`
/// carries: `source` itself, the walk's `root`, and every alias ancestor
/// reaching `source` (`_b = _a` copies, `_b = &mut *_a` reborrows — the
/// `Transparent` chain and every other edge the walk records).
/// **R477-4b (relay 046).** Is this body's retaining store a store INTO a
/// fresh allocation whose only escape is back into the analysed parameter's
/// own subgraph?
///
/// bzip2 `BZ2_bzCompressInit` is the shape: `s = alloc(..); s->strm = strm;
/// strm->state = s`. The retained address is then reachable only through the
/// container, whose frame-confinement the caller has already proved, so the
/// caller's frame bounds it too.
///
/// Fails closed: the allocation must come from a DIRECTLY called, named
/// allocator (an indirect call through a function pointer proves nothing
/// about freshness), it must be assigned exactly once, and every other
/// appearance of it must be a store into a place rooted at the parameter.
fn retains_only_into_a_fresh_allocation<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    parameter: Local,
    target: Local,
) -> bool {
    let allocator = |callee: &rustc_middle::mir::Operand<'tcx>| {
        let Some((did, _)) = callee.const_fn_def() else { return false };
        let path = tcx.def_path_str(did);
        let name = path.rsplit("::").next().unwrap_or(&path).to_owned();
        super::allocator_contract::CONTRACTS
            .iter()
            .any(|contract| contract.allocators.iter().any(|a| a.name == name))
    };
    // The locals that hold the fresh block: a named allocator's destination,
    // closed under the casts and copies c2rust puts between the call and the
    // typed local (`_t = malloc(..); _s = _t as *mut T`).
    let mut block = FxHashSet::default();
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call {
                func, destination, ..
            } = &terminator.kind
            && destination.projection.is_empty()
            && allocator(func)
        {
            block.insert(destination.local);
        }
    }
    if block.is_empty() {
        return false;
    }
    loop {
        let before = block.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else { continue };
                if !lhs.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) = rhs
                    && operand.place().is_some_and(|place| {
                        place.projection.is_empty() && block.contains(&place.local)
                    })
                {
                    block.insert(lhs.local);
                }
            }
        }
        if block.len() == before {
            break;
        }
    }
    if !block.contains(&target) {
        return false;
    }
    // Every other appearance of the block must be a store into the parameter's
    // own subgraph (`(*strm).state = s`) or a field write through the block
    // itself (`(*s).strm = strm`, the retaining store this discharges).
    let mut escapes = false;
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else { continue };
            if lhs.projection.is_empty() && block.contains(&lhs.local) {
                // A definition inside the chain, admitted above.
                continue;
            }
            let into_the_parameter = lhs.local == parameter
                && lhs
                    .projection
                    .first()
                    .is_some_and(|p| matches!(p, ProjectionElem::Deref));
            let into_the_block = block.contains(&lhs.local);
            let mentions = |place: &rustc_middle::mir::Place<'tcx>| {
                place.projection.is_empty() && block.contains(&place.local)
            };
            match rhs {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                    if operand.place().as_ref().is_some_and(mentions)
                        && !into_the_parameter
                        && !into_the_block
                    {
                        escapes = true;
                    }
                }
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    if mentions(place) {
                        escapes = true;
                    }
                }
                Rvalue::Aggregate(_, operands) => {
                    if operands
                        .iter()
                        .any(|o| o.place().as_ref().is_some_and(mentions))
                    {
                        escapes = true;
                    }
                }
                _ => {}
            }
        }
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
        {
            if args.iter().any(|argument| {
                argument.node.place().is_some_and(|place| {
                    place.projection.is_empty() && block.contains(&place.local)
                })
            }) {
                escapes = true;
            }
            if destination.local == RETURN_PLACE && block.contains(&destination.local) {
                escapes = true;
            }
        }
    }
    !escapes && !block.contains(&RETURN_PLACE)
}

fn provenance_ancestors(
    aliases: &[(Local, Local, RetentionStep)],
    root: Local,
    source: Local,
) -> FxHashSet<Local> {
    let mut set = FxHashSet::from_iter([source, root]);
    loop {
        let before = set.len();
        for (from, to, _) in aliases {
            if set.contains(to) {
                set.insert(*from);
            }
        }
        if set.len() == before {
            return set;
        }
    }
}

fn container_frame_confinement<'tcx>(
    body: &Body<'tcx>,
    container: Local,
) -> Option<Vec<(LocalDefId, usize)>> {
    if container == RETURN_PLACE || container.as_usize() <= body.arg_count {
        return None;
    }
    // Locals holding the container's address: `&container` / `&raw mut
    // container`, and — to a fixpoint — every reborrow or copy of one
    // (`_12 = &mut (*_13)` is what a call argument actually passes).
    let mut addresses = FxHashSet::default();
    loop {
        let before = addresses.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else { continue };
                if !lhs.projection.is_empty() {
                    continue;
                }
                let takes_address = match rhs {
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        (place.local == container
                            && !place
                                .projection
                                .iter()
                                .any(|p| matches!(p, ProjectionElem::Deref)))
                            || (addresses.contains(&place.local)
                                && place.projection.len() == 1
                                && matches!(place.projection[0], ProjectionElem::Deref))
                    }
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                        operand.place().is_some_and(|place| {
                            place.projection.is_empty() && addresses.contains(&place.local)
                        })
                    }
                    _ => false,
                };
                if takes_address {
                    addresses.insert(lhs.local);
                }
            }
        }
        if addresses.len() == before {
            break;
        }
    }
    let mut callees = Vec::new();
    let mut escapes = false;
    // `true` when this appearance of the container (or of its address) is one
    // the confinement does not admit.
    let leaks = |place: &rustc_middle::mir::Place<'tcx>, addresses: &FxHashSet<Local>| {
        (place.local == container
            && (place.projection.is_empty()
                || place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref))))
            || addresses.contains(&place.local)
    };
    // Writing the container — `container = <init>`, `container.f = ..` — is
    // not an escape; only a whole-value READ of it is (that copies the stored
    // pointer out of the frame's storage). An address local appearing as a
    // write target is still an escape, which `leaks` keeps.
    let leaks_written = |place: &rustc_middle::mir::Place<'tcx>, addresses: &FxHashSet<Local>| {
        (place.local == container
            && place
                .projection
                .iter()
                .any(|p| matches!(p, ProjectionElem::Deref)))
            || addresses.contains(&place.local)
    };
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            match &statement.kind {
                StatementKind::Assign(box (lhs, rhs)) => {
                    if addresses.contains(&lhs.local) && lhs.projection.is_empty() {
                        // An address definition, admitted by the fixpoint
                        // above; its operand is the container or another
                        // address, never a leak.
                        continue;
                    }
                    if addresses.contains(&lhs.local) {
                        // The address is (re)defined; only the address-of form
                        // above is admitted, anything else hides it.
                        if !matches!(rhs, Rvalue::Ref(..) | Rvalue::RawPtr(..)) {
                            escapes = true;
                        }
                        continue;
                    }
                    escapes |= leaks_written(lhs, &addresses);
                    match rhs {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                            if place.local != container {
                                escapes |= leaks(place, &addresses);
                            }
                        }
                        Rvalue::Use(operand)
                        | Rvalue::Cast(_, operand, _)
                        | Rvalue::Repeat(operand, _) => {
                            if let Some(place) = operand.place() {
                                escapes |= leaks(&place, &addresses);
                            }
                        }
                        Rvalue::Aggregate(_, operands) => {
                            for operand in operands {
                                if let Some(place) = operand.place() {
                                    escapes |= leaks(&place, &addresses);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => escapes |= leaks(place, &addresses),
                _ => {}
            }
        }
        let Some(terminator) = &data.terminator else { continue };
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let callee = func.const_fn_def().and_then(|(did, _)| did.as_local());
                for (index, argument) in args.iter().enumerate() {
                    let Some(place) = argument.node.place() else { continue };
                    if addresses.contains(&place.local) && place.projection.is_empty() {
                        match callee {
                            // The certificate for this position is what
                            // clause (3) consults; a foreign or indirect
                            // callee has none, so the hold stands.
                            Some(callee) => callees.push((callee, index)),
                            None => escapes = true,
                        }
                        continue;
                    }
                    escapes |= leaks(&place, &addresses);
                }
                escapes |= leaks_written(destination, &addresses);
            }
            TerminatorKind::Return => {
                if addresses.contains(&RETURN_PLACE) {
                    escapes = true;
                }
            }
            _ => {}
        }
    }
    (!escapes).then_some(callees)
}

fn collect_retention_facts<'tcx>(
    program: &RustProgram<'tcx>,
    function: LocalDefId,
    root: Local,
    argument_index: Option<usize>,
    body: &Body<'tcx>,
    children: &[ReturnedChildRecord],
    prior: &RetentionPriorPass,
) -> RetentionBodyFacts {
    let tcx = program.tcx;
    let function_path = tcx.def_path_str(function.to_def_id());
    let mut definitions = vec![0usize; body.local_decls.len()];
    let mut aliases = Vec::<(Local, Local, RetentionStep)>::new();
    // wave-6v2 (R407-11): a local callee that only RETURNS its argument makes
    // the call's destination an alias of that argument in this body; a local
    // callee that only stores its argument through output parameters supplied
    // from this body's frame-confined locals (or this body's own output
    // parameters) is discharged here, its confined field reads continuing the
    // walk and its parameter stores transposing to this body's.
    let mut discharges = FxHashMap::<(Location, usize), OutputDischarge>::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        let call = Location {
            block,
            statement_index: data.statements.len(),
        };
        let Some(callee_did) = operand_callee(func) else { continue };
        if core_pointer_method(tcx, callee_did) == Some(CorePointerMethod::Derive)
            && let Some(source) = args
                .first()
                .and_then(|receiver| receiver.node.place())
                .and_then(|place| place.as_local())
            && matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
            && let Some(destination) = destination.as_local()
            && matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
            // Composition with wave-6r (`070164b9`, main 036 claim 1): a derived
            // result the function RETURNS keeps the open reading — no alias edge,
            // so the rebind is not a positive retention of the parameter.
            && !crate::bo_rewriter::wave6r_child_access::result_returned(body, destination)
        {
            aliases.push((
                source,
                destination,
                retention_step(
                    call,
                    RetentionEventKind::Transparent,
                    format!(
                        "{} _{}->_{}",
                        tcx.def_path_str(callee_did),
                        source.as_u32(),
                        destination.as_u32()
                    ),
                ),
            ));
        }
        let Some(callee) = callee_did.as_local() else {
            continue;
        };
        let operands = args
            .iter()
            .map(|argument| argument.node.clone())
            .collect::<Vec<_>>();
        for (index, argument) in args.iter().enumerate() {
            let Some(source) = argument.node.place().and_then(|place| place.as_local()) else {
                continue;
            };
            if !matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..)) {
                continue;
            }
            if let Some(outputs) = prior.output_storage_only.get(&(callee, index)) {
                let discharge = output_discharge(tcx, body, &operands, source, outputs, call);
                if discharge.ok {
                    for &(argument, dest, at) in &discharge.field_reads {
                        aliases.push((
                            argument,
                            dest,
                            retention_step(
                                at,
                                RetentionEventKind::ReturnedAlias,
                                format!(
                                    "{} arg{index} confined-field-read _{}->_{}",
                                    tcx.def_path_str(callee.to_def_id()),
                                    argument.as_u32(),
                                    dest.as_u32()
                                ),
                            ),
                        ));
                    }
                }
                discharges.insert((call, index), discharge);
            }
            if !prior.returning.contains(&(callee, index)) {
                continue;
            }
            let Some(destination) = destination.as_local() else { continue };
            if !matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..)) {
                continue;
            }
            aliases.push((
                source,
                destination,
                retention_step(
                    call,
                    RetentionEventKind::ReturnedAlias,
                    format!(
                        "{} arg{index} returns _{}->_{}",
                        tcx.def_path_str(callee.to_def_id()),
                        source.as_u32(),
                        destination.as_u32()
                    ),
                ),
            ));
        }
    }

    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                continue;
            };
            if let Some(destination) = lhs.as_local() {
                definitions[destination.index()] += 1;
                if let Some(source) = transparent_operand(rhs).and_then(plain_operand_local)
                    && matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                    && matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                {
                    aliases.push((
                        source,
                        destination,
                        retention_step(
                            location,
                            RetentionEventKind::Transparent,
                            format!("_{}->_{}", source.as_u32(), destination.as_u32()),
                        ),
                    ));
                }
                // wave-6v2 (R412-1): the address of a place UNDER a pointer
                // (`&raw mut (*s).extra`, `&mut (*s).f`) is a pointer derived
                // from that pointer's referent — an alias for every sink that
                // follows (a global store of it retains the argument).
                if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rhs
                    && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    && matches!(
                        body.local_decls[place.local].ty.kind(),
                        TyKind::RawPtr(..) | TyKind::Ref(..)
                    )
                    && matches!(
                        body.local_decls[destination].ty.kind(),
                        TyKind::RawPtr(..) | TyKind::Ref(..)
                    )
                {
                    aliases.push((
                        place.local,
                        destination,
                        retention_step(
                            location,
                            RetentionEventKind::ReturnedAlias,
                            format!(
                                "address-derivation _{}->_{}",
                                place.local.as_u32(),
                                destination.as_u32()
                            ),
                        ),
                    ));
                }
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && let Some(destination) = destination.as_local()
        {
            definitions[destination.index()] += 1;
        }
    }
    for record in children {
        let child = &record.evidence;
        if let (
            super::returned_child::ChildRoot::Local(parent),
            super::returned_child::ChildRoot::Local(destination),
        ) = (&child.parent, &child.destination)
            && matches!(body.local_decls[*parent].ty.kind(), TyKind::RawPtr(..))
            && matches!(body.local_decls[*destination].ty.kind(), TyKind::RawPtr(..))
        {
            aliases.push((
                *parent,
                *destination,
                retention_step(
                    child.key.call,
                    RetentionEventKind::ReturnedAlias,
                    format!(
                        "{} arg{} _{}->_{}",
                        record.callee.path,
                        child.key.parent_argument_index,
                        parent.as_u32(),
                        destination.as_u32()
                    ),
                ),
            ));
        }
        for edge in &child.edges {
            if matches!(body.local_decls[edge.from].ty.kind(), TyKind::RawPtr(..))
                && matches!(body.local_decls[edge.to].ty.kind(), TyKind::RawPtr(..))
            {
                aliases.push((
                    edge.from,
                    edge.to,
                    retention_step(
                        edge.location,
                        RetentionEventKind::ReturnedAlias,
                        format!(
                            "child-edge:{:?}:_{}->_{}",
                            edge.kind,
                            edge.from.as_u32(),
                            edge.to.as_u32()
                        ),
                    ),
                ));
            }
        }
    }

    let mut reachable = BTreeSet::from([root.as_u32()]);
    loop {
        let before = reachable.len();
        for (source, destination, _) in &aliases {
            if reachable.contains(&source.as_u32()) {
                reachable.insert(destination.as_u32());
            }
        }
        if reachable.len() == before {
            break;
        }
    }
    let is_reachable = |local: Local| reachable.contains(&local.as_u32());
    // R476-1 clause (1): MIR liveness, so "dead after the store" is the real
    // property and not a syntactic proxy. Built once per body, lazily, because
    // only a field store consults it.
    let liveness = std::cell::RefCell::new(
        None::<rustc_mir_dataflow::ResultsCursor<'_, '_, crate::analyses::liveness::MaybeLiveLocals>>,
    );
    let live_after = |location: Location, local: Local| {
        let mut slot = liveness.borrow_mut();
        let cursor = slot.get_or_insert_with(|| {
            rustc_mir_dataflow::Analysis::iterate_to_fixpoint(
                crate::analyses::liveness::MaybeLiveLocals,
                tcx,
                body,
                None,
            )
            .into_results_cursor(body)
        });
        cursor.seek_before_primary_effect(location);
        cursor.get().contains(local)
    };

    let mut facts = RetentionBodyFacts {
        function,
        function_path,
        argument_index,
        steps: aliases
            .iter()
            .filter(|(source, _, _)| is_reachable(*source))
            .map(|(_, _, step)| step.clone())
            .collect(),
        retains: Vec::new(),
        unknowns: BTreeMap::new(),
        frame_bounded: Vec::new(),
        retains_into_fresh_allocation: Vec::new(),
        dependencies: Vec::new(),
    };
    for record in children {
        let child = &record.evidence;
        let parent = match &child.parent {
            super::returned_child::ChildRoot::Local(parent) => Some(*parent),
            super::returned_child::ChildRoot::Unknown { local, .. } => *local,
        };
        if !parent.is_some_and(is_reachable) {
            continue;
        }
        for sink in &child.outward_sinks {
            facts.retains.push(retention_step(
                sink.location,
                RetentionEventKind::ReturnedChildSink,
                format!(
                    "{} arg{} child _{} {:?}",
                    record.callee.path,
                    child.key.parent_argument_index,
                    sink.local.as_u32(),
                    sink.kind
                ),
            ));
        }
        let reason = match child.initial.state {
            super::return_alias::ReturnUseState::Unused => None,
            super::return_alias::ReturnUseState::Used => {
                Some(RetentionUnknownReason::ReturnedAliasUsed)
            }
            super::return_alias::ReturnUseState::Unknown => {
                Some(RetentionUnknownReason::ReturnedAliasUnknown)
            }
        };
        if let Some(reason) = reason {
            facts
                .unknowns
                .entry(reason)
                .or_default()
                .push(retention_step(
                    child.key.call,
                    RetentionEventKind::ReturnedAlias,
                    format!(
                        "{} arg{} result={};access={:?}",
                        record.callee.path,
                        child.key.parent_argument_index,
                        child.initial.state.key(),
                        child.access
                    ),
                ));
        }
    }

    for local in body.local_decls.indices() {
        if local != root && is_reachable(local) && definitions[local.index()] > 1 {
            facts
                .unknowns
                .entry(RetentionUnknownReason::MultiDef)
                .or_default()
                .push(RetentionStep {
                    location: "body".to_owned(),
                    kind: RetentionEventKind::MultiDef,
                    detail: format!(
                        "_{} has {} definitions",
                        local.as_u32(),
                        definitions[local.index()]
                    ),
                });
        }
    }

    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                continue;
            };
            if is_reachable(lhs.local) && !lhs.projection.is_empty() {
                facts.steps.push(retention_step(
                    location,
                    RetentionEventKind::DereferenceOnly,
                    format!("access through _{}", lhs.local.as_u32()),
                ));
            }
            // R210(c)'s local query treats an aggregate operand as stored
            // pointer evidence even if a later whole-aggregate move hides
            // the field write. Parameter-summary behavior stays unchanged;
            // the local query also uses this mode for dependency roots.
            if argument_index.is_none()
                && let Rvalue::Aggregate(_, operands) = rhs
            {
                for operand in operands {
                    if let Some(source) =
                        plain_operand_local(operand).filter(|source| is_reachable(*source))
                    {
                        facts.retains.push(retention_step(
                            location,
                            RetentionEventKind::FieldOrGlobalStore,
                            format!(
                                "store _{} in aggregate _{}",
                                source.as_u32(),
                                lhs.local.as_u32()
                            ),
                        ));
                    }
                }
            }
            // R416-11: a cast of a reachable POINTER to a non-pointer type
            // (`p as usize`) is an integer image of the alias — an exposed
            // address the walk cannot follow, which a store elsewhere may keep
            // and a later cast may revive. It is an open step (a hand-out) for
            // every certificate; a cast that is itself stored or returned is
            // the store or the return below, seen as before.
            if let Rvalue::Cast(_, operand, target) = rhs
                && let Some(source) = plain_operand_local(operand)
                && is_reachable(source)
                && matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                && !matches!(
                    target.kind(),
                    TyKind::RawPtr(..) | TyKind::Ref(..) | TyKind::FnPtr(..)
                )
                && lhs.as_local().is_some_and(|local| local != RETURN_PLACE)
            {
                let step = retention_step(
                    location,
                    RetentionEventKind::Nontransparent,
                    format!(
                        "integer image _{}->_{}",
                        source.as_u32(),
                        lhs.local.as_u32()
                    ),
                );
                facts
                    .unknowns
                    .entry(RetentionUnknownReason::NontransparentDef)
                    .or_default()
                    .push(step.clone());
                facts.steps.push(step);
                continue;
            }
            let Some(source_place) = transparent_operand(rhs).and_then(Operand::place) else {
                continue;
            };
            if is_reachable(source_place.local) && !source_place.projection.is_empty() {
                facts.steps.push(retention_step(
                    location,
                    RetentionEventKind::DereferenceOnly,
                    format!("read through _{}", source_place.local.as_u32()),
                ));
                continue;
            }
            let Some(source) = source_place.as_local().filter(|local| is_reachable(*local)) else {
                continue;
            };
            if lhs.local == RETURN_PLACE && lhs.projection.is_empty() {
                facts.retains.push(retention_step(
                    location,
                    RetentionEventKind::Return,
                    format!("return _{}", source.as_u32()),
                ));
            } else if !lhs.projection.is_empty() {
                // wave-6v2 (R407-11): a store through a transparent alias of
                // an output parameter (`*(pdest as *mut *mut T) = ..`) is a
                // store through that parameter.
                let storage_root =
                    if lhs.local.as_usize() > 0 && lhs.local.as_usize() <= body.arg_count {
                        Some(lhs.local)
                    } else {
                        parameter_alias_root(body, &aliases, lhs.local)
                    };
                let output_storage = storage_root.is_some()
                    && matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
                let storage_root = storage_root.unwrap_or(lhs.local);
                let (reason, kind) = if output_storage {
                    (
                        RetentionUnknownReason::OutputStorage,
                        RetentionEventKind::OutputStorage,
                    )
                } else {
                    (
                        RetentionUnknownReason::FieldOrGlobalStore,
                        RetentionEventKind::FieldOrGlobalStore,
                    )
                };
                let step = retention_step(
                    location,
                    kind,
                    format!(
                        "store _{} through _{}",
                        source.as_u32(),
                        storage_root.as_u32()
                    ),
                );
                // **R476-1 (USER, relay 045), clauses (1)–(3).** A store into
                // a field of a non-escaping stack local of THIS frame, after
                // which the subject is dead, is bounded by the frame. The
                // callees that receive the container's address are carried so
                // that `evaluate_retention` can require their certificates.
                if !output_storage
                    && !lhs
                        .projection
                        .iter()
                        .any(|p| matches!(p, ProjectionElem::Deref))
                    && let Some(callees) = container_frame_confinement(body, storage_root)
                    // **R477-4a (main 060d).** Condition (1) is asked of the
                    // provenance chain's ROOT, not only of the stored operand:
                    // a reborrowed subject is dead only when every ancestor
                    // whose provenance the stored pointer carries is dead. The
                    // ancestor set is closed over the walk's own alias edges,
                    // a superset of the `Transparent` copy/reborrow chain, so
                    // the question asked here is never weaker than the ruling.
                    && provenance_ancestors(&aliases, root, source)
                        .into_iter()
                        .all(|ancestor| !live_after(location, ancestor))
                {
                    facts.frame_bounded.push(FrameBoundedStore {
                        step: step.clone(),
                        container: storage_root,
                        callees,
                    });
                }
                // R477-4b: the callee-side half — this store puts the
                // parameter's provenance into a fresh allocation that escapes
                // only back into the parameter, so a caller that bounds the
                // parameter's container bounds this too.
                if !output_storage
                    && let Some(index) = argument_index
                    && retains_only_into_a_fresh_allocation(
                        tcx,
                        body,
                        Local::from_usize(index + 1),
                        storage_root,
                    )
                {
                    facts.retains_into_fresh_allocation.push(step.clone());
                }
                facts.retains.push(step.clone());
                facts.unknowns.entry(reason).or_default().push(step);
            }
        }

        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        let terminator = data.terminator();
        let (func, args) = match &terminator.kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => continue,
        };
        for (index, argument) in args.iter().enumerate() {
            let Some(local) = argument.node.place().and_then(|place| place.as_local()) else {
                continue;
            };
            if !is_reachable(local) {
                continue;
            }
            // wave-6v2 (R410-3): `core`'s raw-pointer methods are modeled for
            // the SINK walk — a derived pointer (`offset`, `add`, `cast`, ..)
            // is an alias of the receiver (the edge is in `aliases`, so a store
            // of it is a sink here), and a `write*` of a reachable VALUE
            // through the receiver is a store through it — while the call
            // itself stays the open step it always was for the no-retain
            // CERTIFICATE (the existing T2 tier is unchanged; only the
            // descendant check reads the tag and accepts these steps).
            if let Some(callee) = operand_callee(func)
                && let Some(method) = core_pointer_method(tcx, callee)
            {
                let open = |detail: String, facts: &mut RetentionBodyFacts| {
                    let step = retention_step(location, RetentionEventKind::UnknownCall, detail);
                    facts
                        .unknowns
                        .entry(RetentionUnknownReason::OpenBoundary)
                        .or_default()
                        .push(step.clone());
                    step
                };
                let step = match method {
                    // wave-6r × wave-6v2 seam: hooks 3/4 of the batch-8 line
                    // (`6f521bfc`, `32f42251` narrowed by `070164b9`) prove
                    // that a core `is_null`, or an offset-family call whose
                    // result the function does not return, RETAINS NOTHING —
                    // a known no-retain step, not an open boundary. Outside
                    // that set (`wrapping_*`, `byte_*`, `read`, `addr`, ..)
                    // the call stays the open step wave-6v2 models.
                    CorePointerMethod::Derive | CorePointerMethod::Observe
                        if crate::bo_rewriter::wave6r_child_access::core_pointer_known_no_retain(
                            tcx, body, data, callee,
                        ) =>
                    {
                        retention_step(
                            location,
                            RetentionEventKind::KnownNoRetainCall,
                            format!(
                                "{} arg{index} core-no-retain {CORE_POINTER_METHOD_TAG}",
                                tcx.def_path_str(callee)
                            ),
                        )
                    }
                    // A derivation whose result the function RETURNS keeps the
                    // open reading (wave-6r's `070164b9`) and gets NO alias
                    // edge — so the descendant walk cannot see the hand-out
                    // through the return. The step therefore drops the tag:
                    // `descendant_free` accepts a tagged core step because its
                    // derived pointer is an alias whose sinks are visible, and
                    // that premise does not hold here.
                    CorePointerMethod::Derive
                        if matches!(
                            &terminator.kind,
                            TerminatorKind::Call { destination, .. }
                                if destination.as_local().is_some_and(|result| {
                                    crate::bo_rewriter::wave6r_child_access::result_returned(
                                        body, result,
                                    )
                                })
                        ) =>
                    {
                        open(
                            format!(
                                "{} arg{index} returned-derivation",
                                tcx.def_path_str(callee)
                            ),
                            &mut facts,
                        )
                    }
                    CorePointerMethod::Derive | CorePointerMethod::Observe => open(
                        format!(
                            "{} arg{index} {CORE_POINTER_METHOD_TAG}",
                            tcx.def_path_str(callee)
                        ),
                        &mut facts,
                    ),
                    CorePointerMethod::Write if index == 0 => open(
                        format!(
                            "{} receiver {CORE_POINTER_METHOD_TAG}",
                            tcx.def_path_str(callee)
                        ),
                        &mut facts,
                    ),
                    CorePointerMethod::Write => {
                        let receiver = args
                            .first()
                            .and_then(|receiver| receiver.node.place())
                            .and_then(|place| place.as_local());
                        let root = receiver.and_then(|receiver| {
                            if receiver.as_usize() > 0 && receiver.as_usize() <= body.arg_count {
                                Some(receiver)
                            } else {
                                parameter_alias_root(body, &aliases, receiver)
                            }
                        });
                        let (reason, kind) = if root.is_some() {
                            (
                                RetentionUnknownReason::OutputStorage,
                                RetentionEventKind::OutputStorage,
                            )
                        } else {
                            (
                                RetentionUnknownReason::FieldOrGlobalStore,
                                RetentionEventKind::FieldOrGlobalStore,
                            )
                        };
                        let step = retention_step(
                            location,
                            kind,
                            format!(
                                "store _{} through _{}",
                                local.as_u32(),
                                root.or(receiver).map_or(0, |local| local.as_u32())
                            ),
                        );
                        facts.retains.push(step.clone());
                        facts.unknowns.entry(reason).or_default().push(step.clone());
                        step
                    }
                };
                facts.steps.push(step);
                continue;
            }
            let Some(callee) = operand_callee(func) else {
                let step = retention_step(
                    location,
                    RetentionEventKind::UnknownCall,
                    format!("fn-pointer argument {index}"),
                );
                facts
                    .unknowns
                    .entry(RetentionUnknownReason::FnPtrWeb)
                    .or_default()
                    .push(step.clone());
                facts.steps.push(step);
                continue;
            };
            if let Some(local_callee) = callee
                .as_local()
                .filter(|callee| program.functions.contains(callee))
            {
                // wave-6v2 (R407-11): a callee that stores this argument only
                // through its output parameters, each supplied here from a
                // frame-confined local or this body's own output parameter,
                // is discharged at this call; transposed sinks become this
                // body's output-storage sinks.
                let discharge = discharges.get(&(location, index));
                let discharged_by_stack_storage = discharge.is_some_and(|d| d.ok);
                if let Some(discharge) = discharge.filter(|d| d.ok) {
                    for &(source, parameter) in &discharge.transposed {
                        let step = retention_step(
                            location,
                            RetentionEventKind::OutputStorage,
                            format!("store _{} through _{}", source.as_u32(), parameter.as_u32()),
                        );
                        facts.retains.push(step.clone());
                        facts
                            .unknowns
                            .entry(RetentionUnknownReason::OutputStorage)
                            .or_default()
                            .push(step);
                    }
                }
                let continued_returned_alias = prior.returning.contains(&(local_callee, index))
                    && matches!(
                        &terminator.kind,
                        TerminatorKind::Call { destination, .. }
                            if destination.as_local().is_some_and(|destination| {
                                matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                            })
                    );
                let step = retention_step(
                    location,
                    if discharged_by_stack_storage || continued_returned_alias {
                        RetentionEventKind::KnownNoRetainCall
                    } else {
                        RetentionEventKind::LocalCall
                    },
                    format!(
                        "{} arg{index}{}",
                        tcx.def_path_str(callee),
                        if discharged_by_stack_storage {
                            " stack-storage-certificate"
                        } else if continued_returned_alias {
                            " returned-alias-continued"
                        } else {
                            ""
                        }
                    ),
                );
                facts.dependencies.push(RetentionDependency {
                    callee: local_callee,
                    argument_index: index,
                    step: step.clone(),
                    discharged_by_stack_storage,
                    continued_returned_alias,
                });
                facts.steps.push(step);
                continue;
            }
            let key = symbol_key(tcx, callee, &program.functions);
            let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
            let source_ty = argument.node.ty(body, tcx);
            let target = sig
                .inputs()
                .get(index)
                .copied()
                .and_then(|ty| raw_target_type(tcx, ty))
                .or_else(|| {
                    sig.c_variadic
                        .then(|| raw_target_type(tcx, source_ty))
                        .flatten()
                });
            let Some(target) = target else {
                let step = retention_step(
                    location,
                    RetentionEventKind::UnknownCall,
                    format!("{} arg{index} target-unresolved", key.symbol),
                );
                facts
                    .unknowns
                    .entry(RetentionUnknownReason::CalleeUnresolved)
                    .or_default()
                    .push(step.clone());
                facts.steps.push(step);
                continue;
            };
            match super::raw_boundary_contracts::classify_contract(&key, index, &target) {
                Ok(contract) => {
                    if contract.returns_alias_of == Some(index)
                        && children
                            .iter()
                            .filter(|record| {
                                record.callee == key
                                    && record.evidence.key.call == location
                                    && record.evidence.key.parent_argument_index == index
                            })
                            .count()
                            != 1
                    {
                        facts
                            .unknowns
                            .entry(RetentionUnknownReason::ReturnedAliasUnknown)
                            .or_default()
                            .push(retention_step(
                                location,
                                RetentionEventKind::ReturnedAlias,
                                format!(
                                    "{} arg{index} child-evidence-missing-or-ambiguous",
                                    key.path
                                ),
                            ));
                    }
                    let (kind, detail) = match contract.ownership {
                        super::raw_boundary_contracts::OwnershipContract::Consume => {
                            (RetentionEventKind::Free, "consume")
                        }
                        _ => (RetentionEventKind::KnownNoRetainCall, "no-retain"),
                    };
                    facts.steps.push(retention_step(
                        location,
                        kind,
                        format!("{} arg{index} {detail}", key.symbol),
                    ));
                }
                Err(_)
                    if crate::bo_rewriter::wave6r_child_access::core_pointer_known_no_retain(
                        tcx, body, data, callee,
                    ) =>
                {
                    facts.steps.push(retention_step(
                        location,
                        RetentionEventKind::KnownNoRetainCall,
                        format!("{} arg{index} core-no-retain", key.symbol),
                    ));
                }
                Err(error) => {
                    let step = retention_step(
                        location,
                        RetentionEventKind::UnknownCall,
                        format!("{} arg{index} {error:?}", key.symbol),
                    );
                    facts
                        .unknowns
                        .entry(RetentionUnknownReason::OpenBoundary)
                        .or_default()
                        .push(step.clone());
                    facts.steps.push(step);
                }
            }
        }
    }

    facts.steps.sort();
    facts.steps.dedup();
    facts.retains.sort();
    facts.retains.dedup();
    for steps in facts.unknowns.values_mut() {
        steps.sort();
        steps.dedup();
    }
    facts.dependencies.sort_by_key(|dependency| {
        (
            dependency.callee.local_def_index.as_u32(),
            dependency.argument_index,
            dependency.step.clone(),
        )
    });
    facts.dependencies.dedup();
    facts
}

/// wave-6v2 (R407-11): the verdict a callee parameter carries once its
/// output-storage sinks are discharged at a call — its unknowns and its own
/// dependencies, nothing else.
fn residual_after_discharge(
    facts: &RetentionBodyFacts,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    attested: bool,
) -> Option<RetentionVerdict> {
    residual_after_discharge_in(facts, rows, None, attested, 0)
}

/// [`residual_after_discharge`] with the fact table, so a dependency that was
/// itself discharged or continued contributes ITS residual rather than its row;
/// the depth bound guards a cycle of discharged calls.
fn residual_after_discharge_in(
    facts: &RetentionBodyFacts,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    all_facts: Option<&FxHashMap<(LocalDefId, usize), RetentionBodyFacts>>,
    attested: bool,
    depth: usize,
) -> Option<RetentionVerdict> {
    if !attested {
        return Some(RetentionVerdict::Unknown {
            reason: RetentionUnknownReason::AttestationAbsent,
            frontier: facts.steps.clone(),
        });
    }
    if let Some((&reason, frontier)) = facts
        .unknowns
        .iter()
        .find(|(reason, _)| **reason != RetentionUnknownReason::OutputStorage)
    {
        return Some(RetentionVerdict::Unknown {
            reason,
            frontier: frontier.clone(),
        });
    }
    for dependency in &facts.dependencies {
        let key = (dependency.callee, dependency.argument_index);
        let verdict = if (dependency.discharged_by_stack_storage
            || dependency.continued_returned_alias)
            && depth < 8
            && let Some(callee_facts) = all_facts.and_then(|all| all.get(&key))
        {
            residual_after_discharge_in(callee_facts, rows, all_facts, attested, depth + 1)
        } else {
            rows.get(&key).cloned()
        };
        match verdict {
            Some(RetentionVerdict::NoRetain { .. }) => {}
            Some(RetentionVerdict::Retains { sink, path }) => {
                return Some(RetentionVerdict::Retains { sink, path });
            }
            _ => {
                return Some(RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::LocalSummaryUnknown,
                    frontier: vec![dependency.step.clone()],
                });
            }
        }
    }
    Some(RetentionVerdict::NoRetain {
        certificate: RetentionCertificate {
            function: facts.function_path.clone(),
            argument_index: facts.argument_index?,
            steps: facts.steps.clone(),
            attestation: "stack-storage-certificate",
            frame_bounded: None,
        },
    })
}

fn direct_verdict(facts: &RetentionBodyFacts, attested: bool) -> RetentionVerdict {
    if let Some(sink) = facts.retains.first().cloned() {
        return RetentionVerdict::Retains {
            sink: sink.clone(),
            path: vec![sink],
        };
    }
    if !attested {
        return RetentionVerdict::Unknown {
            reason: RetentionUnknownReason::AttestationAbsent,
            frontier: facts.steps.clone(),
        };
    }
    if let Some((&reason, frontier)) = facts.unknowns.first_key_value() {
        return RetentionVerdict::Unknown {
            reason,
            frontier: frontier.clone(),
        };
    }
    let Some(argument_index) = facts.argument_index else {
        return RetentionVerdict::Unknown {
            reason: RetentionUnknownReason::LocalSummaryUnknown,
            frontier: facts.steps.clone(),
        };
    };
    RetentionVerdict::NoRetain {
        certificate: RetentionCertificate {
            function: facts.function_path.clone(),
            argument_index,
            steps: facts.steps.clone(),
            attestation: "closed_world_frozen_graph",
            frame_bounded: None,
        },
    }
}

/// **R476-1 (USER ruling, relay 045).** The receipt when this body's every
/// retaining step is frame-bounded and every container callee is certified.
///
/// `None` is the answer whenever anything is unproved: a retaining step that
/// is not a frame-bounded store, a parameter-less body (no certificate to
/// mint), a container callee whose own row is `Retains` or `Unknown`, or a
/// body with no retaining step at all (which needs no discharge).
fn frame_bounded_discharge(
    facts: &RetentionBodyFacts,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    all: &FxHashMap<(LocalDefId, usize), RetentionBodyFacts>,
) -> Option<String> {
    if facts.retains.is_empty() || facts.argument_index.is_none() {
        return None;
    }
    if !facts.retains.iter().all(|step| {
        facts
            .frame_bounded
            .iter()
            .any(|bounded| &bounded.step == step)
    }) {
        return None;
    }
    let mut containers = Vec::new();
    let mut callees = Vec::new();
    for bounded in &facts.frame_bounded {
        containers.push(format!("_{}", bounded.container.as_u32()));
        for &(callee, argument) in &bounded.callees {
            match rows.get(&(callee, argument)) {
                Some(RetentionVerdict::NoRetain { .. }) => {}
                // **R477-4b.** A retaining container callee is admissible when
                // every one of its retaining steps stores into a fresh
                // allocation that escapes only back into the container.
                Some(RetentionVerdict::Retains { .. })
                    if all.get(&(callee, argument)).is_some_and(|callee_facts| {
                        !callee_facts.retains.is_empty()
                            && callee_facts.retains.iter().all(|step| {
                                callee_facts.retains_into_fresh_allocation.contains(step)
                            })
                    }) => {}
                _ => return None,
            }
            callees.push(format!("{}:arg{argument}", callee.local_def_index.as_u32()));
        }
    }
    containers.sort();
    containers.dedup();
    callees.sort();
    callees.dedup();
    Some(format!(
        "retention-discharged:frame-bounded(subject=arg{}, container={}, callees={})",
        facts.argument_index?,
        containers.join("+"),
        if callees.is_empty() {
            "none".to_owned()
        } else {
            callees.join("+")
        }
    ))
}

fn evaluate_retention(
    facts: &FxHashMap<(LocalDefId, usize), RetentionBodyFacts>,
    attested: bool,
) -> FxHashMap<(LocalDefId, usize), RetentionVerdict> {
    let mut rows = facts
        .iter()
        .map(|(&key, facts)| (key, direct_verdict(facts, attested)))
        .collect::<FxHashMap<_, _>>();
    let mut keys = facts.keys().copied().collect::<Vec<_>>();
    keys.sort_by_key(|(function, argument)| (function.local_def_index.as_u32(), *argument));
    for _ in 0..=keys.len() {
        let previous = rows.clone();
        for key in &keys {
            let fact = &facts[key];
            let direct = direct_verdict(fact, attested);
            // wave-6v2 (R407-11): a dependency discharged by the stack-storage
            // certificate contributes only the callee's residual verdict.
            let dependency_verdict = |dependency: &RetentionDependency| {
                let row = previous.get(&(dependency.callee, dependency.argument_index));
                if (dependency.discharged_by_stack_storage || dependency.continued_returned_alias)
                    && let Some(callee_facts) =
                        facts.get(&(dependency.callee, dependency.argument_index))
                {
                    residual_after_discharge_in(callee_facts, &previous, Some(facts), attested, 0)
                } else {
                    row.cloned()
                }
            };
            // **R476-1 (USER, relay 045).** Every retaining step of this body
            // is a field store into a non-escaping stack local of its own
            // frame, after which the subject is dead (clauses (1)+(2), decided
            // in the walk), and every callee that receives a container's
            // address is certified no-retain at that position (clause (3),
            // decided here because it needs the other rows). Unknown or
            // retaining callee ⇒ no discharge and the hold stands.
            let frame_bounded = frame_bounded_discharge(fact, &previous, facts);
            let next = if let Some(receipt) = frame_bounded {
                RetentionVerdict::NoRetain {
                    certificate: RetentionCertificate {
                        function: fact.function_path.clone(),
                        argument_index: fact.argument_index.unwrap_or_default(),
                        steps: fact.steps.clone(),
                        attestation: "closed_world_frozen_graph",
                        frame_bounded: Some(receipt),
                    },
                }
            } else if matches!(direct, RetentionVerdict::Retains { .. }) {
                direct
            } else if let Some((dependency, sink)) =
                fact.dependencies.iter().find_map(|dependency| {
                    match dependency_verdict(dependency) {
                        Some(RetentionVerdict::Retains { sink, .. }) => Some((dependency, sink)),
                        _ => None,
                    }
                })
            {
                RetentionVerdict::Retains {
                    sink: sink.clone(),
                    path: vec![dependency.step.clone(), sink],
                }
            } else if matches!(direct, RetentionVerdict::Unknown { .. }) {
                direct
            } else if let Some(dependency) = fact.dependencies.iter().find(|dependency| {
                !matches!(
                    dependency_verdict(dependency),
                    Some(RetentionVerdict::NoRetain { .. })
                )
            }) {
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::LocalSummaryUnknown,
                    frontier: vec![dependency.step.clone()],
                }
            } else {
                direct
            };
            rows.insert(*key, next);
        }
        if rows == previous {
            break;
        }
    }
    rows
}

impl RetentionSummaries {
    /// wave-6v2 (R453-6, relay 025 §1): fill the caller-level settled fact.
    /// Called once, after `RawBoundarySiteFacts::derive`, so wave-6r's seam
    /// guard — which has no site facts at its call — can ask the summaries
    /// directly, exactly as it asks `returned_alias_settled`.
    pub(crate) fn record_output_storage_settlement(&mut self, site_facts: &RawBoundarySiteFacts) {
        let positions = site_facts
            .sites
            .iter()
            .filter_map(|site| {
                site.callee_local
                    .map(|callee| (callee, site.key.argument_index))
            })
            .collect::<FxHashSet<_>>();
        for (callee, index) in positions {
            let settled = super::binn_counted::output_storage_settled_at_every_call(
                site_facts, self, callee, index,
            );
            self.output_storage_settled.insert((callee, index), settled);
        }
    }

    /// wave-6v2 (R453-6): is this position's output-storage retention settled by
    /// the stack-storage certificate at every call? `false` until
    /// `record_output_storage_settlement` has run, and for any position with no
    /// inventoried call.
    pub(crate) fn output_storage_settled(&self, callee: LocalDefId, index: usize) -> bool {
        self.output_storage_settled
            .get(&(callee, index))
            .copied()
            .unwrap_or(false)
    }

    /// wave-6v2 (R412-7): does this callee only RETURN the argument — every
    /// positive sink a `return` of it? The returned alias is then the caller's
    /// to account for (its own row continues the walk), and the site is
    /// retention-unknown under the named waiver, exactly as a contract callee
    /// with `returns_alias_of`.
    pub(crate) fn returns_argument_only(&self, callee: LocalDefId, argument_index: usize) -> bool {
        self.facts
            .get(&(callee, argument_index))
            .is_some_and(|facts| {
                !facts.retains.is_empty()
                    && facts
                        .retains
                        .iter()
                        .all(|step| step.kind == RetentionEventKind::Return)
            })
    }

    /// wave-6v2 (R412-7): does this function's row for the parameter record
    /// no write THROUGH the parameter or any alias the walk reached from it
    /// (the walk's `access through` steps are the writes; reads are `read
    /// through`)? A shared view's caller that never writes through the
    /// returned alias cannot be the write-through-shared-view hazard.
    pub(crate) fn no_write_through(&self, function: LocalDefId, argument_index: usize) -> bool {
        self.facts
            .get(&(function, argument_index))
            .is_some_and(|facts| {
                facts.steps.iter().all(|step| {
                    !(step.kind == RetentionEventKind::DereferenceOnly
                        && step.detail.starts_with("access through"))
                })
            })
    }

    /// wave-6v2 (R410-3): does the callee's BODY store no pointer derived from
    /// this argument anywhere but the named confined output positions? Every
    /// positive sink is `store _s through _p` with `p` confined, the walk has
    /// no open step (no unknown call, no fn-pointer, no unresolved callee, no
    /// multi-definition), and every local dependency is descendant-free in
    /// turn: a discharged one has its sinks confined or transposed inside this
    /// body (the transposed ones are this body's retains, checked here), an
    /// undischarged one may have no sink and no open step at all.
    pub(crate) fn descendant_free(
        &self,
        callee: LocalDefId,
        argument_index: usize,
        confined_outputs: &[usize],
    ) -> bool {
        self.descendant_free_in(callee, argument_index, Some(confined_outputs), false, 0)
    }

    fn descendant_free_in(
        &self,
        callee: LocalDefId,
        argument_index: usize,
        confined_outputs: Option<&[usize]>,
        returns_continued: bool,
        depth: usize,
    ) -> bool {
        if depth > 8 {
            return false;
        }
        let Some(facts) = self.facts.get(&(callee, argument_index)) else {
            return false;
        };
        let sink_confined = |step: &RetentionStep| {
            // A `return` of the argument is the caller's alias, accounted in
            // the caller's own walk when the dependency was continued.
            (returns_continued && step.kind == RetentionEventKind::Return)
                || step.kind == RetentionEventKind::OutputStorage
                    && confined_outputs.is_some_and(|outputs| {
                        step.detail
                            .rsplit("through _")
                            .next()
                            .and_then(|local| local.parse::<usize>().ok())
                            .and_then(|local| local.checked_sub(1))
                            .is_some_and(|position| outputs.contains(&position))
                    })
        };
        if !facts.retains.iter().all(sink_confined) {
            return false;
        }
        // A multi-definition alias withholds the no-retain CERTIFICATE (which
        // value a local holds is unknown) but hides no store: every store of
        // or through a reachable local is in `retains`, checked above. Every
        // other open step (an unknown call, a fn-pointer, an unresolved
        // callee, an unaccounted returned alias) may hide one and rejects.
        // A modeled core pointer method is an open step for the CERTIFICATE
        // only: its derived pointer is an alias whose stores are in `retains`.
        if facts.unknowns.iter().any(|(reason, steps)| {
            !matches!(
                reason,
                RetentionUnknownReason::OutputStorage | RetentionUnknownReason::MultiDef
            ) && steps
                .iter()
                .any(|step| !step.detail.ends_with(CORE_POINTER_METHOD_TAG))
        }) {
            return false;
        }
        facts.dependencies.iter().all(|dependency| {
            let confined =
                if dependency.discharged_by_stack_storage || dependency.continued_returned_alias {
                    // Discharged inside this body: the callee's own output
                    // sinks were confined or transposed here.
                    self.facts
                        .get(&(dependency.callee, dependency.argument_index))
                        .map(|callee_facts| {
                            callee_facts
                                .retains
                                .iter()
                                .filter_map(|step| {
                                    step.detail
                                        .rsplit("through _")
                                        .next()
                                        .and_then(|local| local.parse::<usize>().ok())
                                        .and_then(|local| local.checked_sub(1))
                                })
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default()
                } else {
                    Vec::new()
                };
            self.descendant_free_in(
                dependency.callee,
                dependency.argument_index,
                Some(&confined),
                dependency.continued_returned_alias,
                depth + 1,
            )
        })
    }

    /// wave-6v2 (R406-6): the parameter's retention when EVERY positive sink
    /// is a store through an output parameter of the callee itself (`store _s
    /// through _p`): the output-parameter indices those sinks name, and the
    /// verdict the parameter would carry with those sinks discharged — no
    /// retention when the body is otherwise clean, attested and every local
    /// dependency is no-retain; otherwise the first residual unknown (the
    /// existing waiver path); `None` for any other positive sink, including
    /// one reached through a dependency. A caller whose operands at those
    /// positions are frame-confined locals discharges the sinks: the stored
    /// pointer lives exactly as long as the caller's frame.
    pub(crate) fn output_storage_discharge(
        &self,
        callee: LocalDefId,
        argument_index: usize,
    ) -> Option<(Vec<usize>, RetentionVerdict)> {
        let facts = self.facts.get(&(callee, argument_index))?;
        if facts.retains.is_empty()
            || facts
                .retains
                .iter()
                .any(|step| step.kind != RetentionEventKind::OutputStorage)
        {
            return None;
        }
        let mut parameters = Vec::new();
        for step in &facts.retains {
            let local = step
                .detail
                .rsplit("through _")
                .next()?
                .parse::<usize>()
                .ok()?;
            // MIR local `_p` of an argument is 1-based; the position is `p - 1`.
            parameters.push(local.checked_sub(1)?);
        }
        parameters.sort_unstable();
        parameters.dedup();
        let residual_unknown = facts
            .unknowns
            .iter()
            .find(|(reason, _)| **reason != RetentionUnknownReason::OutputStorage)
            .map(|(reason, steps)| (*reason, steps.clone()));
        let dependency_verdicts = facts
            .dependencies
            .iter()
            .map(|dependency| {
                let key = (dependency.callee, dependency.argument_index);
                let verdict = if (dependency.discharged_by_stack_storage
                    || dependency.continued_returned_alias)
                    && let Some(callee_facts) = self.facts.get(&key)
                {
                    residual_after_discharge_in(
                        callee_facts,
                        &self.rows,
                        Some(&self.facts),
                        self.attested,
                        0,
                    )
                } else {
                    self.rows.get(&key).cloned()
                };
                (dependency, verdict)
            })
            .collect::<Vec<_>>();
        if dependency_verdicts
            .iter()
            .any(|(_, verdict)| matches!(verdict, Some(RetentionVerdict::Retains { .. })))
        {
            return None;
        }
        let residual = if !self.attested {
            RetentionVerdict::Unknown {
                reason: RetentionUnknownReason::AttestationAbsent,
                frontier: facts.steps.clone(),
            }
        } else if let Some((reason, frontier)) = residual_unknown {
            RetentionVerdict::Unknown { reason, frontier }
        } else if let Some((dependency, _)) = dependency_verdicts
            .iter()
            .find(|(_, verdict)| !matches!(verdict, Some(RetentionVerdict::NoRetain { .. })))
        {
            RetentionVerdict::Unknown {
                reason: RetentionUnknownReason::LocalSummaryUnknown,
                frontier: vec![dependency.step.clone()],
            }
        } else {
            RetentionVerdict::NoRetain {
                certificate: RetentionCertificate {
                    function: facts.function_path.clone(),
                    argument_index,
                    steps: facts.steps.clone(),
                    attestation: "stack-storage-certificate",
                    frame_bounded: None,
                },
            }
        };
        Some((parameters, residual))
    }

    pub(crate) fn derive(
        program: &RustProgram<'_>,
        origins: Option<&OriginSummaries>,
        attestation: Option<WholeProgramAttestation>,
    ) -> Self {
        let attested = attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        let mut facts = FxHashMap::default();
        let mut returned_children = FxHashMap::default();
        let mut type_backed_children = FxHashMap::default();
        let mut pointer_free_parameters = FxHashSet::default();
        for &function in &program.functions {
            pointer_free_parameters.extend(
                super::returned_child_descent::pointer_free_parameters(program.tcx, function)
                    .map(|index| (function, index)),
            );
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let mut children = Vec::new();
            let mut type_backed = Vec::new();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                if !matches!(
                    data.terminator().kind,
                    TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. }
                ) {
                    continue;
                }
                let call = Location {
                    block,
                    statement_index: data.statements.len(),
                };
                for evidence in super::returned_child::derive(program.tcx, function, call) {
                    let raw_field_parent = match &evidence.parent {
                        super::returned_child::ChildRoot::Local(parent) => {
                            returned_parent_is_raw_field_load(program.tcx, &body, call, *parent)
                        }
                        super::returned_child::ChildRoot::Unknown { .. } => false,
                    };
                    children.push(ReturnedChildRecord {
                        callee: symbol_key(program.tcx, evidence.key.callee, &program.functions),
                        evidence,
                        raw_field_parent,
                    });
                }
                for evidence in super::returned_child::derive_type_backed(
                    program.tcx,
                    function,
                    call,
                    &|callee| callee_may_yield_pointer(program.tcx, callee),
                ) {
                    type_backed.push(ReturnedChildRecord {
                        callee: symbol_key(program.tcx, evidence.key.callee, &program.functions),
                        evidence,
                        raw_field_parent: false,
                    });
                }
            }
            for argument_index in 0..body.arg_count {
                let local = Local::from_usize(argument_index + 1);
                if !matches!(body.local_decls[local].ty.kind(), TyKind::RawPtr(..)) {
                    continue;
                }
                facts.insert(
                    (function, argument_index),
                    collect_retention_facts(
                        program,
                        function,
                        local,
                        Some(argument_index),
                        &body,
                        &children,
                        &RetentionPriorPass::default(),
                    ),
                );
            }
            returned_children.insert(function, children);
            type_backed_children.insert(function, type_backed);
        }
        // wave-6v2 (R407-11): the returned-alias continuation and the
        // stack-storage discharge read the previous pass; iterate to a
        // fixpoint (a chain of returning callees needs one pass per link).
        let mut prior = RetentionPriorPass::of(&facts);
        for _ in 0..program.functions.len() {
            if prior == RetentionPriorPass::default() {
                break;
            }
            let mut next = FxHashMap::default();
            for &function in &program.functions {
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let children = &returned_children[&function];
                for argument_index in 0..body.arg_count {
                    let local = Local::from_usize(argument_index + 1);
                    if !matches!(body.local_decls[local].ty.kind(), TyKind::RawPtr(..)) {
                        continue;
                    }
                    next.insert(
                        (function, argument_index),
                        collect_retention_facts(
                            program,
                            function,
                            local,
                            Some(argument_index),
                            &body,
                            children,
                            &prior,
                        ),
                    );
                }
            }
            let next_prior = RetentionPriorPass::of(&next);
            facts = next;
            if next_prior == prior {
                break;
            }
            prior = next_prior;
        }
        let rows = if origins.is_none() {
            evaluate_retention(&facts, false)
                .into_iter()
                .map(|(key, verdict)| {
                    (
                        key,
                        if matches!(verdict, RetentionVerdict::Retains { .. }) {
                            verdict
                        } else {
                            RetentionVerdict::Unknown {
                                reason: RetentionUnknownReason::AnalysisIncomplete,
                                frontier: Vec::new(),
                            }
                        },
                    )
                })
                .collect()
        } else {
            evaluate_retention(&facts, attested)
        };
        let child_access = crate::bo_rewriter::wave6r_child_access::discharge(
            program,
            &rows,
            type_backed_children
                .values_mut()
                .flatten()
                .map(|record| &mut record.evidence),
        );
        let consumed_results =
            crate::bo_rewriter::wave6r_child_access::consumed_results(program, &rows);
        let settled_returned_aliases =
            crate::bo_rewriter::wave6r_child_access::settled_returned_aliases(program, &rows);
        Self {
            rows,
            facts,
            attested,
            output_storage_settled: FxHashMap::default(),
            returned_children,
            child_access,
            consumed_results,
            settled_returned_aliases,
            type_backed_children,
            pointer_free_parameters,
        }
    }

    pub(crate) fn pointee_pointer_free(&self, function: LocalDefId, argument_index: usize) -> bool {
        self.pointer_free_parameters
            .contains(&(function, argument_index))
    }

    pub(crate) fn get(
        &self,
        function: LocalDefId,
        argument_index: usize,
    ) -> Option<&RetentionVerdict> {
        self.rows.get(&(function, argument_index))
    }

    fn returned_child_at(
        &self,
        caller: LocalDefId,
        site: &RawBoundarySiteKey,
    ) -> ReturnedChildSiteEvidence {
        let matches = self
            .returned_children
            .get(&caller)
            .into_iter()
            .flatten()
            .filter(|record| {
                record.evidence.key.caller == caller
                    && record.evidence.key.call.block.as_u32() == site.block
                    && record.evidence.key.call.statement_index == site.statement_index as usize
                    && record.evidence.key.parent_argument_index == site.argument_index
                    && record.callee == site.callee
            })
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [record] => ReturnedChildSiteEvidence {
                child: Ok(record.evidence.clone()),
                raw_field_parent: record.raw_field_parent,
            },
            [] => ReturnedChildSiteEvidence {
                child: Err("returned-child-evidence-missing"),
                raw_field_parent: false,
            },
            _ => ReturnedChildSiteEvidence {
                child: Err("returned-child-evidence-ambiguous"),
                raw_field_parent: false,
            },
        }
    }

    /// K18'/OAP-CHILD-ACCESS. What the caller actually does with a pointer this
    /// callee may hand back, for callees with no pinned contract row. `None`
    /// means the walk produced no unique evidence, and the caller must keep
    /// treating the child's access as unknown.
    /// wave-6r (relay 021): is this callee position's Return-only retention
    /// settled at every call of it inside `caller` — the returned alias
    /// discarded or consumed where it is produced? The callee ROW still says
    /// `retains`; this says the caller keeps nothing.
    pub(crate) fn returned_alias_settled(
        &self,
        caller: LocalDefId,
        callee: LocalDefId,
        argument_index: usize,
    ) -> bool {
        self.settled_returned_aliases
            .contains(&(caller, callee, argument_index))
    }

    /// wave-6r (relay 019): does the caller consume the alias returned by the
    /// call at this site where it is produced?
    pub(crate) fn result_consumed_at(
        &self,
        caller: LocalDefId,
        block: u32,
        statement: u32,
    ) -> bool {
        self.consumed_results.contains(&(caller, block, statement))
    }

    pub(crate) fn type_backed_child_access(
        &self,
        caller: LocalDefId,
        site: &RawBoundarySiteKey,
    ) -> Option<&super::returned_child::ChildAccess> {
        let matches = self
            .type_backed_children
            .get(&caller)
            .into_iter()
            .flatten()
            .filter(|record| {
                record.evidence.key.caller == caller
                    && record.evidence.key.call.block.as_u32() == site.block
                    && record.evidence.key.call.statement_index == site.statement_index as usize
                    && record.evidence.key.parent_argument_index == site.argument_index
                    && record.callee == site.callee
            })
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [record] => Some(&record.evidence.access),
            _ => None,
        }
    }

    /// R210(c): outward retention rooted at the copied destination, rather
    /// than at a parameter. This query never licenses a local alias schedule.
    pub(crate) fn copied_local_retention(
        &self,
        program: &RustProgram<'_>,
        function: LocalDefId,
        destination: Local,
    ) -> RetentionVerdict {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let facts = collect_retention_facts(
            program,
            function,
            destination,
            None,
            &body,
            self.returned_children
                .get(&function)
                .map_or(&[], Vec::as_slice),
            &RetentionPriorPass::default(),
        );
        let unknown_reason = if !self.attested {
            RetentionUnknownReason::AttestationAbsent
        } else {
            facts.unknowns.first_key_value().map_or(
                RetentionUnknownReason::LocalSummaryUnknown,
                |(&reason, _)| reason,
            )
        };
        let mut frontier = facts.steps.clone();
        frontier.extend(facts.unknowns.values().flatten().cloned());
        frontier.sort();
        frontier.dedup();

        let mut pending = VecDeque::from([(facts, Vec::<RetentionStep>::new())]);
        let mut visited = FxHashSet::default();
        while let Some((facts, mut path)) = pending.pop_front() {
            // A visible positive sink is sufficient to hold the bridge. It
            // cannot be erased by missing attestation, unknown origin facts,
            // or a second definition on another path.
            if let Some(sink) = facts.retains.first() {
                path.push(sink.clone());
                return RetentionVerdict::Retains {
                    sink: sink.clone(),
                    path,
                };
            }
            for dependency in &facts.dependencies {
                let key = (dependency.callee, dependency.argument_index);
                if !visited.insert(key) || !self.facts.contains_key(&key) {
                    continue;
                }
                // Only the reachable parameter roots are inspected. Existing
                // summary rows can be Unknown solely because attestation or
                // origins were absent; they must not conceal a positive sink.
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(dependency.callee)
                    .borrow();
                let dependency_facts = collect_retention_facts(
                    program,
                    dependency.callee,
                    Local::from_usize(dependency.argument_index + 1),
                    None,
                    &body,
                    self.returned_children
                        .get(&dependency.callee)
                        .map_or(&[], Vec::as_slice),
                    &RetentionPriorPass::default(),
                );
                let mut dependency_path = path.clone();
                dependency_path.push(dependency.step.clone());
                pending.push_back((dependency_facts, dependency_path));
            }
        }

        // Absence of an outward sink says nothing about later uses of this
        // raw alias beside the parent reference, so this is never T1 evidence.
        RetentionVerdict::Unknown {
            reason: unknown_reason,
            frontier,
        }
    }

    pub(crate) fn verify_certificate(
        &self,
        function: LocalDefId,
        argument_index: usize,
        certificate: &RetentionCertificate,
    ) -> Result<(), &'static str> {
        let replay = evaluate_retention(&self.facts, self.attested);
        let sorted_unique = certificate.steps.windows(2).all(|pair| pair[0] < pair[1]);
        match replay.get(&(function, argument_index)) {
            Some(RetentionVerdict::NoRetain {
                certificate: expected,
            }) if expected == certificate && sorted_unique => Ok(()),
            _ => Err("retention-certificate-invalid"),
        }
    }

    pub(crate) fn to_tsv(&self) -> String {
        let mut keys = self.rows.keys().copied().collect::<Vec<_>>();
        keys.sort_by_key(|(function, argument)| (function.local_def_index.as_u32(), *argument));
        let mut out = String::from(
            "function\tlocal_def_index\targument_index\tverdict\treason\tpath_or_frontier\tattested\n",
        );
        for key in keys {
            let facts = self.facts.get(&key);
            let function = facts.map_or("<missing>", |facts| facts.function_path.as_str());
            let (verdict, reason, steps) = match &self.rows[&key] {
                RetentionVerdict::NoRetain { certificate } => (
                    "no-retain",
                    certificate.frame_bounded.as_deref().unwrap_or("-"),
                    certificate
                        .steps
                        .iter()
                        .map(|step| format!("{}:{:?}:{}", step.location, step.kind, step.detail))
                        .collect::<Vec<_>>()
                        .join(";"),
                ),
                RetentionVerdict::Retains { sink, path } => (
                    "retains",
                    "positive-retention",
                    path.iter()
                        .chain(std::iter::once(sink))
                        .map(|step| format!("{}:{:?}:{}", step.location, step.kind, step.detail))
                        .collect::<Vec<_>>()
                        .join(";"),
                ),
                RetentionVerdict::Unknown { reason, frontier } => (
                    "unknown",
                    reason.key(),
                    frontier
                        .iter()
                        .map(|step| format!("{}:{:?}:{}", step.location, step.kind, step.detail))
                        .collect::<Vec<_>>()
                        .join(";"),
                ),
            };
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                function,
                key.0.local_def_index.as_u32(),
                key.1,
                verdict,
                reason,
                if steps.is_empty() { "-" } else { &steps },
                u8::from(self.attested),
            ));
        }
        out
    }
}

pub(crate) const RAW_BOUNDARY_WAIVER_ID: &str =
    "c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01";
pub(crate) const RAW_BOUNDARY_WAIVER_TEXT: &str = "C-aliasing semantics at unsafe bridges. At a receipted T2 site, crat may expose a raw pointer derived from a safe reference to a boundary whose retention behavior is unknown, in order to preserve the source program's C calling convention. Current Rust aliasing models can invalidate a retained raw alias when the originating mutable reference remains live or is later reused. The conditional soundness claim therefore excludes an execution that retains and later uses that raw alias unless no-retention is independently established. This waiver licenses only the recorded safe-to-raw view at that call. It licenses no integer-to-pointer round trip, ownership transfer, unchecked null dereference, positive-retention site, or unreceipted reuse.";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BridgeTemplate {
    Depth2NpoConst,
    Depth2NpoMut,
    VoidFromMut,
    VoidFromRef,
    VoidFromRefCastMut,
    VoidFromMutAsConst,
    /// K19' (R272-2). A settled slice subject reaching a `c_void` position
    /// through a cast. The raw view is taken from the SLICE, so the pointer
    /// carries `len * size_of::<T>()` bytes -- the extent a `&c_void` could
    /// never have carried, which is what makes this bridge the sound reading
    /// of the edge R271-1 opened.
    VoidFromSlice,
    VoidFromSliceMut,
    /// wave-6b: the cursor family's own argument at an opaque formal — the
    /// boundary's receipt over syntax the cursor emits (relay 016).
    VoidFromCursorView,
    RawCastMut,
    RawCastConst,
    TypedRawTemporary,
    RefMutToRawMut,
    RefMutToRawConst,
    RefMutToWritableRawConst,
    RefSharedToRawConst,
    RefSharedToRawMut,
    CursorSharedToRawConst,
    CursorMutToRawMut,
    CursorMutToRawConst,
    SliceMutToRawMut,
    SliceToRawConst,
    SliceMutToWritableRawConst,
    SliceToRawMut,
    OptRefMutToRawMut,
    OptRefToRawConst,
    OptRefMutToWritableRawConst,
    OptRefToRawMut,
    OptSliceToRaw,
    OptSliceMutToWritableRawConst,
    OptSliceToRawMut,
    /// Wave-6o. A THIN optional subject reaching a `c_void` position through
    /// a cast (`memset(item as *mut c_void, ..)`): the same null-map as the
    /// typed cells, with the pointee erased inside the `Some` arm so both
    /// arms of `map_or` agree on `*c_void`. `None` stays null; a shared
    /// optional at a `*mut` position needs the negative-write evidence the
    /// typed twin needs. Optional SLICES stay unavailable here (K19').
    OptRefMutToVoidMut,
    OptRefToVoidConst,
    OptRefToVoidMut,
    /// Wave-6v2 (R406-6). A delivered BYTE VIEW — a counted `&[u8]` /
    /// `Option<&[u8]>` — reaching a `c_void` position: the slice's raw view
    /// carries its whole extent (K19'), the pointee is erased in the `Some`
    /// arm, `None` stays null, and a shared view at a `*mut` position needs
    /// the negative-write evidence the typed twin (`SliceToRawMut`) needs.
    VoidFromSliceCastMut,
    OptSliceMutToVoidMut,
    OptSliceToVoidConst,
    OptSliceToVoidMut,
    BoxBorrowViewToRaw,
    /// R452-3(3). The same borrow view when the owner is OPTIONAL: the option
    /// is opened first and `None` is the null pointer, so `Option<Box<T>>` and
    /// `Option<Box<[T]>>` reach a raw position without the bare
    /// `as_mut_ptr()` that does not exist on an `Option` (batch 10: 27 brotli
    /// reverts and wave-6f's three `verify-reverted` roots).
    OptionalBoxBorrowViewToRaw,
    KnownFreeDrop,
}

impl BridgeTemplate {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Depth2NpoConst | Self::Depth2NpoMut => "depth2-npo-bridge",
            Self::VoidFromMut | Self::VoidFromRef | Self::VoidFromMutAsConst => "void-generic-raw",
            Self::VoidFromSlice | Self::VoidFromSliceMut => "void-generic-raw-slice",
            Self::VoidFromCursorView => "void-cursor-view",
            Self::VoidFromSliceCastMut => "shared-slice-to-mut-void",
            Self::VoidFromRefCastMut => "shared-ref-to-mut-raw",
            Self::RawCastMut => "raw-cast-mut",
            Self::RawCastConst => "raw-cast-const",
            Self::TypedRawTemporary => "typed-raw-temporary",
            Self::RefMutToRawMut => "ref-mut-to-raw-mut",
            Self::RefMutToRawConst => "ref-mut-to-raw-const",
            Self::RefMutToWritableRawConst => "returned-child-ref-mut-to-raw-const",
            Self::RefSharedToRawConst => "ref-shared-to-raw-const",
            Self::RefSharedToRawMut => "shared-ref-to-mut-raw",
            Self::CursorSharedToRawConst => "cursor-shared-to-raw-const",
            Self::CursorMutToRawMut => "cursor-mut-to-raw-mut",
            Self::CursorMutToRawConst => "cursor-mut-to-raw-const",
            Self::SliceMutToRawMut => "slice-mut-to-raw-mut",
            Self::SliceToRawConst => "slice-to-raw-const",
            Self::SliceMutToWritableRawConst => "returned-child-slice-mut-to-raw-const",
            Self::SliceToRawMut => "slice-to-raw-mut",
            Self::OptRefMutToRawMut
            | Self::OptRefToRawConst
            | Self::OptRefToRawMut
            | Self::OptSliceToRaw
            | Self::OptSliceToRawMut
            | Self::OptRefMutToVoidMut
            | Self::OptRefToVoidConst
            | Self::OptRefToVoidMut
            | Self::OptSliceMutToVoidMut
            | Self::OptSliceToVoidConst
            | Self::OptSliceToVoidMut => "option-to-raw-null-map",
            Self::OptRefMutToWritableRawConst | Self::OptSliceMutToWritableRawConst => {
                "returned-child-option-mut-to-raw-const"
            }
            Self::BoxBorrowViewToRaw => "box-borrow-view-to-raw",
            Self::OptionalBoxBorrowViewToRaw => "optional-box-borrow-view-to-raw",
            Self::KnownFreeDrop => "known-free-drop",
        }
    }

    pub(crate) fn render(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        cast_pointee: Option<&str>,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        self.render_mode(argument, target_mutability, box_slice, cast_pointee, false)
    }

    pub(crate) fn render_explicit(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        cast_pointee: Option<&str>,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        self.render_mode(argument, target_mutability, box_slice, cast_pointee, true)
    }

    fn render_mode(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        cast_pointee: Option<&str>,
        force_explicit: bool,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        match self {
            Self::Depth2NpoConst | Self::Depth2NpoMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                let inner = if self == Self::Depth2NpoMut {
                    "mut"
                } else {
                    "const"
                };
                Ok(BridgeRender::Edit(format!(
                    "core::ptr::from_mut(&mut {argument}).cast::<*{inner} {pointee}>()"
                )))
            }
            Self::VoidFromMut
            | Self::VoidFromRef
            | Self::VoidFromRefCastMut
            | Self::VoidFromMutAsConst
            | Self::VoidFromSlice
            | Self::VoidFromSliceMut
            | Self::VoidFromSliceCastMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                if self == Self::VoidFromSliceCastMut {
                    return Ok(BridgeRender::Edit(format!(
                        "{argument}.as_ptr().cast::<{pointee}>().cast_mut()"
                    )));
                }
                let source = match self {
                    Self::VoidFromMut => format!("core::ptr::from_mut({argument})"),
                    Self::VoidFromRef => format!("core::ptr::from_ref({argument})"),
                    Self::VoidFromRefCastMut => {
                        format!("core::ptr::from_ref({argument}).cast_mut()")
                    }
                    Self::VoidFromMutAsConst => {
                        format!("core::ptr::from_ref(&*{argument})")
                    }
                    Self::VoidFromSlice => format!("{argument}.as_ptr()"),
                    Self::VoidFromSliceMut => format!("{argument}.as_mut_ptr()"),
                    _ => unreachable!(),
                };
                Ok(BridgeRender::Edit(format!("{source}.cast::<{pointee}>()")))
            }
            // The cursor family renders this argument itself (relay 016): the
            // boundary's part is the receipt, so the bridge is zero syntax.
            Self::VoidFromCursorView => Ok(BridgeRender::ZeroSyntax),
            Self::RawCastMut => Ok(BridgeRender::Edit(format!("{argument}.cast_mut()"))),
            Self::RawCastConst => Ok(BridgeRender::Edit(format!("{argument}.cast_const()"))),
            Self::TypedRawTemporary => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                let target = match target_mutability {
                    RawMutability::Mut => format!("*mut {pointee}"),
                    RawMutability::Const => format!("*const {pointee}"),
                };
                Ok(BridgeRender::Edit(format!(
                    "{{ let __crat_raw: {target} = ({argument}) as {target}; __crat_raw }}"
                )))
            }
            Self::RefMutToWritableRawConst
            | Self::SliceMutToWritableRawConst
            | Self::OptRefMutToWritableRawConst
            | Self::OptSliceMutToWritableRawConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                let expression = match self {
                    Self::RefMutToWritableRawConst => format!(
                        "core::ptr::from_mut(&mut *{argument}).cast::<{pointee}>().cast_const()"
                    ),
                    Self::SliceMutToWritableRawConst => {
                        format!("{argument}.as_mut_ptr().cast::<{pointee}>().cast_const()")
                    }
                    Self::OptRefMutToWritableRawConst => format!(
                        "{argument}.as_deref_mut().map_or(core::ptr::null::<{pointee}>(), |value| core::ptr::from_mut(value).cast::<{pointee}>().cast_const())"
                    ),
                    Self::OptSliceMutToWritableRawConst => format!(
                        "{argument}.as_deref_mut().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_mut_ptr().cast::<{pointee}>().cast_const())"
                    ),
                    _ => unreachable!("selected returned-child writable view"),
                };
                Ok(BridgeRender::Edit(expression))
            }
            Self::RefMutToRawMut if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_mut(&mut *{argument})"
            ))),
            Self::RefMutToRawConst if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref(&*{argument})"
            ))),
            Self::RefSharedToRawConst if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref({argument})"
            ))),
            Self::RefSharedToRawMut => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref({argument}).cast_mut()"
            ))),
            Self::RefMutToRawMut | Self::RefMutToRawConst | Self::RefSharedToRawConst => {
                Ok(BridgeRender::ZeroSyntax)
            }
            Self::CursorSharedToRawConst | Self::CursorMutToRawMut | Self::CursorMutToRawConst => {
                let mutable = self != Self::CursorSharedToRawConst;
                let expected = if self == Self::CursorMutToRawMut {
                    RawMutability::Mut
                } else {
                    RawMutability::Const
                };
                if target_mutability != expected {
                    return Err(RawBoundaryBlockReason::TemplateUnavailable);
                }
                // SAFETY: native cursor admission proves the retained base and
                // current index; the boundary requires verified no-retention.
                // Borrowing the operand once neither moves the base nor repeats
                // an operand expression. The block's binding shadows only after
                // its initializer, even if the source has the generated name.
                let borrow = if mutable { "&mut " } else { "&" };
                let method = if mutable { "as_mut_ptr" } else { "as_ptr" };
                let cast = cast_pointee
                    .map(|pointee| format!(".cast::<{pointee}>()"))
                    .unwrap_or_default();
                let as_const = if self == Self::CursorMutToRawConst {
                    ".cast_const()"
                } else {
                    ""
                };
                Ok(BridgeRender::Edit(format!(
                    "{{ let __crat_cursor = {borrow}({argument}); __crat_cursor.0.{method}().add(__crat_cursor.1){cast}{as_const} }}"
                )))
            }
            Self::SliceMutToRawMut => Ok(BridgeRender::Edit(format!("{argument}.as_mut_ptr()"))),
            Self::SliceToRawConst => Ok(BridgeRender::Edit(format!("{argument}.as_ptr()"))),
            Self::SliceToRawMut => Ok(BridgeRender::Edit(format!(
                "{argument}.as_ptr().cast_mut()"
            ))),
            Self::OptRefMutToRawMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), core::ptr::from_mut)"
                )))
            }
            Self::OptRefToRawConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), core::ptr::from_ref)"
                )))
            }
            Self::OptRefToRawMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |value| core::ptr::from_ref(value).cast_mut())"
                )))
            }
            Self::OptSliceToRaw => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(match target_mutability {
                    RawMutability::Mut => format!(
                        "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_mut_ptr())"
                    ),
                    RawMutability::Const => format!(
                        "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_ptr())"
                    ),
                }))
            }
            Self::OptSliceToRawMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_ptr().cast_mut())"
                )))
            }
            Self::OptRefMutToVoidMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |value| core::ptr::from_mut(value).cast::<{pointee}>())"
                )))
            }
            Self::OptRefToVoidConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), |value| core::ptr::from_ref(value).cast::<{pointee}>())"
                )))
            }
            Self::OptRefToVoidMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |value| core::ptr::from_ref(value).cast::<{pointee}>().cast_mut())"
                )))
            }
            Self::OptSliceMutToVoidMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_mut_ptr().cast::<{pointee}>())"
                )))
            }
            Self::OptSliceToVoidConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_ptr().cast::<{pointee}>())"
                )))
            }
            Self::OptSliceToVoidMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_ptr().cast::<{pointee}>().cast_mut())"
                )))
            }
            Self::OptSliceMutToVoidMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_mut_ptr().cast::<{pointee}>())"
                )))
            }
            Self::OptSliceToVoidConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_ptr().cast::<{pointee}>())"
                )))
            }
            Self::BoxBorrowViewToRaw if box_slice => {
                Ok(BridgeRender::Edit(match target_mutability {
                    RawMutability::Mut => format!("{argument}.as_mut_ptr()"),
                    RawMutability::Const => format!("{argument}.as_ptr()"),
                }))
            }
            Self::BoxBorrowViewToRaw => Ok(BridgeRender::Edit(match target_mutability {
                RawMutability::Mut => format!("core::ptr::from_mut({argument}.as_mut())"),
                RawMutability::Const => format!("core::ptr::from_ref({argument}.as_ref())"),
            })),
            Self::OptionalBoxBorrowViewToRaw => {
                Ok(BridgeRender::Edit(match (box_slice, target_mutability) {
                    (true, RawMutability::Mut) => format!(
                        "{argument}.as_deref_mut().map_or(core::ptr::null_mut(), |s| s.as_mut_ptr())"
                    ),
                    (true, RawMutability::Const) => {
                        format!("{argument}.as_deref().map_or(core::ptr::null(), |s| s.as_ptr())")
                    }
                    (false, RawMutability::Mut) => format!(
                        "{argument}.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut)"
                    ),
                    (false, RawMutability::Const) => format!(
                        "{argument}.as_deref().map_or(core::ptr::null(), core::ptr::from_ref)"
                    ),
                }))
            }
            Self::KnownFreeDrop => Ok(BridgeRender::Lifecycle),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BridgeRender {
    ZeroSyntax,
    Edit(String),
    Lifecycle,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawBoundaryBlockReason {
    SiteUnresolved,
    SubjectUnrooted,
    SubjectNotSafe,
    SharedToMut,
    OwnershipTransfer,
    PositiveRetention,
    Depth2FatLayout,
    Depth2StorageShape,
    ContractInvalid,
    TemplateUnavailable,
    WaiverUnconfirmed,
    ReturnedChildPermission,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReturnedChildPermissionFailure {
    Writes,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ReturnedChildBridge {
    pub(crate) template: BridgeTemplate,
    pub(crate) mutable_binding_required: bool,
}

pub(crate) fn returned_child_template(
    source: &super::Decision,
    target: &RawTargetType,
    access: Option<&super::returned_child::ChildAccess>,
    base: BridgeTemplate,
) -> Result<ReturnedChildBridge, RawBoundaryBlockReason> {
    let unchanged = ReturnedChildBridge {
        template: base,
        mutable_binding_required: false,
    };
    if target.mutability != RawMutability::Const
        || matches!(
            access,
            Some(
                super::returned_child::ChildAccess::Unused
                    | super::returned_child::ChildAccess::ReadOnly { .. }
            )
        )
    {
        return Ok(unchanged);
    }
    returned_child_permission(source, access)
        .map_err(|_| RawBoundaryBlockReason::ReturnedChildPermission)?;
    if target.depth2.is_some() {
        return Err(RawBoundaryBlockReason::TemplateUnavailable);
    }
    let (template, mutable_binding_required) = match source {
        super::Decision::Ref { mutable: true }
        | super::Decision::InferredRef { mutable: true, .. } => {
            (BridgeTemplate::RefMutToWritableRawConst, false)
        }
        super::Decision::Slice { mutable: true, .. } => {
            (BridgeTemplate::SliceMutToWritableRawConst, false)
        }
        super::Decision::Opt {
            mutable: true,
            slice: false,
            ..
        } => (BridgeTemplate::OptRefMutToWritableRawConst, true),
        super::Decision::Opt {
            mutable: true,
            slice: true,
            ..
        } => (BridgeTemplate::OptSliceMutToWritableRawConst, true),
        super::Decision::Degraded(_) => return Ok(unchanged),
        super::Decision::Ref { mutable: false }
        | super::Decision::InferredRef { mutable: false, .. }
        | super::Decision::Slice { mutable: false, .. }
        | super::Decision::Opt { mutable: false, .. }
        | super::Decision::Box(_)
        | super::Decision::NestedSlice { .. }
        | super::Decision::Cursor { .. } => {
            return Err(RawBoundaryBlockReason::ReturnedChildPermission);
        }
    };
    if base == BridgeTemplate::TypedRawTemporary {
        // A raw expression derived from a safe root needs its own operation
        // adapter; applying a slice/reference method to that raw value cannot
        // preserve permission. Proven field values bypass this selector.
        return Err(RawBoundaryBlockReason::TemplateUnavailable);
    }
    Ok(ReturnedChildBridge {
        template,
        mutable_binding_required,
    })
}

/// A settled safe source whose own view is mutable, so a writable derivation
/// of it is available.
pub(crate) fn is_mutable_safe_source(decision: &super::Decision) -> bool {
    matches!(
        decision,
        super::Decision::Ref { mutable: true }
            | super::Decision::InferredRef { mutable: true, .. }
            | super::Decision::Slice { mutable: true, .. }
            | super::Decision::Opt { mutable: true, .. }
    )
}

/// A settled safe source whose only view is shared. `Box` is excluded: it is an
/// owning form with its own arm, not a borrowed view.
pub(crate) fn is_shared_safe_source(decision: &super::Decision) -> bool {
    matches!(
        decision,
        super::Decision::Ref { mutable: false }
            | super::Decision::InferredRef { mutable: false, .. }
            | super::Decision::Slice { mutable: false, .. }
            | super::Decision::Opt { mutable: false, .. }
    )
}

/// An address expression borrows its selected place, independently of the
/// reference, slice or Option form of the binding containing that place.
pub(crate) fn outbound_reference_view(
    source: &super::Decision,
    source_shape: &str,
) -> Option<super::Decision> {
    match source {
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::Slice { .. }
        | super::Decision::Opt { .. } => match source_shape {
            "addr-of" | "addr-of-cast" => Some(super::Decision::Ref { mutable: false }),
            "addr-of-mut" | "addr-of-mut-cast" => Some(super::Decision::Ref { mutable: true }),
            _ => None,
        },
        super::Decision::Box(_)
        | super::Decision::NestedSlice { .. }
        | super::Decision::Cursor { .. }
        | super::Decision::Degraded(_) => None,
    }
}

/// Policy seam over an already selected expression form. The target raw
/// pointer's mutability cannot establish permission for subsequent child uses.
pub(crate) fn returned_child_permission(
    source: &super::Decision,
    access: Option<&super::returned_child::ChildAccess>,
) -> Result<(), ReturnedChildPermissionFailure> {
    let shared = match source {
        super::Decision::Ref { mutable }
        | super::Decision::InferredRef { mutable, .. }
        | super::Decision::Slice { mutable, .. }
        | super::Decision::Opt { mutable, .. } => !*mutable,
        super::Decision::NestedSlice { .. } | super::Decision::Cursor { .. } => {
            return Err(ReturnedChildPermissionFailure::Unknown);
        }
        super::Decision::Box(_) | super::Decision::Degraded(_) => false,
    };
    if !shared {
        return Ok(());
    }
    match access {
        Some(
            super::returned_child::ChildAccess::Unused
            | super::returned_child::ChildAccess::ReadOnly { .. },
        ) => Ok(()),
        Some(super::returned_child::ChildAccess::Writes { .. }) => {
            Err(ReturnedChildPermissionFailure::Writes)
        }
        Some(super::returned_child::ChildAccess::Unknown { .. }) | None => {
            Err(ReturnedChildPermissionFailure::Unknown)
        }
    }
}

impl RawBoundaryBlockReason {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::SiteUnresolved => "raw-boundary-site-unresolved",
            Self::SubjectUnrooted => "raw-boundary-subject-unrooted",
            Self::SubjectNotSafe => "raw-boundary-subject-not-safe",
            Self::SharedToMut => "raw-boundary-shared-to-mut",
            Self::OwnershipTransfer => "raw-boundary-ownership-transfer",
            Self::PositiveRetention => "raw-boundary-positive-retention",
            Self::Depth2FatLayout => "depth2-fat-layout-incompatible",
            Self::Depth2StorageShape => "depth2-storage-shape-held",
            Self::ContractInvalid => "raw-boundary-contract-invalid",
            Self::TemplateUnavailable => "raw-boundary-template-unavailable",
            Self::WaiverUnconfirmed => "raw-boundary-waiver-unconfirmed",
            Self::ReturnedChildPermission => "raw-boundary-returned-child-permission",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RawBoundaryDisposition {
    T1 {
        template: BridgeTemplate,
        evidence: String,
    },
    T2 {
        template: BridgeTemplate,
        reason: RetentionUnknownReason,
        waiver_id: &'static str,
        evidence: String,
    },
    Blocked {
        reason: RawBoundaryBlockReason,
        detail: String,
    },
    /// Another accepted emitter owns this exact site. It discharges the
    /// boundary obligation without creating an Arm-A edit or atom.
    OwnedByOtherArm {
        owner: &'static str,
        reason: &'static str,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct RawBoundaryRenderSite {
    pub span: Span,
    pub direct_storage_span: Option<Span>,
    pub adapter_operand_span: Span,
    pub call_span: Span,
    pub target: RawTargetType,
    pub box_slice: bool,
    pub source_shape: &'static str,
    pub source_site: String,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee_local: Option<LocalDefId>,
    pub target_stays_raw: bool,
    pub subject_identity: String,
    pub mutable_binding_required: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AddressViewSite {
    pub owner: String,
    pub span: Span,
    pub node: (LocalDefId, HirId),
    pub template: BridgeTemplate,
    pub target: RawTargetType,
    pub op: &'static str,
    pub operand_index: usize,
    pub bridge_kind: &'static str,
    pub target_type: String,
}

impl RawBoundaryDisposition {
    pub(crate) fn is_open(&self) -> bool {
        match self {
            Self::T1 { .. } | Self::T2 { .. } => true,
            Self::Blocked { .. } | Self::OwnedByOtherArm { .. } => false,
        }
    }

    fn is_handled(&self) -> bool {
        match self {
            Self::T1 { .. } | Self::T2 { .. } | Self::OwnedByOtherArm { .. } => true,
            Self::Blocked { .. } => false,
        }
    }

    pub(crate) fn tier(&self) -> &'static str {
        match self {
            Self::T1 { .. } => "T1",
            Self::T2 { .. } => "T2",
            Self::Blocked { .. } => "blocked",
            Self::OwnedByOtherArm { owner: "box", .. } => "owned-by-box",
            Self::OwnedByOtherArm { .. } => "owned-by-other-arm",
        }
    }

    pub(crate) fn template(&self) -> Option<BridgeTemplate> {
        match self {
            Self::T1 { template, .. } | Self::T2 { template, .. } => Some(*template),
            Self::Blocked { .. } | Self::OwnedByOtherArm { .. } => None,
        }
    }
}

fn box_site_owner(
    decision: &super::Decision,
    site: &RawBoundarySiteFact,
) -> Option<(&'static str, &'static str)> {
    let plan = match decision {
        super::Decision::Box(plan) => plan,
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::Slice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::NestedSlice { .. }
        | super::Decision::Cursor { .. }
        | super::Decision::Degraded(_) => return None,
    };
    let site_span = site.source_span.source_callsite();
    if plan
        .delete_statements
        .iter()
        .any(|span| span.source_callsite().contains(site_span))
    {
        return Some(("box", "box-initializer-consumed"));
    }
    plan.expr_edits.iter().find_map(|edit| {
        edit.span.source_callsite().contains(site_span).then_some((
            "box",
            match edit.receipt {
                "c-free-site-drop" => "box-lifecycle-owned",
                "realloc-atomic" => "box-realloc-owned",
                _ => "box-construction-owned",
            },
        ))
    })
}

pub(crate) fn template_for(
    decision: &super::Decision,
    target: &RawTargetType,
    ownership: Option<super::raw_boundary_contracts::OwnershipContract>,
    has_negative_write_evidence: bool,
) -> Result<BridgeTemplate, RawBoundaryBlockReason> {
    use super::{Decision, box_facts::BoxShape, raw_boundary_contracts::OwnershipContract};

    if matches!(
        ownership,
        Some(OwnershipContract::AtomicSourceSink | OwnershipContract::Produce)
    ) {
        return Err(RawBoundaryBlockReason::OwnershipTransfer);
    }
    if let Some(depth2) = target.depth2.as_ref() {
        if !depth2.thin {
            return Err(RawBoundaryBlockReason::Depth2FatLayout);
        }
        return match decision {
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { slice: false, .. } => {
                Ok(if depth2.inner_mutability == RawMutability::Mut {
                    BridgeTemplate::Depth2NpoMut
                } else {
                    BridgeTemplate::Depth2NpoConst
                })
            }
            Decision::Opt { slice: true, .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => Err(RawBoundaryBlockReason::TemplateUnavailable),
        };
    }
    if target.is_void_pointee() {
        return match decision {
            Decision::Ref { mutable: true } | Decision::InferredRef { mutable: true, .. }
                if target.mutability == RawMutability::Mut =>
            {
                Ok(BridgeTemplate::VoidFromMut)
            }
            Decision::Ref { mutable: true } | Decision::InferredRef { mutable: true, .. } => {
                Ok(BridgeTemplate::VoidFromMutAsConst)
            }
            Decision::Ref { mutable: false } | Decision::InferredRef { mutable: false, .. }
                if target.mutability == RawMutability::Const =>
            {
                Ok(BridgeTemplate::VoidFromRef)
            }
            Decision::Ref { mutable: false } | Decision::InferredRef { mutable: false, .. }
                if has_negative_write_evidence =>
            {
                Ok(BridgeTemplate::VoidFromRefCastMut)
            }
            Decision::Ref { mutable: false } | Decision::InferredRef { mutable: false, .. } => {
                Err(RawBoundaryBlockReason::SharedToMut)
            }
            // K19' (R272-2). The four slice cells the void branch was missing.
            // A slice's raw view carries the whole allocation the subject
            // stands for, so the cast to `c_void` is a change of spelling
            // rather than a loss of extent -- the opposite of what
            // `&c_void` did. `Opt` stays unavailable: it is outside R272-2's
            // approved arm and fails closed.
            Decision::Slice { mutable: true, .. } if target.mutability == RawMutability::Mut => {
                Ok(BridgeTemplate::VoidFromSliceMut)
            }
            // R259-2's writable-const carrier itself, not a void-specific
            // twin of it: a mutable subject reaches a `*const` position
            // through a WRITABLE derivation, and this is the exact template
            // `returned_child_template` would select anyway. Naming it here
            // keeps one carrier for one meaning.
            Decision::Slice { mutable: true, .. } => Ok(BridgeTemplate::SliceMutToWritableRawConst),
            Decision::Slice { mutable: false, .. } if target.mutability == RawMutability::Const => {
                Ok(BridgeTemplate::VoidFromSlice)
            }
            // A shared subject at a `*mut` position is NOT one of R272-2's
            // four cells and is not opened here, even with negative-write
            // evidence. That evidence is about the CALLEE's own writes; it
            // says nothing about a descendant the callee hands back and the
            // caller then writes through — the addendum-259 shape, whose
            // guard only runs at `*const` targets. The typed twins
            // (`RefSharedToRawMut`, `SliceToRawMut`, `VoidFromRefCastMut`)
            // carry that same open obligation already; widening it to a new
            // cell is the seat's call, not this arm's.
            // Wave-6v2 (R406-6): the void twin of `SliceToRawMut` — a shared
            // byte view at a `*mut c_void` position under negative-write
            // evidence. The descendant question is asked upstream at every
            // `*mut` target since R283-3 (`returned_child_permission`), the
            // same way it is for the typed twin.
            Decision::Slice { mutable: false, .. } if has_negative_write_evidence => {
                Ok(BridgeTemplate::VoidFromSliceCastMut)
            }
            Decision::Slice { mutable: false, .. } => Err(RawBoundaryBlockReason::SharedToMut),
            // Wave-6o: the thin optional cells, mirroring the typed `Opt`
            // arm below with the pointee erased inside the `Some` arm.
            Decision::Opt {
                mutable: true,
                slice: false,
                ..
            } if target.mutability == RawMutability::Mut => Ok(BridgeTemplate::OptRefMutToVoidMut),
            Decision::Opt { slice: false, .. } if target.mutability == RawMutability::Const => {
                Ok(BridgeTemplate::OptRefToVoidConst)
            }
            Decision::Opt {
                mutable: false,
                slice: false,
                ..
            } if has_negative_write_evidence => Ok(BridgeTemplate::OptRefToVoidMut),
            Decision::Opt { slice: false, .. } => Err(RawBoundaryBlockReason::SharedToMut),
            // Wave-6v2 (R406-6): the optional byte-view cells.
            Decision::Opt {
                mutable: true,
                slice: true,
                ..
            } if target.mutability == RawMutability::Mut => {
                Ok(BridgeTemplate::OptSliceMutToVoidMut)
            }
            Decision::Opt { slice: true, .. } if target.mutability == RawMutability::Const => {
                Ok(BridgeTemplate::OptSliceToVoidConst)
            }
            Decision::Opt {
                mutable: false,
                slice: true,
                ..
            } if has_negative_write_evidence => Ok(BridgeTemplate::OptSliceToVoidMut),
            Decision::Opt { slice: true, .. } => Err(RawBoundaryBlockReason::SharedToMut),
            // wave-6b (relay 016, R448-5): a CURSOR at an opaque formal. The
            // cursor family renders the whole argument itself — its raw view
            // goes inside the source's own cast (`ip.offset_by(k).as_ptr() as
            // *const c_void`, slicecursor's `b8f6071f2`) — so the boundary owes
            // this site a RECEIPT, not syntax: the bridge is the identity over
            // an expression that is already a raw pointer of the target's
            // mutability, and the cast to the opaque type is the source's.
            //
            // A mutable target from a shared cursor is refused with its
            // siblings: the cursor's view cannot widen a shared borrow.
            Decision::Cursor { mutable: true, .. } => Ok(BridgeTemplate::VoidFromCursorView),
            Decision::Cursor { mutable: false, .. }
                if target.mutability == RawMutability::Const =>
            {
                Ok(BridgeTemplate::VoidFromCursorView)
            }
            Decision::Cursor { mutable: false, .. } => Err(RawBoundaryBlockReason::SharedToMut),
            Decision::Box(_) | Decision::NestedSlice { .. } | Decision::Degraded(_) => {
                Err(RawBoundaryBlockReason::TemplateUnavailable)
            }
        };
    }
    match decision {
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
            match (*mutable, target.mutability) {
                (true, RawMutability::Mut) => Ok(BridgeTemplate::RefMutToRawMut),
                (true, RawMutability::Const) => Ok(BridgeTemplate::RefMutToRawConst),
                (false, RawMutability::Const) => Ok(BridgeTemplate::RefSharedToRawConst),
                (false, RawMutability::Mut) if has_negative_write_evidence => {
                    Ok(BridgeTemplate::RefSharedToRawMut)
                }
                (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
            }
        }
        Decision::Slice { mutable, .. } => match (*mutable, target.mutability) {
            (true, RawMutability::Mut) => Ok(BridgeTemplate::SliceMutToRawMut),
            (_, RawMutability::Const) => Ok(BridgeTemplate::SliceToRawConst),
            (false, RawMutability::Mut) if has_negative_write_evidence => {
                Ok(BridgeTemplate::SliceToRawMut)
            }
            (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
        },
        Decision::Opt { mutable, slice, .. } => {
            if *slice {
                match (*mutable, target.mutability) {
                    (false, RawMutability::Mut) if has_negative_write_evidence => {
                        Ok(BridgeTemplate::OptSliceToRawMut)
                    }
                    (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
                    _ => Ok(BridgeTemplate::OptSliceToRaw),
                }
            } else {
                match (*mutable, target.mutability) {
                    (true, RawMutability::Mut) => Ok(BridgeTemplate::OptRefMutToRawMut),
                    (_, RawMutability::Const) => Ok(BridgeTemplate::OptRefToRawConst),
                    (false, RawMutability::Mut) if has_negative_write_evidence => {
                        Ok(BridgeTemplate::OptRefToRawMut)
                    }
                    (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
                }
            }
        }
        Decision::Box(plan) => {
            if ownership == Some(OwnershipContract::Consume) {
                Ok(BridgeTemplate::KnownFreeDrop)
            } else if plan.optional {
                // The owner is opened before it is viewed (R452-3(3)); which
                // view it is — the slice's or the value's — the renderer reads
                // from the shape it is handed.
                Ok(BridgeTemplate::OptionalBoxBorrowViewToRaw)
            } else {
                Ok(BridgeTemplate::BoxBorrowViewToRaw)
            }
        }
        Decision::NestedSlice { .. } => Err(RawBoundaryBlockReason::TemplateUnavailable),
        Decision::Cursor { mutable, plan } => {
            if plan.wrapper && !plan.optional {
                if ownership == Some(OwnershipContract::Consume) {
                    return Err(RawBoundaryBlockReason::OwnershipTransfer);
                }
                return match (*mutable, target.mutability) {
                    (false, RawMutability::Const) | (true, RawMutability::Const) => {
                        Ok(BridgeTemplate::SliceToRawConst)
                    }
                    (true, RawMutability::Mut) => Ok(BridgeTemplate::SliceMutToRawMut),
                    (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
                };
            }
            if ownership == Some(OwnershipContract::Consume) {
                return Err(RawBoundaryBlockReason::OwnershipTransfer);
            }
            match (*mutable, target.mutability) {
                (false, RawMutability::Const) => Ok(BridgeTemplate::CursorSharedToRawConst),
                (true, RawMutability::Mut) => Ok(BridgeTemplate::CursorMutToRawMut),
                (true, RawMutability::Const) => Ok(BridgeTemplate::CursorMutToRawConst),
                (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
            }
        }
        Decision::Degraded(_) => Err(RawBoundaryBlockReason::SubjectNotSafe),
    }
}

fn cursor_retention_permit(
    decision: &super::Decision,
    verdict: &RetentionVerdict,
) -> Result<(), RawBoundaryBlockReason> {
    let cursor = match decision {
        super::Decision::NestedSlice { .. } => false,
        super::Decision::Cursor { .. } => true,
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::Slice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::Box(_)
        | super::Decision::Degraded(_) => false,
    };
    if cursor && matches!(verdict, RetentionVerdict::Unknown { .. }) {
        return Err(RawBoundaryBlockReason::TemplateUnavailable);
    }
    Ok(())
}

fn template_for_source_form(
    template: BridgeTemplate,
    source_shape: &str,
    source_type: &str,
    target: &RawTargetType,
) -> BridgeTemplate {
    if target.depth2.is_none()
        && source_shape == "raw-expr"
        && matches!(
            source_type.trim_start(),
            ty if ty.starts_with("*mut ") || ty.starts_with("*const ")
        )
    {
        BridgeTemplate::TypedRawTemporary
    } else {
        template
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RawBoundaryDispositionIndex {
    return_independent:
        BTreeMap<RawBoundarySiteKey, super::slice_return_evidence::ReturnIndependence>,
    by_site: BTreeMap<RawBoundarySiteKey, RawBoundaryDisposition>,
    negative_write: BTreeMap<RawBoundarySiteKey, NegativeWriteEvidence>,
    render_sites: BTreeMap<RawBoundarySiteKey, RawBoundaryRenderSite>,
    site_lookup: Vec<((LocalDefId, HirId), Span, usize, RawBoundarySiteKey)>,
    open_nodes: FxHashSet<(LocalDefId, HirId)>,
    handled_nodes: FxHashSet<(LocalDefId, HirId)>,
    blocked_nodes: FxHashMap<(LocalDefId, HirId), RawBoundaryBlockReason>,
    address_open_nodes: FxHashSet<(LocalDefId, HirId)>,
    address_sites: Vec<AddressViewSite>,
    address_classes: FxHashMap<(LocalDefId, HirId), super::emitability::AddressUseClass>,
    certificate_replay_wall_s: f64,
    returned_children: BTreeMap<RawBoundarySiteKey, ReturnedChildSiteEvidence>,
    /// Per site: can the callee hand a pointer back, by return or by output
    /// storage? Carried from the site facts so the terminal emission can ask
    /// the same question the disposition asked.
    callee_may_yield_pointer: BTreeMap<RawBoundarySiteKey, bool>,
    /// K18'/OAP-CHILD-ACCESS, carried per site so the terminal emission asks
    /// the same question the disposition asked.
    type_backed_child_access: BTreeMap<RawBoundarySiteKey, super::returned_child::ChildAccess>,
    /// **Wave-6o (relay 018 §1, R304-2).** Null-init-family locals whose
    /// boundary site would be a PENDING sibling-overlap row if delivered — a
    /// stated hold the family consults before delivering.
    pending_sibling_sources: FxHashSet<(LocalDefId, HirId)>,
}

impl RawBoundaryDispositionIndex {
    pub(crate) fn return_independent(
        &self,
        key: &RawBoundarySiteKey,
    ) -> Option<&super::slice_return_evidence::ReturnIndependence> {
        self.return_independent.get(key)
    }

    pub(crate) fn with_pending_sibling_sources(
        mut self,
        sources: FxHashSet<(LocalDefId, HirId)>,
    ) -> Self {
        self.pending_sibling_sources = sources;
        self
    }

    pub(crate) fn pending_sibling_source(&self, node: (LocalDefId, HirId)) -> bool {
        self.pending_sibling_sources.contains(&node)
    }

    /// Fails closed: a site with no recorded answer is treated as able to
    /// yield a pointer.
    pub(crate) fn callee_may_yield_pointer(&self, key: &RawBoundarySiteKey) -> bool {
        self.callee_may_yield_pointer
            .get(key)
            .copied()
            .unwrap_or(true)
    }

    /// K18'/OAP-CHILD-ACCESS, so the terminal emission asks the same question
    /// the disposition asked.
    pub(crate) fn type_backed_child_access_for(
        &self,
        key: &RawBoundarySiteKey,
    ) -> Option<&super::returned_child::ChildAccess> {
        self.type_backed_child_access.get(key)
    }

    pub(crate) fn returned_child_evidence(
        &self,
        key: &RawBoundarySiteKey,
    ) -> Option<&ReturnedChildSiteEvidence> {
        self.returned_children.get(key)
    }

    pub(crate) fn derive(
        site_facts: &RawBoundarySiteFacts,
        retention: &RetentionSummaries,
        hypothetical: &super::DecisionTable,
        emitability: &super::emitability::EmitabilityFacts,
        mut_facts: &crate::analyses::borrow_ownership::mutability_facts::MutFacts,
    ) -> Self {
        let decisions = hypothetical
            .entries
            .iter()
            .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), (subject, decision)))
            .collect::<FxHashMap<_, _>>();
        let mut out = Self::default();
        let mut certificate_replay_wall_s = 0.0f64;
        let mut open_nodes = FxHashMap::<(LocalDefId, HirId), Vec<bool>>::default();
        let mut handled_nodes = FxHashMap::<(LocalDefId, HirId), Vec<bool>>::default();
        for site in &site_facts.sites {
            out.callee_may_yield_pointer
                .insert(site.key.clone(), site.callee_may_yield_pointer);
            if let Some(node) = site.node
                && let Some(access) = retention.type_backed_child_access(node.0, &site.key)
            {
                out.type_backed_child_access
                    .insert(site.key.clone(), access.clone());
            }
            let mut mutable_binding_required = false;
            let disposition: Result<RawBoundaryDisposition, (RawBoundaryBlockReason, String)> =
                (|| {
                    let node = site.node.ok_or_else(|| {
                        (
                            RawBoundaryBlockReason::SubjectUnrooted,
                            "site has no subject root".to_owned(),
                        )
                    })?;
                    if site.target.depth2.is_some() && site.direct_storage_span.is_none() {
                        return Err((
                            RawBoundaryBlockReason::Depth2StorageShape,
                            "depth-2 out-param storage is not a direct variable local".to_owned(),
                        ));
                    }
                    let (subject, decision) = decisions.get(&node).copied().ok_or_else(|| {
                        (
                            RawBoundaryBlockReason::SubjectNotSafe,
                            "hypothetical has no safe subject decision".to_owned(),
                        )
                    })?;
                    let source_stays_raw = match decision {
                        super::Decision::Degraded(_) => true,
                        super::Decision::Ref { .. }
                        | super::Decision::InferredRef { .. }
                        | super::Decision::Slice { .. }
                        | super::Decision::Opt { .. }
                        | super::Decision::Box(_)
                        | super::Decision::NestedSlice { .. }
                        | super::Decision::Cursor { .. } => false,
                    };
                    if source_stays_raw
                        && let Some(source_mutability) = site.adapter_operand_mutability
                        && source_mutability != site.target.mutability
                    {
                        let template = if site.target.mutability == RawMutability::Mut {
                            BridgeTemplate::RawCastMut
                        } else {
                            BridgeTemplate::RawCastConst
                        };
                        return Ok(RawBoundaryDisposition::T1 {
                            template,
                            evidence: "raw-pointer-mutability-cast".to_owned(),
                        });
                    }
                    if let Some((owner, reason)) = box_site_owner(decision, site) {
                        return Ok(RawBoundaryDisposition::OwnedByOtherArm { owner, reason });
                    }
                    let contract = super::cursor_native::foreign::for_decision(
                        decision,
                        &site.key.callee,
                        site.key.argument_index,
                        &site.target,
                    );
                    let returned_child = contract
                        .as_ref()
                        .ok()
                        .filter(|contract| {
                            contract.returns_alias_of == Some(site.key.argument_index)
                        })
                        .map(|_| {
                            let mut child = retention.returned_child_at(node.0, &site.key);
                            // A local that was initialized from a raw field may
                            // itself have been converted. Exemption belongs to
                            // the original field-load expression at this call.
                            child.raw_field_parent &= site.source_shape == "raw-expr";
                            out.returned_children
                                .insert(site.key.clone(), child.clone());
                            child
                        });
                    let (
                        mut retention_verdict,
                        ownership,
                        negative_write,
                        mut evidence,
                        negative_detail,
                    ) = match contract {
                        Ok(contract) => (
                            RetentionVerdict::NoRetain {
                                certificate: RetentionCertificate {
                                    function: site.key.callee.path.clone(),
                                    argument_index: site.key.argument_index,
                                    steps: Vec::new(),
                                    attestation: "boundary-contract",
                                    frame_bounded: None,
                                },
                            },
                            Some(contract.ownership),
                            (contract.access == super::raw_boundary_contracts::PointeeAccess::Read)
                                .then_some(NegativeWriteEvidence::LibcReadOnly),
                            format!(
                                "contract:{};negative-write={}",
                                contract.provenance,
                                if contract.access
                                    == super::raw_boundary_contracts::PointeeAccess::Read
                                {
                                    NegativeWriteEvidence::LibcReadOnly.key()
                                } else {
                                    "none"
                                }
                            ),
                            format!("libc-access={}", contract.access.key()),
                        ),
                        Err(super::raw_boundary_contracts::ContractFailure::PositionUnmodeled)
                            if site.callee_local.is_none() =>
                        {
                            (
                                RetentionVerdict::Unknown {
                                    reason: RetentionUnknownReason::OpenBoundary,
                                    frontier: Vec::new(),
                                },
                                None,
                                None,
                                "foreign-retention-unknown".to_owned(),
                                "foreign-contract-missing".to_owned(),
                            )
                        }
                        Err(super::raw_boundary_contracts::ContractFailure::NotForeign)
                            if site.callee_local.is_some() =>
                        {
                            let callee = site.callee_local.expect("guarded local callee");
                            let local = Local::from_usize(site.key.argument_index + 1);
                            let foster_immutable = !mut_facts.is_defaulted(callee, local)
                                && !mut_facts.is_mutable(callee, local);
                            (
                                crate::bo_rewriter::wave6r_child_access::site_retention(
                                    retention, node.0, &site.key, callee,
                                )
                                .unwrap_or(
                                    RetentionVerdict::Unknown {
                                        reason: RetentionUnknownReason::LocalSummaryUnknown,
                                        frontier: Vec::new(),
                                    },
                                ),
                                None,
                                foster_immutable.then_some(NegativeWriteEvidence::FosterImmutable),
                                format!(
                                    "local-retention-summary;negative-write={}",
                                    if foster_immutable {
                                        NegativeWriteEvidence::FosterImmutable.key()
                                    } else {
                                        "none"
                                    }
                                ),
                                if mut_facts.is_defaulted(callee, local) {
                                    "foster-defaulted".to_owned()
                                } else if mut_facts.is_mutable(callee, local) {
                                    "foster-mutable".to_owned()
                                } else {
                                    "foster-immutable".to_owned()
                                },
                            )
                        }
                        Err(error) => {
                            return Err((
                                RawBoundaryBlockReason::ContractInvalid,
                                format!("{error:?}"),
                            ));
                        }
                    };
                    if let Some(evidence) = negative_write {
                        out.negative_write.insert(site.key.clone(), evidence);
                    }
                    // A borrowed element/projection is a reference view even
                    // when its owning subject is a slice or Option slice.
                    // Select its template before applying the R-B gate, so a
                    // shared projection cannot inherit the base's mutability.
                    let reference_view = outbound_reference_view(decision, site.source_shape);
                    let reference_view = crate::bo_rewriter::wave6r_shared_root::disposition_view(
                        emitability,
                        site,
                        node,
                        decision,
                        reference_view,
                    );
                    if let Some(returned) = &returned_child {
                        let child = returned.child.as_ref().ok();
                        if let Some(sink) = child.and_then(|child| child.outward_sinks.first()) {
                            return Err((
                                RawBoundaryBlockReason::PositiveRetention,
                                format!(
                                    "returned-child-sink:{}:_{}:{:?}",
                                    location_label(sink.location),
                                    sink.local.as_u32(),
                                    sink.kind
                                ),
                            ));
                        }
                        if !returned.raw_field_parent {
                            returned_child_permission(
                                reference_view.as_ref().unwrap_or(decision),
                                child.map(|child| &child.access),
                            )
                            .map_err(|failure| {
                                (
                                    RawBoundaryBlockReason::ReturnedChildPermission,
                                    format!("returned-child-permission:{failure:?}"),
                                )
                            })?;
                        }
                        let state = child
                            .map(|child| child.initial.state)
                            .unwrap_or(super::return_alias::ReturnUseState::Unknown);
                        evidence.push_str(&format!(";returned-alias-parent={};returned-use={};child-permission={};lookup={}",
                            site.key.argument_index, state.key(), if returned.raw_field_parent { "raw-field-value" } else { "checked-effective-source" },
                            returned.child.as_ref().err().copied().unwrap_or("exact")));
                        let reason = match state {
                            super::return_alias::ReturnUseState::Unused => None,
                            super::return_alias::ReturnUseState::Used => {
                                Some(RetentionUnknownReason::ReturnedAliasUsed)
                            }
                            super::return_alias::ReturnUseState::Unknown => {
                                Some(RetentionUnknownReason::ReturnedAliasUnknown)
                            }
                        };
                        if let Some(reason) = reason {
                            retention_verdict = RetentionVerdict::Unknown {
                                reason,
                                frontier: Vec::new(),
                            };
                        }
                    }
                    let mut template = if returned_child
                        .as_ref()
                        .is_some_and(|child| child.raw_field_parent)
                    {
                        Ok(BridgeTemplate::TypedRawTemporary)
                    } else {
                        template_for(
                            reference_view.as_ref().unwrap_or(decision),
                            &site.target,
                            ownership,
                            negative_write.is_some(),
                        )
                    }
                    .map_err(|reason| {
                        let detail = if reason == RawBoundaryBlockReason::SharedToMut {
                            format!("negative-write-absent:{negative_detail}")
                        } else {
                            "template-preflight".to_owned()
                        };
                        (reason, detail)
                    })?;
                    template = template_for_source_form(
                        template,
                        site.source_shape,
                        &site.source_type,
                        &site.target,
                    );
                    let independent_return =
                        (matches!(
                            super::seam::form_of(decision),
                            super::seam::Form::Slice { .. }
                        ) && matches!(retention_verdict, RetentionVerdict::NoRetain { .. }))
                        .then(|| site_facts.forward_return_independent.get(&site.key))
                        .flatten();
                    if let Some(proof) = independent_return {
                        evidence.push_str(&format!(";{proof}"));
                        out.return_independent
                            .insert(site.key.clone(), proof.clone());
                    }
                    if let Some(returned) = &returned_child
                        && !returned.raw_field_parent
                    {
                        let selected = returned_child_template(
                            reference_view.as_ref().unwrap_or(decision),
                            &site.target,
                            returned.child.as_ref().ok().map(|child| &child.access),
                            template,
                        )
                        .map_err(|reason| {
                            (
                                reason,
                                "returned-child-writable-const-view-unavailable".to_owned(),
                            )
                        })?;
                        template = selected.template;
                        mutable_binding_required = selected.mutable_binding_required;
                    } else if returned_child.is_none() {
                        // Addendum 259. Without a contract row there is no
                        // returned-child evidence, and absence of evidence was
                        // being read as evidence of absence: the block above
                        // never ran and a `*const` position received `as_ptr()`
                        // however the callee used what it got. A pointer
                        // derived from a shared-reference view of non-UnsafeCell
                        // bytes may never be written through, whether or not the
                        // parent reference is still live, so the seam decides
                        // on the source's own mutability.
                        let view = reference_view.as_ref().unwrap_or(decision);
                        // K18'/OAP-CHILD-ACCESS: what the caller actually does
                        // with a pointer this callee may hand back. Absent this,
                        // every shared subject holds on "no evidence"; with it,
                        // an unused or read-only child stays admitted.
                        let child_access = retention.type_backed_child_access(node.0, &site.key);
                        if site.target.mutability == RawMutability::Const
                            && is_mutable_safe_source(view)
                        {
                            // (1) A writable derivation satisfies the const
                            // parameter type and keeps write permission, so the
                            // mutable case costs no hold at all. The shared
                            // presentation of a mutable subject is retired here.
                            match returned_child_template(
                                view,
                                &site.target,
                                child_access,
                                template,
                            ) {
                                Ok(selected) => {
                                    template = selected.template;
                                    mutable_binding_required = selected.mutable_binding_required;
                                }
                                // The writable carrier does not exist for this
                                // base -- a raw expression derived from a safe
                                // root, or depth-2 storage. Hold only where the
                                // callee could actually hand a pointer back.
                                Err(reason) if site.callee_may_yield_pointer => {
                                    return Err((
                                        reason,
                                        "ordinary-argument-permission:writable-carrier-unavailable"
                                            .to_owned(),
                                    ));
                                }
                                Err(_) => {}
                            }
                        } else if is_shared_safe_source(view)
                            && site.callee_may_yield_pointer
                            && contract.is_err()
                            && independent_return.is_none()
                            && returned_child_permission(view, child_access).is_err()
                            && !super::returned_child_descent::no_child_can_descend(
                                &retention_verdict,
                                site.callee_local.is_some_and(|callee| {
                                    retention.pointee_pointer_free(callee, site.key.argument_index)
                                }),
                            )
                            // wave-6v2 (R406-6 / R410-3): no descendant can
                            // reach the caller except through frame-confined
                            // storage — by the callee's signature AND by its
                            // body: no pointer derived from the argument is
                            // stored anywhere but such storage.
                            && !(site.descendants_frame_confined
                                && site.callee_local.is_some_and(|callee| {
                                    retention.descendant_free(
                                        callee,
                                        site.key.argument_index,
                                        &site.frame_confined_outputs,
                                    )
                                }))
                            // wave-6v2 (R412-7): the descendant a Return-only
                            // callee hands back is the caller's own alias; the
                            // caller's row (continued) shows whether it ever
                            // WRITES through the subject or any alias of it.
                            && !(site.callee_local.is_some_and(|callee| {
                                retention.returns_argument_only(callee, site.key.argument_index)
                            }) && match subject.kind {
                                super::SubjectKind::Param { hir_index } => {
                                    retention.no_write_through(node.0, hir_index)
                                }
                                _ => false,
                            })
                        {
                            // **R283-3 widened this arm to `*mut` positions.**
                            // It used to run only at `*const` targets, so a
                            // shared subject reaching a contract-less callee's
                            // `*mut` parameter was bridged
                            // `from_ref(x).cast_mut()` with no descendant check
                            // at all — the R277-1 gap, 173 sites at J''. The
                            // negative-write evidence that admitted those is
                            // Foster immutability, which describes what the
                            // CALLEE writes through the pointee; it is not a
                            // statement about a child the callee hands back.
                            // The K18' type-backed walk is the same evidence
                            // here as at `*const`, so it is asked the same
                            // question.
                            // (2) A shared subject has no mutable view to
                            // upgrade to. Negative-write evidence does not
                            // discharge this: it says the callee does not write
                            // through the pointee, and says nothing about what
                            // the CALLER may do with a descendant.
                            //
                            // A pinned contract row IS descendant evidence:
                            // `returns_alias_of` names the argument a callee
                            // hands back, so a row that does not name this one
                            // proves no child descends from it. `strlen` is the
                            // case that makes this matter -- it returns
                            // `usize`, which the carrier walk correctly calls
                            // pointer-width, and without this guard every
                            // modeled read-only libc position would hold.
                            return Err((
                                RawBoundaryBlockReason::ReturnedChildPermission,
                                "ordinary-argument-permission:write-through-shared-view".to_owned(),
                            ));
                        }
                    }
                    cursor_retention_permit(decision, &retention_verdict).map_err(|reason| {
                        (reason, "cursor-retention-unknown-unlicensed".to_owned())
                    })?;
                    match retention_verdict {
                        RetentionVerdict::NoRetain { certificate } => {
                            let certificate_started = std::time::Instant::now();
                            let certificate_invalid = site.callee_local.is_some()
                                && crate::bo_rewriter::wave6r_child_access::verify_certificate(
                                    retention,
                                    node.0,
                                    &site.key,
                                    site.callee_local.expect("local"),
                                    &certificate,
                                )
                                .is_err();
                            certificate_replay_wall_s +=
                                certificate_started.elapsed().as_secs_f64();
                            if certificate_invalid {
                                return Err((
                                    RawBoundaryBlockReason::ContractInvalid,
                                    "retention-certificate-invalid".to_owned(),
                                ));
                            }
                            Ok(RawBoundaryDisposition::T1 { template, evidence })
                        }
                        RetentionVerdict::Retains { sink, .. } => {
                            // wave-6v2 (R406-6): retention into caller-owned
                            // stack storage that never escapes the caller is
                            // discharged — the referent dies with the caller's
                            // frame — and the parameter takes the verdict it
                            // would carry without those sinks: T1 when the
                            // rest is clean, the waiver path when the rest is
                            // unknown.
                            let discharged = site.callee_local.and_then(|callee| {
                                retention
                                    .output_storage_discharge(callee, site.key.argument_index)
                                    .filter(|(outputs, _)| {
                                        outputs.iter().all(|index| {
                                            site.frame_confined_outputs.contains(index)
                                        })
                                    })
                            });
                            match discharged {
                                Some((outputs, RetentionVerdict::NoRetain { .. })) => {
                                    evidence = format!(
                                        "{evidence};stack-storage-certificate:outputs={outputs:?}"
                                    );
                                    Ok(RawBoundaryDisposition::T1 { template, evidence })
                                }
                                Some((outputs, RetentionVerdict::Unknown { reason, .. })) => {
                                    evidence = format!(
                                        "{evidence};stack-storage-certificate:outputs={outputs:?}"
                                    );
                                    Ok(RawBoundaryDisposition::T2 {
                                        template,
                                        reason,
                                        waiver_id: RAW_BOUNDARY_WAIVER_ID,
                                        evidence,
                                    })
                                }
                                // wave-6v2 (R412-7): a local callee that only
                                // returns the argument hands the alias to the
                                // caller, whose own row accounts for it; the
                                // site is T2 `ReturnedAliasUsed`. (A discarded
                                // result is wave-6r's T1 arm, above.) A caller
                                // that WRITES through the returned alias keeps
                                // wave-6r's positive retention (their
                                // `kept_by_caller` pin): the tier is for a
                                // caller whose own row only reads through it.
                                Some((_, RetentionVerdict::Retains { .. })) | None
                                    if site.callee_local.is_some_and(|callee| {
                                        retention
                                            .returns_argument_only(callee, site.key.argument_index)
                                    }) && match subject.kind {
                                        super::SubjectKind::Param { hir_index } => {
                                            retention.no_write_through(node.0, hir_index)
                                        }
                                        _ => false,
                                    } =>
                                {
                                    evidence = format!("{evidence};returned-alias-used");
                                    Ok(RawBoundaryDisposition::T2 {
                                        template,
                                        reason: RetentionUnknownReason::ReturnedAliasUsed,
                                        waiver_id: RAW_BOUNDARY_WAIVER_ID,
                                        evidence,
                                    })
                                }
                                Some((_, RetentionVerdict::Retains { .. })) | None => Err((
                                    RawBoundaryBlockReason::PositiveRetention,
                                    format!("{sink:?}"),
                                )),
                            }
                        }
                        RetentionVerdict::Unknown { reason, .. } => {
                            Ok(RawBoundaryDisposition::T2 {
                                template,
                                reason,
                                waiver_id: RAW_BOUNDARY_WAIVER_ID,
                                evidence,
                            })
                        }
                    }
                })();
            let disposition = disposition.unwrap_or_else(|(reason, detail)| {
                RawBoundaryDisposition::Blocked { reason, detail }
            });
            let box_slice = site
                .node
                .and_then(|node| decisions.get(&node).map(|(_, decision)| *decision))
                .is_some_and(|decision| match decision {
                    super::Decision::Box(plan) => plan.shape == super::box_facts::BoxShape::Slice,
                    super::Decision::Ref { .. }
                    | super::Decision::InferredRef { .. }
                    | super::Decision::Slice { .. }
                    | super::Decision::Opt { .. }
                    | super::Decision::NestedSlice { .. }
                    | super::Decision::Cursor { .. }
                    | super::Decision::Degraded(_) => false,
                });
            let target_stays_raw = site.callee_local.is_none_or(|callee| {
                hypothetical
                    .entries
                    .iter()
                    .find_map(|(subject, decision)| {
                        let super::SubjectKind::Param { hir_index } = subject.kind else {
                            return None;
                        };
                        (subject.fn_did == callee && hir_index == site.key.argument_index)
                            .then_some(match decision {
                                super::Decision::Degraded(_) => true,
                                super::Decision::Ref { .. }
                                | super::Decision::InferredRef { .. }
                                | super::Decision::Slice { .. }
                                | super::Decision::Opt { .. }
                                | super::Decision::Box(_)
                                | super::Decision::NestedSlice { .. }
                                | super::Decision::Cursor { .. } => false,
                            })
                    })
                    .unwrap_or(true)
            });
            out.render_sites.insert(
                site.key.clone(),
                RawBoundaryRenderSite {
                    span: site.source_span,
                    direct_storage_span: site.direct_storage_span,
                    adapter_operand_span: site.adapter_operand_span,
                    call_span: site.call_span,
                    target: site.target.clone(),
                    box_slice,
                    source_shape: site.source_shape,
                    source_site: site.source_site.clone(),
                    node: site.node,
                    callee_local: site.callee_local,
                    target_stays_raw,
                    mutable_binding_required,
                    subject_identity: site
                        .node
                        .and_then(|node| decisions.get(&node).map(|(subject, _)| *subject))
                        .map_or_else(
                            || format!("{}::{}", site.key.caller, site.key.subject),
                            |subject| subject.identity_key(&site.key.caller),
                        ),
                },
            );
            if let Some(node) = site.node {
                let opens_arm_a = disposition.is_open() && target_stays_raw;
                let handled = match &disposition {
                    RawBoundaryDisposition::OwnedByOtherArm { .. } => true,
                    _ => disposition.is_handled() && target_stays_raw,
                };
                open_nodes.entry(node).or_default().push(opens_arm_a);
                if super::mixed_boundary::site_votes(target_stays_raw, &disposition) {
                    handled_nodes.entry(node).or_default().push(handled);
                }
                out.site_lookup.push((
                    node,
                    site.source_span.source_callsite(),
                    site.key.argument_index,
                    site.key.clone(),
                ));
                if let RawBoundaryDisposition::Blocked { reason, .. } = &disposition {
                    out.blocked_nodes.entry(node).or_insert(*reason);
                }
            }
            out.by_site.insert(site.key.clone(), disposition);
        }
        for failure in &site_facts.failures {
            if let Some(node) = failure.node {
                open_nodes.entry(node).or_default().push(false);
                handled_nodes.entry(node).or_default().push(false);
                out.blocked_nodes
                    .entry(node)
                    .or_insert(RawBoundaryBlockReason::SiteUnresolved);
            }
        }
        for (node, verdicts) in open_nodes {
            if !verdicts.is_empty() && verdicts.into_iter().all(|open| open) {
                out.open_nodes.insert(node);
            }
        }
        for (node, verdicts) in handled_nodes {
            if !verdicts.is_empty() && verdicts.into_iter().all(|handled| handled) {
                out.handled_nodes.insert(node);
            }
        }
        for observation in &emitability.address_observations {
            // Wave-6o: an EQUALITY operand that is not a safe subject (no
            // decision, or a degraded one) keeps its raw text; the safe
            // operands still receive their views. Ordering keeps the
            // all-operands rule: a cursor shape is not opened here.
            let raw_partner = |operand: &super::emitability::AddressOperand| {
                matches!(observation.op, "eq" | "ne")
                    && decisions
                        .get(&operand.node)
                        .is_none_or(|(_, decision)| match decision {
                            super::Decision::Degraded(_) => true,
                            super::Decision::Ref { .. }
                            | super::Decision::InferredRef { .. }
                            | super::Decision::Slice { .. }
                            | super::Decision::Opt { .. }
                            | super::Decision::Box(_)
                            | super::Decision::NestedSlice { .. }
                            | super::Decision::Cursor { .. } => false,
                        })
            };
            if observation.operands.is_empty()
                || observation.operands.iter().all(raw_partner)
                || !observation.operands.iter().all(|operand| {
                    raw_partner(operand)
                        || emitability.address_use_class(operand.node)
                            == super::emitability::AddressUseClass::ValueOnly
                })
            {
                continue;
            }
            let mut views = Vec::with_capacity(observation.operands.len());
            let mut viewed = 0usize;
            for (operand_index, operand) in observation.operands.iter().enumerate() {
                if raw_partner(operand) {
                    continue;
                }
                viewed += 1;
                let Some((_, decision)) = decisions.get(&operand.node).copied() else {
                    views.clear();
                    break;
                };
                let target = operand.target.clone();
                let Ok(template) = template_for(decision, &target, None, true) else {
                    views.clear();
                    break;
                };
                views.push(AddressViewSite {
                    owner: site_facts
                        .sites
                        .iter()
                        .find(|site| site.node == Some(operand.node))
                        .map_or_else(
                            || observation.owner.local_def_index.as_u32().to_string(),
                            |site| site.key.caller.clone(),
                        ),
                    span: operand.span,
                    node: operand.node,
                    template,
                    target,
                    op: observation.op,
                    operand_index,
                    bridge_kind: match observation.op {
                        "ptr-to-int" | "ptr-cast" => "raw-op-cast-sink",
                        "ptr-eq" => "raw-op-ptr-eq",
                        _ => "raw-op-address-view",
                    },
                    target_type: observation.target_type.clone(),
                });
            }
            if views.len() != viewed {
                continue;
            }
            for view in &views {
                out.address_open_nodes.insert(view.node);
            }
            out.address_sites.extend(views);
        }
        out.address_sites.sort_by_key(|site| {
            (
                site.node.0.local_def_index.as_u32(),
                site.node.1.local_id.as_u32(),
                site.span.lo(),
                site.span.hi(),
            )
        });
        let mut address_nodes = emitability
            .raw_only_uses
            .keys()
            .copied()
            .collect::<FxHashSet<_>>();
        address_nodes.extend(
            emitability
                .address_observations
                .iter()
                .flat_map(|observation| observation.operands.iter().map(|operand| operand.node)),
        );
        out.address_classes = address_nodes
            .into_iter()
            .map(|node| (node, emitability.address_use_class(node)))
            .collect();
        out.site_lookup.sort_by(|left, right| {
            (
                left.0.0.local_def_index.as_u32(),
                left.0.1.local_id.as_u32(),
                left.1.lo(),
                left.1.hi(),
                left.2,
                &left.3,
            )
                .cmp(&(
                    right.0.0.local_def_index.as_u32(),
                    right.0.1.local_id.as_u32(),
                    right.1.lo(),
                    right.1.hi(),
                    right.2,
                    &right.3,
                ))
        });
        out.certificate_replay_wall_s = certificate_replay_wall_s;
        out
    }

    pub(crate) fn disposition(&self, key: &RawBoundarySiteKey) -> Option<&RawBoundaryDisposition> {
        self.by_site.get(key)
    }

    pub(crate) fn emission_sites(
        &self,
    ) -> impl Iterator<
        Item = (
            &RawBoundarySiteKey,
            &RawBoundaryDisposition,
            &RawBoundaryRenderSite,
        ),
    > {
        self.inventoried_sites()
            .filter(|(_, _, site)| site.target_stays_raw)
    }

    pub(crate) fn inventoried_sites(
        &self,
    ) -> impl Iterator<
        Item = (
            &RawBoundarySiteKey,
            &RawBoundaryDisposition,
            &RawBoundaryRenderSite,
        ),
    > {
        self.by_site.iter().filter_map(|(key, disposition)| {
            self.render_sites
                .get(key)
                .map(|site| (key, disposition, site))
        })
    }

    pub(crate) fn negative_write_evidence(
        &self,
        key: &RawBoundarySiteKey,
    ) -> Option<NegativeWriteEvidence> {
        self.negative_write.get(key).copied()
    }

    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from(
            "caller\tblock\tstatement_index\tcallee\targument_index\tsubject\tsubject_identity\tsource_site\ttarget_stays_raw\tsite_owner\ttier\ttemplate\twaiver_id\tevidence\treason\tdetail\tatom_group\n",
        );
        let atom_groups = self.subject_atom_groups();
        for (key, disposition) in &self.by_site {
            let (template, waiver, evidence, reason, detail, site_owner) = match disposition {
                RawBoundaryDisposition::T1 { template, evidence } => {
                    (template.key(), "-", evidence.as_str(), "-", "-", "arm-a")
                }
                RawBoundaryDisposition::T2 {
                    template,
                    reason,
                    waiver_id,
                    evidence,
                } => (
                    template.key(),
                    *waiver_id,
                    evidence.as_str(),
                    reason.key(),
                    "-",
                    "arm-a",
                ),
                RawBoundaryDisposition::Blocked { reason, detail } => {
                    ("-", "-", "-", reason.key(), detail.as_str(), "blocked")
                }
                RawBoundaryDisposition::OwnedByOtherArm { owner, reason } => {
                    ("-", "-", "-", *reason, "-", *owner)
                }
            };
            let render = self.render_sites.get(key);
            let subject_identity = render.map_or("-", |site| site.subject_identity.as_str());
            let atom_group = render
                .and_then(|site| site.node)
                .map(|node| {
                    atom_groups
                        .get(&node)
                        .into_iter()
                        .flatten()
                        .map(|atom| atom.id.as_str())
                        .collect::<Vec<_>>()
                        .join(";")
                })
                .filter(|group| !group.is_empty())
                .unwrap_or_else(|| "-".to_owned());
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                key.caller,
                key.block,
                key.statement_index,
                key.callee.path,
                key.argument_index,
                key.subject,
                subject_identity,
                render.map_or("-", |site| site.source_site.as_str()),
                render.map_or("-", |site| if site.target_stays_raw { "1" } else { "0" }),
                site_owner,
                disposition.tier(),
                template,
                waiver,
                evidence,
                reason,
                detail,
                atom_group,
            ));
        }
        out
    }

    pub(crate) fn address_sites(&self) -> &[AddressViewSite] {
        &self.address_sites
    }

    pub(crate) fn opens_address(&self, node: (LocalDefId, HirId)) -> bool {
        self.address_open_nodes.contains(&node)
    }

    pub(crate) fn addresses_tsv(&self, tcx: TyCtxt<'_>) -> String {
        let mut out = String::from(
            "owner\tlocal_def_index\thir_local_id\tuse_class\trealized_edit_count\tops\n",
        );
        let mut classes = self.address_classes.iter().collect::<Vec<_>>();
        classes
            .sort_by_key(|(node, _)| (node.0.local_def_index.as_u32(), node.1.local_id.as_u32()));
        for (&node, &class) in classes {
            let sites = self
                .address_sites
                .iter()
                .filter(|site| site.node == node)
                .collect::<Vec<_>>();
            let ops = sites
                .iter()
                .map(|site| site.op)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join(";");
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\n",
                tcx.def_path_str(node.0.to_def_id()),
                node.0.local_def_index.as_u32(),
                node.1.local_id.as_u32(),
                class.key(),
                sites.len(),
                if ops.is_empty() { "-" } else { &ops },
            ));
        }
        out
    }

    pub(crate) fn certificate_replay_wall_s(&self) -> f64 {
        self.certificate_replay_wall_s
    }

    pub(crate) fn atoms_tsv(&self) -> String {
        let groups = self.subject_atom_groups();
        let mut rows = groups
            .values()
            .flatten()
            .map(|atom| {
                (
                    atom.id.clone(),
                    format!(
                        "{}\t{}\t{}\t{}\n",
                        atom.id,
                        atom.owner,
                        atom.node.0.local_def_index.as_u32(),
                        atom.node.1.local_id.as_u32()
                    ),
                )
            })
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| left.0.cmp(&right.0));
        let mut out = String::from("atom_id\towner\tlocal_def_index\thir_local_id\n");
        for (_, row) in rows {
            out.push_str(&row);
        }
        out
    }

    /// Exact site atoms grouped by the subject whose safe declaration and use
    /// edits they jointly justify. Every consumer receives the already-sorted
    /// group; none reconstructs dependency closure from rendered text.
    pub(crate) fn subject_atom_groups(
        &self,
    ) -> FxHashMap<(LocalDefId, HirId), Vec<SubjectAtomKey>> {
        let mut groups = FxHashMap::<(LocalDefId, HirId), Vec<SubjectAtomKey>>::default();
        for (key, disposition) in &self.by_site {
            if !disposition.is_open() {
                continue;
            }
            let Some(site) = self
                .render_sites
                .get(key)
                .filter(|site| site.target_stays_raw)
            else {
                continue;
            };
            let Some(node) = site.node else {
                continue;
            };
            groups.entry(node).or_default().push(SubjectAtomKey {
                id: site_atom_id(key),
                node,
                owner: key.caller.clone(),
            });
        }
        for site in &self.address_sites {
            groups.entry(site.node).or_default().push(SubjectAtomKey {
                id: address_atom_id(site),
                node: site.node,
                owner: site.owner.clone(),
            });
        }
        for atoms in groups.values_mut() {
            atoms.sort_by(|left, right| left.id.cmp(&right.id));
            atoms.dedup_by(|left, right| left.id == right.id);
        }
        groups
    }

    pub(crate) fn opens_node(&self, node: (LocalDefId, HirId)) -> bool {
        self.open_nodes.contains(&node)
    }

    fn handles_site(&self, key: &RawBoundarySiteKey) -> bool {
        match self.by_site.get(key) {
            Some(RawBoundaryDisposition::OwnedByOtherArm { .. }) => true,
            Some(RawBoundaryDisposition::T1 { .. } | RawBoundaryDisposition::T2 { .. }) => self
                .render_sites
                .get(key)
                .is_some_and(|site| site.target_stays_raw),
            Some(RawBoundaryDisposition::Blocked { .. }) | None => false,
        }
    }

    pub(crate) fn node_dispositions(
        &self,
        node: (LocalDefId, HirId),
    ) -> Vec<(&RawBoundarySiteKey, &RawBoundaryDisposition)> {
        let mut rows = self
            .render_sites
            .iter()
            .filter_map(|(key, site)| {
                (site.node == Some(node))
                    .then(|| self.by_site.get(key).map(|disposition| (key, disposition)))
                    .flatten()
            })
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| left.0.cmp(right.0));
        rows
    }

    pub(crate) fn opens_span(&self, node: (LocalDefId, HirId), span: Span) -> bool {
        let span = span.source_callsite();
        self.handled_nodes.contains(&node)
            && self
                .site_lookup
                .iter()
                .any(|(candidate, site_span, _, key)| {
                    *candidate == node
                        && (site_span.contains(span) || span.contains(*site_span))
                        && self.handles_site(key)
                })
    }

    /// wave-6f (W6F-2): is THIS escape site handled by a raw-boundary bridge
    /// (T1 / T2 with the target staying raw), whatever the node's other sites
    /// do? An escape through a foreign or indirect call is discharged by the
    /// receipted bridge at that call; the node's other sites (a raw expression
    /// rooted at it, passed to a converting local callee) are the seam's, and
    /// their own gates still apply.
    pub(crate) fn opens_escape_site(&self, node: (LocalDefId, HirId), span: Span) -> bool {
        let span = span.source_callsite();
        self.site_lookup
            .iter()
            .any(|(candidate, site_span, _, key)| {
                *candidate == node
                    && (site_span.contains(span) || span.contains(*site_span))
                    && self.handles_site(key)
            })
    }

    pub(crate) fn opens_argument(
        &self,
        node: (LocalDefId, HirId),
        span: Span,
        argument_index: usize,
    ) -> bool {
        let span = span.source_callsite();
        self.handled_nodes.contains(&node)
            && self
                .site_lookup
                .iter()
                .any(|(candidate, site_span, index, key)| {
                    *candidate == node
                        && *index == argument_index
                        && (site_span.contains(span) || span.contains(*site_span))
                        && self.handles_site(key)
                })
    }

    /// Whether this exact argument is in the T1/T2 boundary market, including
    /// a site whose final surface makes the raw bridge syntax a no-op. PAIR
    /// still owes an A5 proof receipt for that identity; unlike
    /// [`Self::opens_argument`], this observation does not claim the site is an
    /// active Arm-A edit.
    pub(crate) fn tracks_call_argument(
        &self,
        caller: LocalDefId,
        callee_path: &str,
        span: Span,
        argument_index: usize,
    ) -> bool {
        let span = span.source_callsite();
        self.site_lookup
            .iter()
            .any(|(candidate, site_span, index, key)| {
                candidate.0 == caller
                    && key.callee.path == callee_path
                    && *index == argument_index
                    && (site_span.contains(span) || span.contains(*site_span))
                    && self
                        .by_site
                        .get(key)
                        .is_some_and(RawBoundaryDisposition::is_open)
            })
    }

    pub(crate) fn block_reason(&self, node: (LocalDefId, HirId)) -> Option<RawBoundaryBlockReason> {
        self.blocked_nodes.get(&node).copied()
    }
}

/// Select the one MIR call which represents an already-resolved HIR call site.
/// The resolved callee of the one matching candidate, when there is exactly
/// one. Ambiguity and absence answer `None`, and the carrier question then
/// fails closed at the caller.
fn unique_candidate<'c>(
    expected: &ForeignSymbolKey,
    candidates: &'c [MirCallCandidate],
) -> Option<&'c MirCallCandidate> {
    let mut matching = candidates.iter().filter(|site| site.callee == *expected);
    let site = matching.next()?;
    matching.next().is_none().then_some(site)
}

/// Zero and multiple matches stay typed rather than choosing by traversal
/// order.
pub(crate) fn select_unique_site(
    expected: &ForeignSymbolKey,
    candidates: &[MirCallCandidate],
) -> Result<(u32, u32), SiteMatchFailure> {
    let mut matching = candidates.iter().filter(|site| site.callee == *expected);
    let Some(site) = matching.next() else {
        return Err(if candidates.is_empty() {
            SiteMatchFailure::Missing
        } else {
            SiteMatchFailure::CalleeMismatch
        });
    };
    if matching.next().is_some() {
        return Err(SiteMatchFailure::Ambiguous);
    }
    Ok((site.block, site.statement_index))
}

#[cfg(test)]
mod tests {
    use rustc_hir::def_id::CRATE_DEF_ID;

    use super::*;

    fn constructed_child_access() -> (
        super::super::returned_child::ChildAccess,
        super::super::returned_child::ChildAccess,
        super::super::returned_child::ChildAccess,
    ) {
        use super::super::returned_child::*;
        let location = Location {
            block: rustc_middle::mir::BasicBlock::from_u32(1),
            statement_index: 0,
        };
        let local = Local::from_u32(2);
        (
            ChildAccess::Writes {
                sites: vec![ChildWriteSite {
                    location,
                    local,
                    kind: ChildWriteKind::PointeeStore,
                }],
                unknown_frontiers: Vec::new(),
            },
            ChildAccess::Unknown {
                frontiers: vec![ChildFrontier {
                    location,
                    local: Some(local),
                    reason: ChildUnknownReason::OpaquePointerUse,
                    callee: None,
                    argument_index: None,
                }],
            },
            ChildAccess::ReadOnly {
                checked_uses: vec![CheckedChildUse {
                    location,
                    local,
                    kind: ChildUseKind::PointeeRead,
                }],
            },
        )
    }

    #[test]
    fn rb_retalias_policy_shared_const_target_forbids_child_writes() {
        // Constructed policy input, not a model-admission or emitted-output claim.
        let source = super::super::Decision::Ref { mutable: false };
        let target = RawTargetType {
            rendered: "*const i8".into(),
            pointee: "i8".into(),
            mutability: RawMutability::Const,
            depth2: None,
        };
        assert!(
            template_for(&source, &target, None, true).is_ok(),
            "the immediate const view alone permits this source"
        );
        let (writes, _, _) = constructed_child_access();
        assert_eq!(
            returned_child_permission(&source, Some(&writes)),
            Err(ReturnedChildPermissionFailure::Writes)
        );
    }

    #[test]
    fn rb_retalias_policy_shared_const_target_forbids_unknown_child_access() {
        // Constructed policy input, independent of whether this model admits a shared source.
        let source = super::super::Decision::Ref { mutable: false };
        let target = RawTargetType {
            rendered: "*const i8".into(),
            pointee: "i8".into(),
            mutability: RawMutability::Const,
            depth2: None,
        };
        assert!(template_for(&source, &target, None, true).is_ok());
        let (_, unknown, _) = constructed_child_access();
        assert_eq!(
            returned_child_permission(&source, Some(&unknown)),
            Err(ReturnedChildPermissionFailure::Unknown)
        );
        assert_eq!(
            returned_child_permission(&source, None),
            Err(ReturnedChildPermissionFailure::Unknown)
        );
    }

    #[test]
    fn rb_retalias_policy_complete_readonly_and_unused_children_preserve_permission() {
        // A complete typed access witness is required; absence of a write row is insufficient.
        let source = super::super::Decision::Ref { mutable: false };
        let (_, _, readonly) = constructed_child_access();
        assert_eq!(returned_child_permission(&source, Some(&readonly)), Ok(()));
        assert_eq!(
            returned_child_permission(
                &source,
                Some(&super::super::returned_child::ChildAccess::Unused)
            ),
            Ok(())
        );
    }

    #[test]
    fn rb_retalias_policy_mutable_and_raw_sources_have_no_shared_parent_obligation() {
        // Both forms are explicit policy inputs, not forced frozen decisions.
        let mutable = super::super::Decision::Ref { mutable: true };
        let raw = super::super::Decision::Degraded(super::super::Degradation {
            subject: "constructed-raw-policy-input".into(),
            site: "policy".into(),
            reason: super::super::DegradeReason::KindRaw,
        });
        let (writes, unknown, _) = constructed_child_access();
        for source in [&mutable, &raw] {
            assert_eq!(returned_child_permission(source, Some(&writes)), Ok(()));
            assert_eq!(returned_child_permission(source, Some(&unknown)), Ok(()));
        }
    }

    fn constructed_writable_const_bridge(
        source: super::super::Decision,
        declaration: &str,
        unknown: bool,
        expected_view: &str,
        mutable_binding_required: bool,
    ) {
        // This is a constructed consumer input, not a frozen-model admission.
        let target = RawTargetType {
            rendered: "*const i8".into(),
            pointee: "i8".into(),
            mutability: RawMutability::Const,
            depth2: None,
        };
        let (writes, unknown_access, _) = constructed_child_access();
        let access = if unknown { &unknown_access } else { &writes };
        assert_eq!(returned_child_permission(&source, Some(access)), Ok(()));
        let base =
            template_for(&source, &target, None, true).expect("existing const-target template");
        let selected = returned_child_template(&source, &target, Some(access), base)
            .expect("mutable consumer permission");
        let BridgeRender::Edit(expression) = selected
            .template
            .render_explicit("p", RawMutability::Const, false, Some("i8"))
            .unwrap()
        else {
            panic!("writable returned-child origin requires an explicit adapter");
        };
        let emitted = format!(
            "#![allow(unused_mut, dead_code)]\nextern \"C\" {{ fn strchr(p: *const i8, c: i32) -> *mut i8; }}\nunsafe fn caller({declaration}) {{ let child = strchr({expression}, 0); if !child.is_null() {{ *child = 1; }} }}"
        );
        assert!(
            crate::bo_rewriter::verify::type_checks_str(&emitted),
            "{emitted}"
        );
        assert!(
            expression.contains(expected_view) && expression.contains(".cast_const()"),
            "const ABI adapter discarded writable provenance: {expression}"
        );
        assert!(
            !expression.contains("from_ref") && !expression.contains(".as_deref()"),
            "shared view remains: {expression}"
        );
        assert_eq!(
            selected.mutable_binding_required, mutable_binding_required,
            "mutable Option view must expose its binding requirement"
        );
    }

    #[test]
    fn rb_retalias_writable_const_ref_child_write_keeps_mutable_origin() {
        constructed_writable_const_bridge(
            super::super::Decision::Ref { mutable: true },
            "p: &mut i8",
            false,
            "core::ptr::from_mut",
            false,
        );
    }

    #[test]
    fn rb_retalias_writable_const_slice_unknown_child_keeps_mutable_origin() {
        constructed_writable_const_bridge(
            super::super::Decision::Slice {
                mutable: true,
                uses: Vec::new(),
            },
            "p: &mut [i8]",
            true,
            ".as_mut_ptr()",
            false,
        );
    }

    #[test]
    fn rb_retalias_writable_const_option_ref_child_write_requires_mutable_binding() {
        constructed_writable_const_bridge(
            super::super::Decision::Opt {
                mutable: true,
                slice: false,
                uses: Vec::new(),
            },
            "mut p: Option<&mut i8>",
            false,
            ".as_deref_mut()",
            true,
        );
    }

    #[test]
    fn rb_retalias_writable_const_option_slice_unknown_child_requires_mutable_binding() {
        constructed_writable_const_bridge(
            super::super::Decision::Opt {
                mutable: true,
                slice: true,
                uses: Vec::new(),
            },
            "mut p: Option<&mut [i8]>",
            true,
            ".as_deref_mut()",
            true,
        );
    }

    #[test]
    fn rb_retalias_writable_const_readonly_child_keeps_existing_adapter() {
        let source = super::super::Decision::Ref { mutable: true };
        let target = RawTargetType {
            rendered: "*const i8".into(),
            pointee: "i8".into(),
            mutability: RawMutability::Const,
            depth2: None,
        };
        let (_, _, readonly) = constructed_child_access();
        let base = template_for(&source, &target, None, true).unwrap();
        let selected = returned_child_template(&source, &target, Some(&readonly), base).unwrap();
        assert_eq!(selected.template, base);
        assert!(!selected.mutable_binding_required);
    }

    #[test]
    fn rb_retalias_source_proven_field_load_is_distinct_from_slice_and_offset_views() {
        let source = r#"
            extern "C" { fn strchr(p: *const i8, needle: i32) -> *mut i8; }
            pub struct Holder { pub p: *const i8 }
            pub unsafe fn raw_field(holder: *const Holder) { let _ = strchr((*holder).p as *const i8, 0); }
            pub unsafe fn slice_view(slice: &[i8]) { let _ = strchr(slice.as_ptr(), 0); }
            pub unsafe fn offset_view(pointer: *const i8) { let _ = strchr(pointer.offset(1), 0); }
        "#;
        let observed = ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let mut observed = BTreeMap::new();
            for function in &program.functions {
                let name = tcx.item_name(function.to_def_id()).to_string();
                if !matches!(name.as_str(), "raw_field" | "slice_view" | "offset_view") {
                    continue;
                }
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(*function)
                    .borrow();
                let calls = body
                    .basic_blocks
                    .iter_enumerated()
                    .filter_map(|(block, data)| {
                        let TerminatorKind::Call { func, args, .. } = &data.terminator().kind
                        else {
                            return None;
                        };
                        let callee = operand_callee(func)?;
                        (tcx.item_name(callee).as_str() == "strchr").then_some((
                            Location {
                                block,
                                statement_index: data.statements.len(),
                            },
                            plain_operand_local(&args[0].node)
                                .expect("real pointer argument local"),
                        ))
                    })
                    .collect::<Vec<_>>();
                let [(call, parent)] = calls.as_slice() else {
                    panic!("one real strchr call required for {name}")
                };
                assert!(matches!(
                    body.local_decls[*parent].ty.kind(),
                    TyKind::RawPtr(..)
                ));
                observed.insert(
                    name,
                    returned_parent_is_raw_field_load(tcx, &body, *call, *parent),
                );
            }
            observed
        })
        .expect("source-form provenance controls compile");
        assert_eq!(
            observed.get("slice_view"),
            Some(&false),
            "existing Slice borrow cannot be treated as a raw field value"
        );
        assert_eq!(
            observed.get("offset_view"),
            Some(&false),
            "offset provenance cannot be treated as a raw field value"
        );
        assert_eq!(
            observed.get("raw_field"),
            Some(&true),
            "exact projected pointer-value load must not inherit container permission"
        );
    }

    #[test]
    fn rb_retalias_returned_child_sink_is_positive_without_attestation() {
        let source = r#"
            extern "C" { fn strchr(p: *const i8, needle: i32) -> *mut i8; }
            pub unsafe fn keep(p: *const i8, output: *mut *mut i8) {
                let child = strchr(p, 0);
                let copied = child;
                *output = copied;
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.item_name(function.to_def_id()).as_str() == "keep")
                .unwrap();
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let calls = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    let TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } = &data.terminator().kind
                    else {
                        return None;
                    };
                    let callee = operand_callee(func)?;
                    (tcx.item_name(callee).as_str() == "strchr").then_some((
                        block,
                        args,
                        destination,
                        callee,
                    ))
                })
                .collect::<Vec<_>>();
            let [(call_block, args, destination, callee)] = calls.as_slice() else {
                panic!("one real strchr call required")
            };
            let mut parent =
                plain_operand_local(&args[0].node).expect("plain compiler argument temporary");
            let mut visited = BTreeSet::new();
            while parent != Local::from_u32(1) {
                assert!(
                    visited.insert(parent.as_u32()),
                    "parent copy chain must be acyclic"
                );
                let definitions = body.basic_blocks[*call_block]
                    .statements
                    .iter()
                    .filter_map(|statement| {
                        let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                            return None;
                        };
                        (lhs.as_local() == Some(parent)).then_some(rhs)
                    })
                    .collect::<Vec<_>>();
                let [rhs] = definitions.as_slice() else {
                    panic!(
                        "parent temporary requires one pre-call definition: _{}",
                        parent.as_u32()
                    )
                };
                let source = transparent_operand(rhs)
                    .and_then(plain_operand_local)
                    .expect("transparent parent copy/cast");
                assert!(
                    matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                        && matches!(body.local_decls[parent].ty.kind(), TyKind::RawPtr(..))
                );
                parent = source;
            }
            let child = destination
                .as_local()
                .expect("real plain-local returned child");
            assert!(matches!(
                body.local_decls[child].ty.kind(),
                TyKind::RawPtr(..)
            ));
            let key = symbol_key(tcx, *callee, &program.functions);
            let target = raw_target_type(
                tcx,
                tcx.fn_sig(*callee).skip_binder().skip_binder().inputs()[0],
            )
            .unwrap();
            assert_eq!(
                super::super::raw_boundary_contracts::classify_contract(&key, 0, &target)
                    .unwrap()
                    .returns_alias_of,
                Some(0)
            );
            let mut copies = Vec::new();
            let mut stores = Vec::new();
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else { continue };
                    let Some(source) = transparent_operand(rhs).and_then(plain_operand_local)
                    else {
                        continue;
                    };
                    if let Some(destination) = lhs.as_local() {
                        if matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                            && matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                        {
                            copies.push((source, destination));
                        }
                    } else if lhs.local == Local::from_u32(2) && !lhs.projection.is_empty() {
                        stores.push(source);
                    }
                }
            }
            let mut reachable = BTreeSet::from([child.as_u32()]);
            loop {
                let before = reachable.len();
                for (source, destination) in &copies {
                    if reachable.contains(&source.as_u32()) {
                        reachable.insert(destination.as_u32());
                    }
                }
                if before == reachable.len() {
                    break;
                }
            }
            assert!(
                copies.iter().any(|(source, _)| *source == child),
                "real child-copy edge required"
            );
            assert!(
                stores
                    .iter()
                    .any(|source| reachable.contains(&source.as_u32())),
                "copied returned child must reach real outward storage"
            );
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let summaries = RetentionSummaries::derive(&program, Some(&origins), None);
            assert!(
                matches!(
                    summaries.get(function, 0),
                    Some(RetentionVerdict::Retains { .. })
                ),
                "positive returned-child sink was hidden by absent attestation: {:?}",
                summaries.get(function, 0)
            );
        })
        .expect("returned-child sink fixture compiles");
    }

    fn retention_of(
        src: &str,
        function_suffix: &str,
        attestation: Option<WholeProgramAttestation>,
    ) -> (RetentionVerdict, Result<(), &'static str>) {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| {
                    tcx.def_path_str(function.to_def_id())
                        .ends_with(function_suffix)
                })
                .expect("fixture function");
            let summaries = RetentionSummaries::derive(&program, Some(&origins), attestation);
            let verdict = summaries
                .get(function, 0)
                .expect("argument summary")
                .clone();
            let verification = match &verdict {
                RetentionVerdict::NoRetain { certificate } => {
                    summaries.verify_certificate(function, 0, certificate)
                }
                _ => Err("not-a-certificate"),
            };
            (verdict, verification)
        })
        .expect("fixture compiles")
    }

    fn copied_local_retention_of(
        source: &str,
        attestation: Option<WholeProgramAttestation>,
    ) -> RetentionVerdict {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.item_name(function.to_def_id()).as_str() == "target")
                .expect("copied-local fixture function");
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let destination = body
                .var_debug_info
                .iter()
                .find_map(|info| {
                    if info.name.as_str() != "copied" {
                        return None;
                    }
                    match &info.value {
                        rustc_middle::mir::VarDebugInfoContents::Place(place) => place.as_local(),
                        _ => None,
                    }
                })
                .expect("named copied destination retains its MIR identity");
            assert!(
                destination.as_usize() > body.arg_count,
                "control must query a local, not a parameter"
            );
            // Positive MIR sinks do not need an origin solve or a whole-graph
            // no-retention certificate. Missing origins keeps ordinary
            // parameter rows Unknown, including the dependency controls.
            let summaries = RetentionSummaries::derive(&program, None, attestation);
            summaries.copied_local_retention(&program, function, destination)
        })
        .expect("copied-local retention fixture compiles")
    }

    #[test]
    fn rb_r210_local_copy_field_store_is_positive_unattested() {
        let verdict = copied_local_retention_of(
            "#![allow(dead_code, unused_assignments)]\n\
             struct Holder { saved: *const i32 }\n\
             unsafe fn target(seed: *const i32) -> Holder {\n\
                 let copied = seed; let alias = copied;\n\
                 let mut holder = Holder { saved: core::ptr::null() };\n\
                 holder.saved = alias; holder\n\
             }",
            None,
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Retains {
                    sink: RetentionStep {
                        kind: RetentionEventKind::FieldOrGlobalStore,
                        ..
                    },
                    ..
                }
            ),
            "local-to-local field escape became unknown: {verdict:?}"
        );
    }

    #[test]
    fn rb_r210_local_copy_return_is_positive_unattested() {
        let verdict = copied_local_retention_of(
            "unsafe fn target(seed: *const i32) -> *const i32 {\n\
                 let copied = seed; let alias = copied; alias\n\
             }",
            None,
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Retains {
                    sink: RetentionStep {
                        kind: RetentionEventKind::Return,
                        ..
                    },
                    ..
                }
            ),
            "local-to-local return escape became unknown: {verdict:?}"
        );
    }

    #[test]
    fn rb_r210_local_copy_aggregate_store_is_positive_unattested() {
        let verdict = copied_local_retention_of(
            "#![allow(dead_code)]\n\
             struct Holder { saved: *const i32 }\n\
             unsafe fn target(seed: *const i32) -> Holder {\n\
                 let copied = seed; let alias = copied; Holder { saved: alias }\n\
             }",
            None,
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Retains {
                    sink: RetentionStep {
                        kind: RetentionEventKind::FieldOrGlobalStore,
                        ..
                    },
                    ..
                }
            ),
            "aggregate field escape became unknown: {verdict:?}"
        );
    }

    #[test]
    fn rb_r210_local_copy_retaining_dependency_is_positive_unattested() {
        let verdict = copied_local_retention_of(
            "#![allow(dead_code)]\n\
             struct Holder { saved: *const i32 }\n\
             unsafe fn store(p: *const i32, out: *mut Holder) { (*out).saved = p; }\n\
             unsafe fn relay(p: *const i32, out: *mut Holder) { store(p, out); }\n\
             unsafe fn target(seed: *const i32, out: *mut Holder) {\n\
                 let copied = seed; let alias = copied; relay(alias, out);\n\
             }",
            None,
        );
        let RetentionVerdict::Retains { sink, path } = &verdict else {
            panic!("local-call field escape became unknown: {verdict:?}");
        };
        assert_eq!(sink.kind, RetentionEventKind::OutputStorage);
        assert_eq!(
            path.iter()
                .filter(|step| step.kind == RetentionEventKind::LocalCall)
                .count(),
            2,
            "both calls must retain their positive-sink provenance: {path:?}"
        );
    }

    #[test]
    fn rb_r210_local_copy_never_mints_a_no_retention_certificate() {
        let verdict = copied_local_retention_of(
            "unsafe fn target(seed: *const i32) -> i32 {\n\
                 let copied = seed; *copied\n\
             }",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::Unknown { .. }),
            "absence of outward retention cannot license the local alias schedule: {verdict:?}"
        );
    }

    fn symbol(name: &str, foreign: bool) -> ForeignSymbolKey {
        ForeignSymbolKey {
            symbol: name.to_owned(),
            path: format!("fixture::{name}"),
            abi: "C".to_owned(),
            signature: "(*mut i32)->()".to_owned(),
            foreign,
        }
    }

    #[test]
    fn rb_x1_exact_single_call_candidate_builds_owned_key() {
        let expected = symbol("consume", true);
        let site = select_unique_site(
            &expected,
            &[MirCallCandidate {
                block: 7,
                statement_index: 3,
                callee: expected.clone(),
                did: Some(CRATE_DEF_ID.to_def_id()),
                may_yield_pointer: true,
            }],
        );
        assert_eq!(site, Ok((7, 3)));
    }

    #[test]
    fn rb_x1_zero_or_multiple_candidates_fail_closed() {
        let expected = symbol("consume", true);
        assert_eq!(
            select_unique_site(&expected, &[]),
            Err(SiteMatchFailure::Missing)
        );
        let one = MirCallCandidate {
            block: 1,
            statement_index: 0,
            callee: expected.clone(),
            did: Some(CRATE_DEF_ID.to_def_id()),
            may_yield_pointer: true,
        };
        assert_eq!(
            select_unique_site(&expected, &[one.clone(), one]),
            Err(SiteMatchFailure::Ambiguous)
        );
    }

    #[test]
    fn rb_x1_same_spelled_local_is_not_the_foreign_site() {
        let expected = symbol("consume", true);
        let local = symbol("consume", false);
        assert_eq!(
            select_unique_site(
                &expected,
                &[MirCallCandidate {
                    block: 2,
                    statement_index: 1,
                    callee: local,
                    did: Some(CRATE_DEF_ID.to_def_id()),
                    may_yield_pointer: true,
                }],
            ),
            Err(SiteMatchFailure::CalleeMismatch)
        );
    }

    #[test]
    fn rb_x1_target_mutability_is_not_collapsed() {
        assert_ne!(RawMutability::Const, RawMutability::Mut);
    }

    #[test]
    fn rb_x1_foreign_argument_fact_carries_callee_position_and_target_type() {
        let src = r#"
            extern "C" { fn consume(p: *mut i32); }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let fact = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            assert_eq!(
                facts.foreign_call_args.len(),
                1,
                "{:#?}",
                facts.foreign_call_args
            );
            facts.foreign_call_args[0].clone()
        })
        .expect("fixture compiles");
        assert_eq!(fact.callee.symbol, "consume");
        assert!(fact.callee.foreign);
        assert_eq!(fact.argument_index, 0);
        assert_eq!(fact.shape, "bare-local");
        assert_eq!(fact.target.mutability, RawMutability::Mut);
        assert!(fact.target.pointee.contains("i32"), "{fact:#?}");
    }

    #[test]
    fn rb_x1_derived_foreign_site_has_the_exact_mir_location() {
        let src = r#"
            extern "C" { fn consume(p: *mut i32); }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let sites = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            RawBoundarySiteFacts::derive(&program, &facts)
        })
        .expect("fixture compiles");
        assert!(sites.failures.is_empty(), "{sites:#?}");
        assert_eq!(sites.sites.len(), 1, "{sites:#?}");
        let site = &sites.sites[0];
        assert_eq!(site.key.argument_index, 0);
        assert_eq!(site.key.callee.symbol, "consume");
        assert_eq!(site.target.mutability, RawMutability::Mut);
        assert_eq!(sites.to_tsv(), sites.clone().to_tsv());
    }

    #[test]
    fn rb_x1_direct_local_call_uses_the_same_owned_site_domain() {
        let src = r#"
            unsafe fn consume(p: *mut i32) { *p = 1; }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let sites = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            RawBoundarySiteFacts::derive(&program, &facts)
        })
        .expect("fixture compiles");
        assert!(sites.failures.is_empty(), "{sites:#?}");
        assert_eq!(sites.sites.len(), 1, "{sites:#?}");
        assert!(!sites.sites[0].key.callee.foreign);
        assert_eq!(sites.sites[0].key.argument_index, 0);
    }

    #[test]
    fn rb_x1_variadic_raw_argument_keeps_its_position_and_contract() {
        let src = r#"
            extern "C" { fn printf(fmt: *const i8, ...) -> i32; }
            unsafe fn caller(fmt: *const i8, p: *const i8) { printf(fmt, p); }
        "#;
        let facts = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            super::super::emitability::collect(tcx, &program.functions).foreign_call_args
        })
        .expect("fixture compiles");
        assert_eq!(facts.len(), 2, "{facts:#?}");
        assert_eq!(facts[1].argument_index, 1);
        assert_eq!(
            super::super::raw_boundary_contracts::classify_contract(
                &facts[1].callee,
                facts[1].argument_index,
                &facts[1].target,
            )
            .expect("printf vararg contract")
            .retention,
            super::super::raw_boundary_contracts::RetentionContract::NoRetain
        );
    }

    #[test]
    fn rb_w2_local_pointee_access_without_escape_has_a_verified_certificate() {
        let (verdict, verification) = retention_of(
            "unsafe fn no_retain(p: *mut i32) { let _ = *p; *p = 1; }",
            "no_retain",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::NoRetain { .. }),
            "{verdict:#?}"
        );
        assert_eq!(verification, Ok(()));
    }

    #[test]
    fn rb_w3_returned_pointer_is_positive_retention() {
        let (verdict, _) = retention_of(
            "unsafe fn returns(p: *mut i32) -> *mut i32 { p }",
            "returns",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Retains {
                    sink: RetentionStep {
                        kind: RetentionEventKind::Return,
                        ..
                    },
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_w10_missing_attestation_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn no_retain(p: *mut i32) { let _ = *p; }",
            "no_retain",
            None,
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::AttestationAbsent,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n1_multi_definition_alias_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn branch(p: *mut i32, q: *mut i32, flag: bool) { let mut x = p; if flag { x = q; } let _ = *x; }",
            "branch",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::MultiDef,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n2_function_pointer_call_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn indirect(p: *mut i32, cb: unsafe fn(*mut i32)) { cb(p); }",
            "indirect",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::FnPtrWeb,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n3_positive_retention_never_collapses_to_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn returns(p: *mut i32) -> *mut i32 { p }",
            "returns",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::Retains { .. }),
            "{verdict:#?}"
        );
    }

    #[test]
    fn retention_unknown_reason_vocabulary_is_exact_and_exhaustive() {
        assert_eq!(
            RetentionUnknownReason::ALL.map(RetentionUnknownReason::key),
            [
                "retention-callee-unresolved",
                "retention-fnptr-web",
                "retention-open-boundary",
                "retention-multi-def",
                "retention-nontransparent-def",
                "retention-projection-ambiguous",
                "retention-output-storage",
                "retention-field-or-global-store",
                "retention-return",
                "retention-local-summary-unknown",
                "retention-attestation-absent",
                "retention-analysis-incomplete",
                "retention-returned-alias-used",
                "retention-returned-alias-unknown",
            ]
        );
    }

    #[test]
    fn local_no_retain_summary_propagates_to_its_caller() {
        let (verdict, verification) = retention_of(
            "unsafe fn leaf(p: *mut i32) { *p = 1; } unsafe fn wrapper(p: *mut i32) { leaf(p); }",
            "wrapper",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::NoRetain { .. }),
            "{verdict:#?}"
        );
        assert_eq!(verification, Ok(()));
    }

    #[test]
    fn rb_w5_optional_mutable_ref_bridge_is_one_evaluation_without_unwrap() {
        let rendered = BridgeTemplate::OptRefMutToRawMut
            .render("p", RawMutability::Mut, false, Some("i32"))
            .expect("optional bridge");
        let BridgeRender::Edit(text) = rendered else {
            panic!("expected edit, got {rendered:?}");
        };
        assert_eq!(text.matches("p.").count(), 1, "{text}");
        assert!(text.contains("as_deref_mut"), "{text}");
        assert!(!text.contains("unwrap"), "{text}");
    }

    #[test]
    fn rb_w6_shared_source_to_mutable_target_is_typed_block() {
        let target = RawTargetType {
            rendered: "*mut i32".to_owned(),
            pointee: "i32".to_owned(),
            mutability: RawMutability::Mut,
            depth2: None,
        };
        assert_eq!(
            template_for(
                &super::super::Decision::Ref { mutable: false },
                &target,
                None,
                false,
            ),
            Err(RawBoundaryBlockReason::SharedToMut)
        );
        assert_eq!(
            RawBoundaryBlockReason::SharedToMut.key(),
            "raw-boundary-shared-to-mut"
        );
    }

    #[test]
    fn rb_x3_read_only_family_permission_has_an_explicit_shared_to_mut_bridge() {
        let target = RawTargetType {
            rendered: "*mut i8".to_owned(),
            pointee: "i8".to_owned(),
            mutability: RawMutability::Mut,
            depth2: None,
        };
        let template = template_for(
            &super::super::Decision::Ref { mutable: false },
            &target,
            Some(super::super::raw_boundary_contracts::OwnershipContract::BorrowView),
            true,
        )
        .expect("ruled family bridge");
        assert_eq!(template, BridgeTemplate::RefSharedToRawMut);
        let BridgeRender::Edit(text) = template
            .render("p", RawMutability::Mut, false, None)
            .expect("explicit bridge")
        else {
            panic!("shared-to-mut family bridge must emit syntax");
        };
        assert!(text.contains("core::ptr::from_ref(p)"), "{text}");
        assert!(text.contains(".cast_mut()"), "{text}");
    }

    #[test]
    fn rb_w7_box_borrow_view_does_not_consume_the_owner() {
        let rendered = BridgeTemplate::BoxBorrowViewToRaw
            .render("owner", RawMutability::Mut, false, None)
            .expect("Box view");
        let BridgeRender::Edit(text) = rendered else {
            panic!("expected edit, got {rendered:?}");
        };
        assert_eq!(text, "core::ptr::from_mut(owner.as_mut())");
        assert!(!text.contains("into_raw"), "{text}");
    }

    /// D12-W1 — R172's E0282/E0308 pair came from passing an already-raw cast
    /// to `ptr::from_mut`/`ptr::from_ref`.  A raw temporary keeps its raw value
    /// and receives an explicit target type; it is not treated as a reference.
    #[test]
    fn d12_w1_raw_temporary_has_an_explicit_pointer_type() {
        let target = RawTargetType {
            rendered: "*mut core::ffi::c_void".to_owned(),
            pointee: "core::ffi::c_void".to_owned(),
            mutability: RawMutability::Mut,
            depth2: None,
        };
        assert_eq!(
            template_for_source_form(
                BridgeTemplate::VoidFromMut,
                "raw-expr",
                "*mut core::ffi::c_void",
                &target,
            ),
            BridgeTemplate::TypedRawTemporary
        );
        assert_eq!(
            template_for_source_form(
                BridgeTemplate::VoidFromMut,
                "cast-of-local",
                "*mut core::ffi::c_void",
                &target,
            ),
            BridgeTemplate::VoidFromMut,
            "a rewritten local remains a reference under its cast"
        );
        let rendered = BridgeTemplate::TypedRawTemporary
            .render(
                "p as *mut core::ffi::c_void",
                RawMutability::Mut,
                false,
                Some("core::ffi::c_void"),
            )
            .expect("typed raw temporary");
        let BridgeRender::Edit(text) = rendered else {
            panic!("typed raw temporary must emit syntax: {rendered:?}");
        };
        assert!(
            text.contains("let __crat_raw: *mut core::ffi::c_void"),
            "{text}"
        );
        assert!(
            !text.contains("from_mut") && !text.contains("from_ref"),
            "{text}"
        );
        let source = format!(
            "fn take(_: *mut core::ffi::c_void) {{}}\n\
             fn witness(p: *mut i32) {{ unsafe {{ take({text}); }} }}\n"
        );
        assert!(
            ::utils::compilation::run_compiler_on_str(&source, |_| ()).is_ok(),
            "typed raw bridge must type-check:\n{source}"
        );
    }

    #[test]
    fn rb_w8_known_free_uses_the_existing_lifecycle_path() {
        assert_eq!(
            BridgeTemplate::KnownFreeDrop
                .render("owner", RawMutability::Mut, false, None)
                .expect("lifecycle"),
            BridgeRender::Lifecycle
        );
    }

    #[test]
    fn zero_syntax_ref_bridge_is_receipted_without_an_edit() {
        assert_eq!(
            BridgeTemplate::RefMutToRawMut
                .render("p", RawMutability::Mut, false, None)
                .expect("zero syntax"),
            BridgeRender::ZeroSyntax
        );
    }
}

#[cfg(test)]
#[path = "cursor_raw_tests.rs"]
mod cursor_raw_tests;
