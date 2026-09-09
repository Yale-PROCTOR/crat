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
    let signature = tcx.fn_sig(callee).skip_binder().skip_binder();
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
        Some(Decision::Box(_)) => None,
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
    pub shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
    pub direct_storage: Option<(HirId, Span)>,
    pub adapter_operand_span: Span,
    pub adapter_operand_mutability: Option<RawMutability>,
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
            let callee = operand_callee(func)?;
            let key = symbol_key(tcx, callee, functions);
            let call_span = terminator.source_info.span.source_callsite();
            (key == *expected && call_span.contains(argument_span)).then_some(MirCallCandidate {
                block: block.as_u32(),
                statement_index: data.statements.len() as u32,
                callee: key,
                did: callee,
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
                    callee_may_yield_pointer: unique_candidate_did(&fact.callee, &candidates)
                        .is_none_or(|did| callee_may_yield_pointer(tcx, did)),
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
                            callee_may_yield_pointer: unique_candidate_did(
                                &callee_key,
                                &candidates,
                            )
                            .is_none_or(|did| callee_may_yield_pointer(tcx, did)),
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
    pub did: DefId,
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct RetentionDependency {
    callee: LocalDefId,
    argument_index: usize,
    step: RetentionStep,
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
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RetentionSummaries {
    rows: FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    facts: FxHashMap<(LocalDefId, usize), RetentionBodyFacts>,
    attested: bool,
    returned_children: FxHashMap<LocalDefId, Vec<ReturnedChildRecord>>,
    /// K18'/OAP-CHILD-ACCESS: the same descendant evidence for callees with no
    /// pinned contract row, kept apart so the row stays the authority wherever
    /// it exists.
    type_backed_children: FxHashMap<LocalDefId, Vec<ReturnedChildRecord>>,
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

fn returned_parent_is_raw_field_load<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    call: Location,
    mut parent: Local,
) -> bool {
    fn before(body: &Body<'_>, definition: Location, call: Location) -> bool {
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

fn collect_retention_facts<'tcx>(
    program: &RustProgram<'tcx>,
    function: LocalDefId,
    root: Local,
    argument_index: Option<usize>,
    body: &Body<'tcx>,
    children: &[ReturnedChildRecord],
) -> RetentionBodyFacts {
    let tcx = program.tcx;
    let function_path = tcx.def_path_str(function.to_def_id());
    let mut definitions = vec![0usize; body.local_decls.len()];
    let mut aliases = Vec::<(Local, Local, RetentionStep)>::new();

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
                let output_storage = lhs.local.as_usize() > 0
                    && lhs.local.as_usize() <= body.arg_count
                    && matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
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
                    format!("store _{} through _{}", source.as_u32(), lhs.local.as_u32()),
                );
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
                let step = retention_step(
                    location,
                    RetentionEventKind::LocalCall,
                    format!("{} arg{index}", tcx.def_path_str(callee)),
                );
                facts.dependencies.push(RetentionDependency {
                    callee: local_callee,
                    argument_index: index,
                    step: step.clone(),
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
        },
    }
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
            let next = if matches!(direct, RetentionVerdict::Retains { .. }) {
                direct
            } else if let Some((dependency, sink)) =
                fact.dependencies.iter().find_map(|dependency| {
                    match previous.get(&(dependency.callee, dependency.argument_index)) {
                        Some(RetentionVerdict::Retains { sink, .. }) => {
                            Some((dependency, sink.clone()))
                        }
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
                    previous.get(&(dependency.callee, dependency.argument_index)),
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
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        origins: Option<&OriginSummaries>,
        attestation: Option<WholeProgramAttestation>,
    ) -> Self {
        let attested = attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        let mut facts = FxHashMap::default();
        let mut returned_children = FxHashMap::default();
        let mut type_backed_children = FxHashMap::default();
        for &function in &program.functions {
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
                    ),
                );
            }
            returned_children.insert(function, children);
            type_backed_children.insert(function, type_backed);
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
        Self {
            rows,
            facts,
            attested,
            returned_children,
            type_backed_children,
        }
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
                    "-",
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
    RawCastMut,
    RawCastConst,
    TypedRawTemporary,
    RefMutToRawMut,
    RefMutToRawConst,
    RefMutToWritableRawConst,
    RefSharedToRawConst,
    RefSharedToRawMut,
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
    BoxBorrowViewToRaw,
    KnownFreeDrop,
}

impl BridgeTemplate {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Depth2NpoConst | Self::Depth2NpoMut => "depth2-npo-bridge",
            Self::VoidFromMut | Self::VoidFromRef | Self::VoidFromMutAsConst => "void-generic-raw",
            Self::VoidFromRefCastMut => "shared-ref-to-mut-raw",
            Self::RawCastMut => "raw-cast-mut",
            Self::RawCastConst => "raw-cast-const",
            Self::TypedRawTemporary => "typed-raw-temporary",
            Self::RefMutToRawMut => "ref-mut-to-raw-mut",
            Self::RefMutToRawConst => "ref-mut-to-raw-const",
            Self::RefMutToWritableRawConst => "returned-child-ref-mut-to-raw-const",
            Self::RefSharedToRawConst => "ref-shared-to-raw-const",
            Self::RefSharedToRawMut => "shared-ref-to-mut-raw",
            Self::SliceMutToRawMut => "slice-mut-to-raw-mut",
            Self::SliceToRawConst => "slice-to-raw-const",
            Self::SliceMutToWritableRawConst => "returned-child-slice-mut-to-raw-const",
            Self::SliceToRawMut => "slice-to-raw-mut",
            Self::OptRefMutToRawMut
            | Self::OptRefToRawConst
            | Self::OptRefToRawMut
            | Self::OptSliceToRaw
            | Self::OptSliceToRawMut => "option-to-raw-null-map",
            Self::OptRefMutToWritableRawConst | Self::OptSliceMutToWritableRawConst => {
                "returned-child-option-mut-to-raw-const"
            }
            Self::BoxBorrowViewToRaw => "box-borrow-view-to-raw",
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
            | Self::VoidFromMutAsConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                let source = match self {
                    Self::VoidFromMut => format!("core::ptr::from_mut({argument})"),
                    Self::VoidFromRef => format!("core::ptr::from_ref({argument})"),
                    Self::VoidFromRefCastMut => {
                        format!("core::ptr::from_ref({argument}).cast_mut()")
                    }
                    Self::VoidFromMutAsConst => {
                        format!("core::ptr::from_ref(&*{argument})")
                    }
                    _ => unreachable!(),
                };
                Ok(BridgeRender::Edit(format!("{source}.cast::<{pointee}>()")))
            }
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
        | super::Decision::Box(_) => return Err(RawBoundaryBlockReason::ReturnedChildPermission),
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
        super::Decision::Box(_) | super::Decision::Degraded(_) => None,
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
            Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => Err(RawBoundaryBlockReason::TemplateUnavailable),
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
            } else if plan.shape == BoxShape::Sized || plan.shape == BoxShape::Slice {
                Ok(BridgeTemplate::BoxBorrowViewToRaw)
            } else {
                Err(RawBoundaryBlockReason::TemplateUnavailable)
            }
        }
        Decision::Degraded(_) => Err(RawBoundaryBlockReason::SubjectNotSafe),
    }
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
}

impl RawBoundaryDispositionIndex {
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
                    let (_, decision) = decisions.get(&node).copied().ok_or_else(|| {
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
                        | super::Decision::Box(_) => false,
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
                    let contract = super::raw_boundary_contracts::classify_contract(
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
                                retention
                                    .get(callee, site.key.argument_index)
                                    .cloned()
                                    .unwrap_or(RetentionVerdict::Unknown {
                                        reason: RetentionUnknownReason::LocalSummaryUnknown,
                                        frontier: Vec::new(),
                                    }),
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
                    } else if returned_child.is_none()
                        && site.target.mutability == RawMutability::Const
                    {
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
                        if is_mutable_safe_source(view) {
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
                            && returned_child_permission(view, child_access).is_err()
                        {
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
                    match retention_verdict {
                        RetentionVerdict::NoRetain { certificate } => {
                            let certificate_started = std::time::Instant::now();
                            let certificate_invalid = site.callee_local.is_some()
                                && retention
                                    .verify_certificate(
                                        site.callee_local.expect("local"),
                                        site.key.argument_index,
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
                        RetentionVerdict::Retains { sink, .. } => Err((
                            RawBoundaryBlockReason::PositiveRetention,
                            format!("{sink:?}"),
                        )),
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
                                | super::Decision::Box(_) => false,
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
                handled_nodes.entry(node).or_default().push(handled);
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
            if observation.operands.is_empty()
                || !observation.operands.iter().all(|operand| {
                    emitability.address_use_class(operand.node)
                        == super::emitability::AddressUseClass::ValueOnly
                })
            {
                continue;
            }
            let mut views = Vec::with_capacity(observation.operands.len());
            for (operand_index, operand) in observation.operands.iter().enumerate() {
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
            if views.len() != observation.operands.len() {
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
fn unique_candidate_did(
    expected: &ForeignSymbolKey,
    candidates: &[MirCallCandidate],
) -> Option<DefId> {
    let mut matching = candidates.iter().filter(|site| site.callee == *expected);
    let site = matching.next()?;
    matching.next().is_none().then_some(site.did)
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
                did: CRATE_DEF_ID.to_def_id(),
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
            did: CRATE_DEF_ID.to_def_id(),
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
                    did: CRATE_DEF_ID.to_def_id(),
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
