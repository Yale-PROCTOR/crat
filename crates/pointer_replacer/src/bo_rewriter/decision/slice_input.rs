//! W-C7: slice input propagation.
//!
//! A parameter the fatness analysis already calls an array (`Arr`) but that
//! has no arithmetic of its own — it only forwards its pointer into callee
//! parameters that access past one element — takes the thin `Form::Plain`
//! (the form rule reads the subject's OWN uses) and is then held
//! `held:local-callee-access-extent` (fix-2: a `&T` is a one-element claim and
//! may not be widened at a local callee). When every caller of its function
//! supplies a buffer at that position — an `Arr` subject, or a parameter that
//! is itself supplied this way — the parameter is not a one-element claim but
//! the slice its callers hand it: it takes `&[T]` and the extent travels from
//! the callers as the slice's length. Nothing is widened anywhere: the callers
//! already hold slices, the callees index them with the ordinary bounds check,
//! and a non-array caller anywhere in the closure refuses the whole chain
//! (typed, the hold stays).
use rustc_hir::{
    Expr, ExprKind, HirId,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{
    Subject, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts},
    thin_counted,
};
use crate::bo_rewriter::fat_facts::FatFacts;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Proof {
    /// Every function whose parameter the slice travels through, this one
    /// first; each must keep its SliceUse family for the chain to stand.
    pub members: Vec<LocalDefId>,
    /// Where the slice's extent comes from.
    pub extent: Extent,
}

/// R418-1 (relay 024): the forwarder's extent is evidence-backed only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Extent {
    /// Every caller supplies a slice (W-C7) or a fresh root (W-C9): the
    /// extent travels down as the slice's length.
    Supplied,
    /// The forwarder's OWN companion integer beside the pointer
    /// (`adler32(data, len)`): its callers adapt raw with it, or take the
    /// slice form themselves, or decline typed (`thin-caller-argument`).
    Companion(super::seam::LenEvidence),
    /// **R477-6.** The companion MASKS the index rather than counting the
    /// elements: every index the accessing callee forms is `expr & companion`
    /// (brotli's hash readers, `data.offset((ix & mask) as isize)`), so it is
    /// bounded by the companion whatever `expr` is — and the extent that
    /// covers every one of them is `companion + 1`, not `companion`.
    ///
    /// **What this is evidence of, exactly.** It bounds the INDEXES the callee
    /// forms. A read of several bytes AT such an index — brotli's four- and
    /// eight-byte hash loads — is not bounded by it, and neither is the
    /// allocation, which the signature does not carry. That residue is what
    /// §77's fabricated-extent receipt covers, and every admitted site carries
    /// one (R477-6 rules (a) with (b)'s receipt).
    CompanionMask(super::seam::LenEvidence),
}

impl Extent {
    /// **R425-3: the chain's companion IS count evidence** — the accessing
    /// callee's indexes are bounded by exactly this parameter (checked by
    /// [`index_bound_by_companion`]), which is the same class of evidence as
    /// the thin-count proof's reader walk. The seam reads this index into its
    /// `count_companions` so R408-1's arm licenses the adjacent integer and
    /// nothing fabricated enters through the chain.
    pub(crate) fn companion_index(self, parameter: usize) -> Option<usize> {
        match self {
            Self::Supplied => None,
            Self::Companion(super::seam::LenEvidence::Following)
            | Self::CompanionMask(super::seam::LenEvidence::Following) => Some(parameter + 1),
            Self::Companion(super::seam::LenEvidence::Preceding)
            | Self::CompanionMask(super::seam::LenEvidence::Preceding) => parameter.checked_sub(1),
            Self::Companion(_) | Self::CompanionMask(_) => None,
        }
    }

    /// Does the length this extent licenses need the mask's `+ 1`?
    pub(crate) fn is_mask(self) -> bool {
        matches!(self, Self::CompanionMask(_))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Hold {
    OutsideScope,
    /// The subject reaches a callee parameter that is not a buffer.
    CalleeNotFat,
    /// A caller passes something other than a binding at this position (a
    /// computed pointer, an address, a cast).
    CallerNotSupplied,
    /// A caller's binding at this position is null-tested: its own form is
    /// the thin Option, which the extent hold does not reach.
    CallerNullable,
    /// Not every caller is known, or one is a fn-pointer / exported entry.
    IncompleteCallers,
    /// **R423-6.** An adjacent integer that does not bound the indexes: the
    /// accessing callee reaches its element through ANOTHER parameter
    /// (`bitstream[*bitpointer >> 3]`, the bit-stream readers of report 019
    /// §1's FALSE-companion column), so the integer beside the pointer counts
    /// something else — bits read, one output line — and a slice of that
    /// length under-claims the buffer. Typed decline; the caller stays raw
    /// and adapts under the addendum-77 receipt like every raw caller.
    CompanionNotIndexBound,
}

fn param_index(tcx: TyCtxt<'_>, function: LocalDefId, binding: rustc_hir::HirId) -> Option<usize> {
    tcx.hir_body_owned_by(function)
        .params
        .iter()
        .position(|p| p.pat.hir_id == binding)
}

/// The relay 068 review (F2 / F3): every local's definitions in one body (the
/// `let` initializer, each plain assignment, each compound assignment's
/// operand) and the locals borrowed mutably or captured. A parameter's entry
/// means it is written.
struct Defs<'tcx> {
    values: rustc_hash::FxHashMap<HirId, Vec<(&'tcx Expr<'tcx>, bool)>>,
    borrowed: rustc_hash::FxHashSet<HirId>,
}

impl<'tcx> Defs<'tcx> {
    fn of(tcx: TyCtxt<'tcx>, function: LocalDefId) -> Self {
        struct Collect<'tcx> {
            tcx: TyCtxt<'tcx>,
            defs: Defs<'tcx>,
        }
        fn local(e: &Expr<'_>) -> Option<HirId> {
            let mut e = e;
            loop {
                match e.kind {
                    ExprKind::DropTemps(inner) => e = inner,
                    ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                        return match path.res {
                            Res::Local(id) => Some(id),
                            _ => None,
                        };
                    }
                    _ => return None,
                }
            }
        }
        impl<'tcx> Visitor<'tcx> for Collect<'tcx> {
            fn visit_local(&mut self, let_: &'tcx rustc_hir::LetStmt<'tcx>) {
                if let rustc_hir::PatKind::Binding(mode, id, ..) = let_.pat.kind {
                    if let Some(init) = let_.init {
                        self.defs.values.entry(id).or_default().push((init, false));
                    }
                    if matches!(mode.0, rustc_hir::ByRef::Yes(_)) {
                        self.defs.borrowed.insert(id);
                    }
                }
                intravisit::walk_local(self, let_);
            }

            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                match e.kind {
                    ExprKind::Assign(lhs, rhs, _) => {
                        if let Some(id) = local(lhs) {
                            self.defs.values.entry(id).or_default().push((rhs, false));
                        }
                    }
                    ExprKind::AssignOp(_, lhs, rhs) => {
                        if let Some(id) = local(lhs) {
                            self.defs.values.entry(id).or_default().push((rhs, true));
                        }
                    }
                    ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place) => {
                        if let Some(id) = local(place) {
                            self.defs.borrowed.insert(id);
                        }
                    }
                    ExprKind::Closure(closure) => {
                        if let Some(upvars) = self.tcx.upvars_mentioned(closure.def_id) {
                            self.defs.borrowed.extend(upvars.keys().copied());
                        }
                    }
                    _ => {}
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut collect = Collect {
            tcx,
            defs: Defs {
                values: Default::default(),
                borrowed: Default::default(),
            },
        };
        collect.visit_body(tcx.hir_body_owned_by(function));
        collect.defs
    }

    /// A parameter (or a local) written after entry, or borrowed mutably.
    fn written(&self, id: HirId) -> bool {
        self.values.contains_key(&id) || self.borrowed.contains(&id)
    }
}

/// Relay 068 (R674): the call at `call` in `caller` passes `binding` (through
/// casts) as its `index`-th argument.
fn argument_names(
    tcx: TyCtxt<'_>,
    caller: LocalDefId,
    call: rustc_span::Span,
    index: usize,
    binding: rustc_hir::HirId,
) -> bool {
    struct Find<'tcx> {
        call: rustc_span::Span,
        index: usize,
        found: Option<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if self.found.is_none() && e.span == self.call {
                self.found = match e.kind {
                    ExprKind::Call(_, args) => args.get(self.index),
                    ExprKind::MethodCall(_, receiver, args, _) => match self.index {
                        0 => Some(receiver),
                        k => args.get(k - 1),
                    },
                    _ => None,
                };
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut find = Find {
        call,
        index,
        found: None,
    };
    find.visit_body(tcx.hir_body_owned_by(caller));
    let mut e = match find.found {
        Some(e) => e,
        None => return false,
    };
    loop {
        match e.kind {
            ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                return path.res == Res::Local(binding);
            }
            _ => return false,
        }
    }
}

/// Every position `(function, parameter)` is forwarded into is a fat callee
/// parameter, or a parameter that itself only forwards into fat ones (a
/// forwarder chain); at least one forwarding exists, and a cycle is not fat.
#[allow(clippy::too_many_arguments)]
fn forwards_into_fat(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    binding: rustc_hir::HirId,
    companion: Option<rustc_hir::HirId>,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    visited: &mut Vec<(LocalDefId, usize)>,
    accessed: &mut Vec<(LocalDefId, usize)>,
    unrelated: &mut bool,
) -> Result<(), Hold> {
    let mut forwarded = false;
    // The relay 068 review's F2: a pointer written before it is handed on is
    // not the caller's pointer, and a companion written is not the caller's
    // count.
    let defs = Defs::of(tcx, function);
    let binding_written = defs.written(binding);
    let companion = companion.filter(|c| !defs.written(*c));
    for (&callee, calls) in &facts.call_args {
        for call in calls.iter().filter(|call| call.caller == function) {
            for arg in &call.args {
                let ArgShape::BareLocal(argument) = arg.shape else { continue };
                if argument != binding {
                    continue;
                }
                forwarded = true;
                // Relay 068 (R674) (B): the callee's index test is checked
                // against ITS companion, which bounds the chain's only where
                // the call passes the chain's companion there
                // (`readBitsFromReversedStream(&j, in_0, bitdepth)` does not
                // pass lodepng's `i`).
                let callee_companion = match super::seam::length_evidence(tcx, callee, arg.index) {
                    super::seam::LenEvidence::Following => arg.index.checked_add(1),
                    super::seam::LenEvidence::Preceding => arg.index.checked_sub(1),
                    _ => None,
                };
                let passed = companion
                    .zip(callee_companion)
                    .is_some_and(|(c, k)| argument_names(tcx, function, call.span, k, c));
                let passed = passed && !binding_written;
                let local = Local::from_usize(arg.index + 1);
                if fat.is_array(callee, local) {
                    if !passed {
                        *unrelated = true;
                    }
                    if !accessed.contains(&(callee, arg.index)) {
                        accessed.push((callee, arg.index));
                    }
                    continue;
                }
                if visited.contains(&(callee, arg.index)) {
                    return Err(Hold::CalleeNotFat);
                }
                visited.push((callee, arg.index));
                let params = tcx.hir_body_owned_by(callee).params;
                let param = params[arg.index].pat.hir_id;
                let next = if passed {
                    callee_companion
                        .and_then(|k| params.get(k))
                        .map(|p| p.pat.hir_id)
                } else {
                    None
                };
                forwards_into_fat(
                    tcx, callee, param, next, facts, fat, visited, accessed, unrelated,
                )?;
            }
        }
    }
    if forwarded {
        Ok(())
    } else {
        Err(Hold::CalleeNotFat)
    }
}

fn supplied(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    parameter: usize,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    members: &mut Vec<LocalDefId>,
) -> Result<(), Hold> {
    if members.contains(&function) {
        // A cycle supplies nothing by itself.
        return Err(Hold::CallerNotSupplied);
    }
    members.push(function);
    let calls =
        thin_counted::closed_calls(tcx, function, facts).map_err(|_| Hold::IncompleteCallers)?;
    for call in calls {
        let arg = call
            .args
            .iter()
            .find(|a| a.index == parameter)
            .ok_or(Hold::CallerNotSupplied)?;
        let ArgShape::BareLocal(binding) = arg.shape else {
            return Err(Hold::CallerNotSupplied);
        };
        let uses = facts.raw_only_uses.get(&(call.caller, binding));
        let has = |op: &str| uses.is_some_and(|uses| uses.iter().any(|(use_op, _)| use_op == op));
        if let Some(index) = param_index(tcx, call.caller, binding) {
            // A supplier is a parameter with array evidence of its OWN —
            // arithmetic uses in its function (the form rule decides it a
            // slice there) — or a forwarder that is itself supplied. The
            // flow-insensitive array verdict alone is not enough: a forwarder
            // carries it from its callees.
            if fat.is_array(call.caller, Local::from_usize(index + 1))
                && uses.is_some_and(|uses| {
                    uses.iter().any(|(op, _)| {
                        super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str())
                    })
                })
            {
                continue;
            }
            let reached = members.len();
            match supplied(tcx, call.caller, index, facts, fat, members) {
                Ok(()) => continue,
                Err(Hold::IncompleteCallers | Hold::CallerNotSupplied | Hold::CallerNullable) => {
                    members.truncate(reached);
                }
                Err(hold) => return Err(hold),
            }
        }
        // **W-C9 — a fresh root supplies the chain.** The caller's own
        // allocation local (`BrotliSplitBlock::literals`): a binding whose
        // every definition is a call that takes no pointer — so its value is
        // a fresh allocation, never a borrow of anything thinner — or the
        // null literal. Such a binding never takes the thin form (a fresh
        // pointer has no referent to be a one-element claim on); it is
        // either owning or stays raw, and the call then takes the
        // companion-length adapter — the seam every raw caller of a slice
        // parameter already takes. A null-TESTED root is the thin Option,
        // which no extent hold reaches, so it refuses; anything else that
        // is not a fresh root (a parameter whose own callers refused, a
        // pointer read out of a field) refuses as before.
        if has("is_null") {
            return Err(Hold::CallerNullable);
        }
        if param_index(tcx, call.caller, binding).is_some()
            || !fresh_root(tcx, call.caller, binding)
        {
            return Err(Hold::CallerNotSupplied);
        }
    }
    Ok(())
}

/// A call whose arguments carry no pointer: what it returns was made by the
/// callee, not borrowed from the caller (`xalloc(n)`, `malloc(n)`). Brotli's
/// `BrotliAllocate(m, n)` takes its memory manager and is NOT this shape;
/// it is the allocator contract's (R409-1, wave-6a's consumer).
fn fresh_call(tcx: TyCtxt<'_>, owner: LocalDefId, e: &rustc_hir::Expr<'_>) -> bool {
    use rustc_hir::ExprKind;
    let types = tcx.typeck(owner);
    match e.kind {
        ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => fresh_call(tcx, owner, inner),
        ExprKind::Block(block, _) => match (block.stmts, block.expr) {
            ([], Some(tail)) => fresh_call(tcx, owner, tail),
            _ => false,
        },
        ExprKind::If(_, then, Some(otherwise)) => {
            // `if n > 0 { alloc(n) } else { null }`: one arm allocates, the
            // other may be the null literal; two null arms allocate nothing.
            let then_fresh = fresh_call(tcx, owner, then);
            let otherwise_fresh = fresh_call(tcx, owner, otherwise);
            (then_fresh || otherwise_fresh)
                && (then_fresh || super::emitability::is_zero_literal(then))
                && (otherwise_fresh || super::emitability::is_zero_literal(otherwise))
        }
        ExprKind::Call(_, args) => args.iter().all(|arg| !types.expr_ty(arg).is_any_ptr()),
        _ => false,
    }
}

fn fresh_root(tcx: TyCtxt<'_>, owner: LocalDefId, binding: rustc_hir::HirId) -> bool {
    use rustc_hir::{
        ExprKind, Node,
        def::Res,
        intravisit::{self, Visitor},
    };
    let Node::LetStmt(stmt) = tcx.parent_hir_node(binding) else { return false };
    let Some(init) = stmt.init else { return false };
    if !fresh_call(tcx, owner, init) {
        return false;
    }
    struct Assigned<'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        binding: rustc_hir::HirId,
        refused: bool,
    }
    impl<'tcx> Visitor<'tcx> for Assigned<'tcx> {
        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = e.kind
                && let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = lhs.kind
                && path.res == Res::Local(self.binding)
                && !(fresh_call(self.tcx, self.owner, rhs)
                    || super::emitability::is_zero_literal(rhs))
            {
                self.refused = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut assigned = Assigned {
        tcx,
        owner,
        binding,
        refused: false,
    };
    assigned.visit_body(tcx.hir_body_owned_by(owner));
    !assigned.refused
}

pub(crate) fn prove(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
) -> Result<Proof, Hold> {
    let SubjectKind::Param { hir_index } = subject.kind else { return Err(Hold::OutsideScope) };
    if subject.ptr_depth != 1 || !fat.is_array(subject.fn_did, subject.local) {
        return Err(Hold::OutsideScope);
    }
    let mut accessed = Vec::new();
    let mut unrelated = false;
    let own_param = match super::seam::length_evidence(tcx, subject.fn_did, hir_index) {
        super::seam::LenEvidence::Following => hir_index.checked_add(1),
        super::seam::LenEvidence::Preceding => hir_index.checked_sub(1),
        _ => None,
    }
    .and_then(|k| tcx.hir_body_owned_by(subject.fn_did).params.get(k));
    let own_companion = own_param.map(|p| p.pat.hir_id);
    let own_companion_name = own_param.and_then(|p| match p.pat.kind {
        rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.name.to_string()),
        _ => None,
    });
    forwards_into_fat(
        tcx,
        subject.fn_did,
        subject.hir_id,
        own_companion,
        facts,
        fat,
        &mut vec![(subject.fn_did, hir_index)],
        &mut accessed,
        &mut unrelated,
    )?;
    let mut members = Vec::new();
    match supplied(tcx, subject.fn_did, hir_index, facts, fat, &mut members) {
        Ok(()) => Ok(Proof {
            members,
            extent: Extent::Supplied,
        }),
        // The signature must still be this crate's to change.
        Err(Hold::IncompleteCallers) => Err(Hold::IncompleteCallers),
        Err(hold) => {
            // **The companion may not overrule measured count evidence.** The
            // thin-count rule reads every caller's count against the array it
            // passes; when that read HOLDS on the count itself
            // (`caller-count`: a constant that does not fit the capacity, or a
            // foldable one out of range), the adjacent integer is exactly the
            // number this lane has already refused as an extent. Taking it
            // here would put `from_raw_parts(a.as_ptr(), 19)` on an
            // 18-element array — out of the addendum-77 waiver and into
            // ordinary out-of-bounds UB.
            if matches!(
                thin_counted::prove(tcx, subject, facts),
                Err(thin_counted::Hold::CallerCount)
            ) {
                return Err(hold);
            }
            let evidence = super::seam::length_evidence(tcx, subject.fn_did, hir_index);
            if !matches!(
                evidence,
                super::seam::LenEvidence::Following | super::seam::LenEvidence::Preceding
            ) {
                return Err(hold);
            }
            // R423-6 / R425-3: the companion is the extent only where it
            // BOUNDS the accessing callee's indexes. Checked at every
            // position the chain reaches, so the evidence the seam licenses
            // (`Extent::companion_index`) is the evidence checked here.
            if unrelated {
                return Err(Hold::CompanionNotIndexBound);
            }
            let own_mask_named = own_companion_name
                .as_deref()
                .is_some_and(super::masked_runtime::mask_named);
            // Relay 068 (R674) (A): the subject's own reads are checked too,
            // against its own companion — the extent is that companion
            // (lodepng's `getPixelColorRGBA8` reads `in_0[i]` itself).
            let mut masked = false;
            for &(callee, parameter) in
                std::iter::once(&(subject.fn_did, hir_index)).chain(&accessed)
            {
                match index_bound_by_companion(tcx, callee, parameter) {
                    IndexBound::No => return Err(Hold::CompanionNotIndexBound),
                    IndexBound::MaskedByCompanion => masked = true,
                    IndexBound::MaskUnproven if !own_mask_named => {
                        return Err(Hold::CompanionNotIndexBound);
                    }
                    IndexBound::MaskUnproven | IndexBound::ByCompanion => {}
                }
            }
            Ok(Proof {
                members: vec![subject.fn_did],
                extent: if masked {
                    Extent::CompanionMask(evidence)
                } else {
                    Extent::Companion(evidence)
                },
            })
        }
    }
}

pub(crate) fn enabled_proof(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    policy: &crate::bo_rewriter::additive::FamilyPolicy,
) -> Option<Proof> {
    let proof = prove(tcx, subject, facts, fat).ok()?;
    proof
        .members
        .iter()
        .all(|owner| policy.enabled(*owner, crate::bo_rewriter::additive::FamilyStage::SliceUse))
        .then_some(proof)
}

/// **R758-1 (2) / R763-1 (a) — the thin-into-fat hand-on (main 147 §2).** A
/// subject handed BARE into a callee parameter the fatness analysis calls an
/// array is used as an array there: the hand-on is its array-use op-fact, and
/// its own fatness is the licence (the S3.2′-2 authority split, with the
/// callee's access standing in for the subject's uses). W-C7 above takes such a
/// forwarder only when every caller supplies a buffer; without it the thin form
/// reaches the callee as a one-element `from_ref` / `from_mut` (shape (i),
/// R416-5's defect: the callee indexes past it and panics on a UB-free input)
/// or, at a raw formal, as a one-element reference read past its end (g25,
/// R763-1). The extent comes from where it comes for every slice: the callers
/// that hold one hand it on; the others adapt under §77's receipted fallback
/// (R481). One fat hand-on is enough — a slice also serves a thin formal
/// (`&x[0]`), where a thin form never serves a fat one.
pub(crate) fn hands_on_to_fat(
    subject: &Subject,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    policy: &crate::bo_rewriter::additive::FamilyPolicy,
) -> bool {
    subject.ptr_depth == 1
        && fat.is_array(subject.fn_did, subject.local)
        && policy.enabled(
            subject.fn_did,
            crate::bo_rewriter::additive::FamilyStage::SliceUse,
        )
        && facts.call_args.iter().any(|(&callee, calls)| {
            calls
                .iter()
                .filter(|call| call.caller == subject.fn_did)
                .flat_map(|call| &call.args)
                .any(|arg| {
                    matches!(arg.shape, ArgShape::BareLocal(argument) if argument == subject.hir_id)
                        && fat.is_array(callee, Local::from_usize(arg.index + 1))
                })
        })
}

/// **Does the accessing callee index this parameter under its OWN adjacent
/// companion, and nothing else?**
///
/// `update_adler32(adler, data, len)` indexes `data` by a local `i` bounded by
/// `len`: the companion is the bound. `readBitFromReversedStream(bitpointer,
/// bitstream)` indexes `bitstream` by `*bitpointer >> 3`: the index is reached
/// through ANOTHER parameter, so whatever integer sits beside the pointer
/// counts something else. The test is structural and conservative — an index
/// expression naming any parameter of the accessing function other than its
/// own companion refuses; locals, fields and literals are fine (they are
/// bounded by the callee's own loop, which the extent is what it is checked
/// against). An index naming the companion ITSELF is bounded by it only
/// masked (relay 068: `companion_index`).
/// How the accessing callee's indexes stand to the companion beside the
/// pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IndexBound {
    /// An index reaches the parameter through something the companion does not
    /// bound — another parameter, in the general case.
    No,
    /// Every index is bounded by the companion itself (`i < len`): the extent
    /// is the companion.
    ByCompanion,
    /// **R477-6.** Every index that would otherwise fail the test is MASKED by
    /// the companion (`ix & mask`), so it is bounded whatever it names, and the
    /// extent that covers all of them is `companion + 1`.
    MaskedByCompanion,
    /// The relay 068 review's F4: a mask-named companion whose in-place proof
    /// failed. The seam refuses it as a count only where the chain's own
    /// companion is mask-named; reached from a `len`, it is not bounded.
    MaskUnproven,
}

fn index_bound_by_companion(tcx: TyCtxt<'_>, function: LocalDefId, parameter: usize) -> IndexBound {
    let body = tcx.hir_body_owned_by(function);
    let Some(param) = body.params.get(parameter) else {
        return IndexBound::No;
    };
    let binding = param.pat.hir_id;
    let companion = match super::seam::length_evidence(tcx, function, parameter) {
        super::seam::LenEvidence::Following => parameter.checked_add(1),
        super::seam::LenEvidence::Preceding => parameter.checked_sub(1),
        _ => None,
    };
    // Relay 065 review (finding 6): the in-place proof below is for a MASK,
    // so it reads only a companion whose formal is mask-named.
    let mask_formal = companion
        .and_then(|index| body.params.get(index))
        .is_some_and(|p| {
            matches!(p.pat.kind, rustc_hir::PatKind::Binding(_, _, ident, _)
                if super::masked_runtime::mask_named(ident.name.as_str()))
        });
    let companion = companion.and_then(|index| body.params.get(index).map(|p| p.pat.hir_id));
    let Some(companion) = companion else {
        return IndexBound::No;
    };
    let others: Vec<HirId> = body
        .params
        .iter()
        .map(|p| p.pat.hir_id)
        .filter(|id| *id != binding && *id != companion)
        .collect();

    enum CompanionIndex {
        Masked,
        Below,
        Unbounded,
    }
    /// How an index (or a local's definition) stands to the companion: the
    /// relay 068 review's F3 follows an index's locals to their definitions.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Taint {
        /// Names neither the companion nor another parameter: a loop local, a
        /// field, a literal (the relay: these stay admitted).
        Clean,
        /// Below the companion (`n - c`, `n - 1 - i`).
        Below,
        /// Masked by it (`ix & n`): `n + 1`.
        Masked,
        /// Anything else that names the companion or another parameter.
        Bad,
    }
    fn join(a: Taint, b: Taint) -> Taint {
        match (a, b) {
            (Taint::Bad, _) | (_, Taint::Bad) => Taint::Bad,
            (Taint::Masked, _) | (_, Taint::Masked) => Taint::Masked,
            (Taint::Below, _) | (_, Taint::Below) => Taint::Below,
            _ => Taint::Clean,
        }
    }
    /// The non-parameter locals `e` names.
    fn locals_in(e: &Expr<'_>, params: &[HirId]) -> Vec<HirId> {
        struct Locals<'a> {
            params: &'a [HirId],
            found: Vec<HirId>,
        }
        impl<'tcx> Visitor<'tcx> for Locals<'_> {
            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
                    && let Res::Local(id) = path.res
                    && !self.params.contains(&id)
                    && !self.found.contains(&id)
                {
                    self.found.push(id);
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut locals = Locals {
            params,
            found: Vec::new(),
        };
        locals.visit_expr(e);
        locals.found
    }
    /// `e` is exactly the local `id`, through casts.
    fn exactly(e: &Expr<'_>, id: HirId) -> bool {
        is_binding(e, id)
    }
    /// **The relay 068 review's F1.** `let end = p.offset(n)` whose `end` is
    /// only ever compared (or measured with `offset_from`), never read, never
    /// reassigned: one past the last element, and it reads none.
    fn end_pointer_let<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        defs: &Defs<'tcx>,
        e: &'tcx Expr<'tcx>,
    ) -> bool {
        let rustc_hir::Node::LetStmt(let_) = tcx.parent_hir_node(e.hir_id) else {
            return false;
        };
        let (Some(init), rustc_hir::PatKind::Binding(_, end, ..)) = (let_.init, let_.pat.kind)
        else {
            return false;
        };
        if init.hir_id != e.hir_id
            || defs.borrowed.contains(&end)
            || defs.values.get(&end).map_or(0, |v| v.len()) != 1
        {
            return false;
        }
        struct Uses<'tcx> {
            tcx: TyCtxt<'tcx>,
            end: HirId,
            other: bool,
        }
        impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
                    && path.res == Res::Local(self.end)
                {
                    let compared = match self.tcx.parent_hir_node(e.hir_id) {
                        rustc_hir::Node::Expr(Expr {
                            kind: ExprKind::Binary(op, ..),
                            ..
                        }) => matches!(
                            op.node,
                            rustc_hir::BinOpKind::Lt
                                | rustc_hir::BinOpKind::Le
                                | rustc_hir::BinOpKind::Gt
                                | rustc_hir::BinOpKind::Ge
                                | rustc_hir::BinOpKind::Eq
                                | rustc_hir::BinOpKind::Ne
                        ),
                        rustc_hir::Node::Expr(Expr {
                            kind: ExprKind::MethodCall(segment, ..),
                            ..
                        }) => segment.ident.name.as_str() == "offset_from",
                        _ => false,
                    };
                    if !compared {
                        self.other = true;
                    }
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut uses = Uses {
            tcx,
            end,
            other: false,
        };
        uses.visit_body(body);
        !uses.other
    }
    /// `x & (n - c)`, through casts: below `n` only if `n >= 1`, which the
    /// extent prover receipts as its mask-of-length premise (the review's F5).
    fn masked_below(
        e: &Expr<'_>,
        companion: HirId,
        typeck: &rustc_middle::ty::TypeckResults<'_>,
    ) -> bool {
        let mut e = e;
        loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Binary(op, left, right)
                    if matches!(op.node, rustc_hir::BinOpKind::BitAnd) =>
                {
                    return below_companion(left, companion, typeck)
                        || below_companion(right, companion, typeck);
                }
                _ => return false,
            }
        }
    }
    /// `e` reads nothing but the companion, the local `this`, and literals,
    /// through arithmetic (`wrapping_*` included).
    fn companion_pure(e: &Expr<'_>, companion: HirId, this: HirId) -> bool {
        match e.kind {
            ExprKind::Lit(_) => true,
            ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) | ExprKind::Unary(_, inner) => {
                companion_pure(inner, companion, this)
            }
            ExprKind::Binary(_, left, right) => {
                companion_pure(left, companion, this) && companion_pure(right, companion, this)
            }
            ExprKind::MethodCall(segment, receiver, args, _)
                if segment.ident.name.as_str().starts_with("wrapping_") =>
            {
                companion_pure(receiver, companion, this)
                    && args.iter().all(|a| companion_pure(a, companion, this))
            }
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                matches!(path.res, Res::Local(id) if id == companion || id == this)
            }
            _ => false,
        }
    }
    struct Indexes<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        binding: HirId,
        others: &'a [HirId],
        params: &'a [HirId],
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        defs: &'a Defs<'tcx>,
        /// The review's F2: the companion is written in the body, so an index
        /// naming it is not bounded by the caller's argument.
        companion_written: bool,
        companion: HirId,
        bound: bool,
        masked: bool,
        /// Relay 065: a mask-named companion's reads, in place.
        mask_formal: bool,
        local_masked: bool,
        unproven: bool,
    }
    fn names(e: &Expr<'_>, others: &[HirId]) -> bool {
        struct Names<'a> {
            others: &'a [HirId],
            found: bool,
        }
        impl<'tcx> Visitor<'tcx> for Names<'_> {
            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
                    && let Res::Local(id) = path.res
                    && self.others.contains(&id)
                {
                    self.found = true;
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut visitor = Names {
            others,
            found: false,
        };
        visitor.visit_expr(e);
        visitor.found
    }
    /// `(ix & mask)`, `(ix & mask) + 1`, `((ix & mask) as isize)` — the index
    /// is bounded by the companion when a `&` with the companion on one side
    /// dominates it. Additions of a CONSTANT are allowed through (brotli's
    /// `at + 1 .. at + 3` neighbours of a masked index); anything else is not.
    fn masked_by(e: &Expr<'_>, companion: HirId) -> bool {
        let mut e = e;
        loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Binary(op, left, right)
                    if matches!(op.node, rustc_hir::BinOpKind::BitAnd) =>
                {
                    return is_binding(left, companion)
                        || is_binding(right, companion)
                        || masked_by(left, companion)
                        || masked_by(right, companion);
                }
                ExprKind::Binary(op, left, right)
                    if matches!(op.node, rustc_hir::BinOpKind::Add) =>
                {
                    return (masked_by(left, companion) && constant(right))
                        || (masked_by(right, companion) && constant(left));
                }
                _ => return false,
            }
        }
    }
    /// **Relay 065 — a read of ONE element, in place.** The offset (or index)
    /// at `e` is dereferenced where it stands, `*data.offset(i)` or
    /// `data[i]`, and the place is not borrowed: `&*data.offset(i)` handed
    /// to a callee, or `*(data.offset(i) as *const u32)`, reads past the
    /// element, so a masked index there bounds nothing the length must cover.
    fn read_in_place<'tcx>(tcx: TyCtxt<'tcx>, e: &'tcx Expr<'tcx>) -> bool {
        let place = match e.kind {
            ExprKind::Index(..) => e,
            _ => match tcx.parent_hir_node(e.hir_id) {
                rustc_hir::Node::Expr(
                    deref @ Expr {
                        kind: ExprKind::Unary(rustc_hir::UnOp::Deref, _),
                        ..
                    },
                ) => deref,
                _ => return false,
            },
        };
        !matches!(
            tcx.parent_hir_node(place.hir_id),
            rustc_hir::Node::Expr(Expr {
                kind: ExprKind::AddrOf(..),
                ..
            })
        )
    }
    /// `(v & companion)` exactly, nothing added (relay 065, the third review's
    /// B-2).
    fn pure_inline_mask(e: &Expr<'_>, companion: HirId) -> bool {
        let mut e = e;
        loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Binary(op, left, right)
                    if matches!(op.node, rustc_hir::BinOpKind::BitAnd) =>
                {
                    return is_binding(left, companion) || is_binding(right, companion);
                }
                _ => return false,
            }
        }
    }
    /// **Relay 068 (R674).** An index that names the companion itself is
    /// bounded by it only in the masked form: `ix & companion` (the masked
    /// arm, `companion + 1`), or below it — `ix & (companion - 1)` (ht's
    /// `hash & (capacity - 1)`) or `companion - c` (the last element, which a
    /// UB-free input reads only when `companion >= c`, §28). `in_0[i]`,
    /// `in_0[i * 4 + k]`, `i + 1`,
    /// `i << 2` read at or past the companion: lodepng's
    /// `getPixelColorRGBA8(.., in_0, i, ..)`, whose `i` is the read position.
    /// `None` where the index does not name it; a mask-named companion keeps
    /// its in-place proof below.
    fn companion_index(
        e: &Expr<'_>,
        companion: HirId,
        typeck: &rustc_middle::ty::TypeckResults<'_>,
    ) -> Option<CompanionIndex> {
        if !names(e, &[companion]) {
            return None;
        }
        Some(if masked_by(e, companion) {
            CompanionIndex::Masked
        } else if below_companion(e, companion, typeck) {
            CompanionIndex::Below
        } else {
            CompanionIndex::Unbounded
        })
    }
    /// `companion - c`, through casts, for a literal `c >= 1`, and any further
    /// unsigned subtraction (`n - 1 - i`, the reverse walk: the review's F6):
    /// below the companion in a UB-free input. `ix & (companion - c)` is NOT
    /// here (the review's F5): at `companion = 0` it is all ones, and only the
    /// extent prover's receipted mask-of-length premise bounds it.
    fn below_companion(
        e: &Expr<'_>,
        companion: HirId,
        typeck: &rustc_middle::ty::TypeckResults<'_>,
    ) -> bool {
        fn chain(
            e: &Expr<'_>,
            companion: HirId,
            typeck: &rustc_middle::ty::TypeckResults<'_>,
        ) -> Option<bool> {
            let mut e = e;
            loop {
                match e.kind {
                    ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                    _ => break,
                }
            }
            if is_binding(e, companion) {
                return Some(false);
            }
            let (left, right) = match e.kind {
                ExprKind::Binary(op, left, right)
                    if matches!(op.node, rustc_hir::BinOpKind::Sub) =>
                {
                    (left, right)
                }
                ExprKind::MethodCall(segment, receiver, [argument], _)
                    if segment.ident.name.as_str() == "wrapping_sub" =>
                {
                    (receiver, argument)
                }
                _ => return None,
            };
            let literal = chain(left, companion, typeck)?;
            if positive_literal(right) {
                Some(true)
            } else if matches!(
                typeck.expr_ty(right).kind(),
                rustc_middle::ty::TyKind::Uint(_)
            ) {
                Some(literal)
            } else {
                None
            }
        }
        chain(e, companion, typeck) == Some(true)
    }
    fn positive_literal(e: &Expr<'_>) -> bool {
        let mut e = e;
        loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Lit(lit) => {
                    return matches!(lit.node, rustc_ast::LitKind::Int(n, _) if n.get() >= 1);
                }
                _ => return false,
            }
        }
    }
    fn constant(e: &Expr<'_>) -> bool {
        let mut e = e;
        loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Lit(_) => return true,
                _ => return false,
            }
        }
    }
    fn is_binding(e: &Expr<'_>, binding: HirId) -> bool {
        let mut e = e;
        loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                    return path.res == Res::Local(binding);
                }
                _ => return false,
            }
        }
    }
    /// **Relay 065 (R653-1, STOP 1) — a local index masked in place.**
    /// `prev_ix &= ring_buffer_mask; data[prev_ix]`: the index is exactly a
    /// local (no constant added: `mask + 1` covers `<= mask` and nothing
    /// more) whose LAST write before the read masks it by the companion (`v &= companion`, `v = e &
    /// companion`, `let v = e & companion`). Nothing writes it between that
    /// write and the read, nor anywhere in the statement that holds the read,
    /// since a loop's later write reaches its next read. Its address is never
    /// taken mutably (nor captured by a closure, nor bound `ref mut`), and the
    /// companion is never written in the body: the value the read sees is
    /// bounded by the caller's argument. Straight-line and syntactic:
    /// anything else is not a proof, and a mask offered as a count is refused
    /// (relay 063 item 6). The verdict is the FUNCTION's: one read of the
    /// parameter that is neither masked nor names another parameter fails it
    /// (the review's finding 3; `at` beside `at + 3`).
    fn masked_local<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        index: &'tcx Expr<'tcx>,
        companion: HirId,
    ) -> bool {
        let mut e = index;
        let local = loop {
            match e.kind {
                ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
                    Res::Local(local) if local != companion => break local,
                    _ => return false,
                },
                _ => return false,
            }
        };
        /// The writes to `local` in one subtree, and whether one borrows it
        /// mutably (`&mut`, a closure's capture, a `ref mut` binding).
        struct Writes<'tcx> {
            tcx: TyCtxt<'tcx>,
            local: HirId,
            count: usize,
            borrowed: bool,
        }
        fn ref_mut(pat: &rustc_hir::Pat<'_>) -> bool {
            let mut found = false;
            pat.walk_always(|p| {
                if let rustc_hir::PatKind::Binding(
                    rustc_hir::BindingMode(rustc_hir::ByRef::Yes(rustc_hir::Mutability::Mut), _),
                    ..,
                ) = p.kind
                {
                    found = true;
                }
            });
            found
        }
        impl<'tcx> Visitor<'tcx> for Writes<'tcx> {
            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                match e.kind {
                    ExprKind::Assign(lhs, ..) | ExprKind::AssignOp(_, lhs, _)
                        if is_binding(lhs, self.local) =>
                    {
                        self.count += 1
                    }
                    ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place)
                        if is_binding(place, self.local) =>
                    {
                        self.borrowed = true
                    }
                    ExprKind::Closure(closure)
                        if self
                            .tcx
                            .upvars_mentioned(closure.def_id)
                            .is_some_and(|upvars| upvars.contains_key(&self.local)) =>
                    {
                        self.borrowed = true
                    }
                    ExprKind::Match(scrutinee, arms, _)
                        if is_binding(scrutinee, self.local)
                            && arms.iter().any(|arm| ref_mut(arm.pat)) =>
                    {
                        self.borrowed = true
                    }
                    ExprKind::Let(let_)
                        if is_binding(let_.init, self.local) && ref_mut(let_.pat) =>
                    {
                        self.borrowed = true
                    }
                    _ => {}
                }
                intravisit::walk_expr(self, e);
            }

            fn visit_local(&mut self, let_: &'tcx rustc_hir::LetStmt<'tcx>) {
                if let_.init.is_some_and(|init| is_binding(init, self.local)) && ref_mut(let_.pat) {
                    self.borrowed = true;
                }
                intravisit::walk_local(self, let_);
            }

            fn visit_pat(&mut self, p: &'tcx rustc_hir::Pat<'tcx>) {
                if let rustc_hir::PatKind::Binding(_, id, ..) = p.kind
                    && id == self.local
                {
                    self.count += 1;
                }
                intravisit::walk_pat(self, p);
            }
        }
        let writes = |visit: &dyn Fn(&mut Writes<'tcx>)| {
            let mut writes = Writes {
                tcx,
                local,
                count: 0,
                borrowed: false,
            };
            visit(&mut writes);
            writes
        };
        if writes(&|w| w.visit_body(body)).borrowed {
            return false;
        }
        // The companion is the caller's argument only while nothing in the
        // body writes it (the review's finding 5).
        let mut companion_writes = Writes {
            tcx,
            local: companion,
            count: 0,
            borrowed: false,
        };
        companion_writes.visit_expr(body.value);
        if companion_writes.count != 0 || companion_writes.borrowed {
            return false;
        }
        let stmt_writes = |stmt: &'tcx rustc_hir::Stmt<'tcx>| writes(&|w| w.visit_stmt(stmt)).count;
        // `x & companion`, nothing added.
        let pure_mask = |e: &Expr<'_>| {
            let mut e = e;
            loop {
                match e.kind {
                    ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
                    ExprKind::Binary(op, left, right)
                        if matches!(op.node, rustc_hir::BinOpKind::BitAnd) =>
                    {
                        return is_binding(left, companion) || is_binding(right, companion);
                    }
                    _ => return false,
                }
            }
        };
        let masks = |stmt: &'tcx rustc_hir::Stmt<'tcx>| match stmt.kind {
            rustc_hir::StmtKind::Semi(e) | rustc_hir::StmtKind::Expr(e) => match e.kind {
                ExprKind::AssignOp(op, lhs, rhs) => {
                    matches!(op.node, rustc_hir::AssignOpKind::BitAndAssign)
                        && is_binding(lhs, local)
                        && is_binding(rhs, companion)
                }
                ExprKind::Assign(lhs, rhs, _) => is_binding(lhs, local) && pure_mask(rhs),
                _ => false,
            },
            rustc_hir::StmtKind::Let(let_) => {
                matches!(let_.pat.kind, rustc_hir::PatKind::Binding(_, id, ..) if id == local)
                    && let_.init.is_some_and(|init| pure_mask(init))
            }
            _ => false,
        };
        let mut child = index.hir_id;
        for (id, node) in tcx.hir_parent_iter(index.hir_id) {
            match node {
                rustc_hir::Node::Block(block) => {
                    let (before, holding) =
                        if let Some(k) = block.stmts.iter().position(|stmt| stmt.hir_id == child) {
                            (&block.stmts[..k], stmt_writes(&block.stmts[k]))
                        } else if block.expr.is_some_and(|tail| tail.hir_id == child) {
                            let tail = block.expr.expect("the tail");
                            (block.stmts, writes(&|w| w.visit_expr(tail)).count)
                        } else {
                            return false;
                        };
                    if holding != 0 {
                        return false;
                    }
                    if let Some(last) = before.iter().rev().find(|stmt| stmt_writes(stmt) != 0) {
                        return stmt_writes(last) == 1 && masks(last);
                    }
                }
                rustc_hir::Node::Expr(Expr {
                    kind: ExprKind::Closure(..),
                    ..
                })
                | rustc_hir::Node::Item(_)
                | rustc_hir::Node::ImplItem(_)
                | rustc_hir::Node::TraitItem(_) => return false,
                _ => {}
            }
            child = id;
        }
        false
    }
    impl<'tcx> Indexes<'_, 'tcx> {
        fn taint(&self, e: &'tcx Expr<'tcx>, depth: u32, seen: &mut Vec<HirId>) -> Taint {
            if masked_by(e, self.companion) {
                return if self.companion_written {
                    Taint::Bad
                } else {
                    Taint::Masked
                };
            }
            if names(e, self.others) {
                return Taint::Bad;
            }
            match companion_index(e, self.companion, self.typeck) {
                Some(CompanionIndex::Below) if !self.companion_written => return Taint::Below,
                Some(_) => return Taint::Bad,
                None => {}
            }
            let mut out = Taint::Clean;
            for local in locals_in(e, self.params) {
                if seen.contains(&local) {
                    continue;
                }
                seen.push(local);
                let taint = self.local_taint(local, depth + 1, seen);
                seen.pop();
                out = match taint {
                    Taint::Clean => out,
                    // A tainted local stands for its bound only as the
                    // whole index; `at + 1` over `at <= n` reads past it.
                    taint if exactly(e, local) => join(out, taint),
                    _ => Taint::Bad,
                };
            }
            out
        }

        /// A local stands for the companion only where every definition is
        /// an expression over the companion, literals and the local itself
        /// (`let j = i * 4`: the companion in disguise, the review's F3). A
        /// definition that also reads anything else (another local, a
        /// parameter, a call, memory) is a loop local in the relay's sense and
        /// stays admitted: its bound is the extent prover's (step 3). Whatever
        /// it reads, `x & (n - c)` is below `n` only under the prover's
        /// mask-of-length premise (F5), and `x & n` is masked.
        fn local_taint(&self, local: HirId, depth: u32, seen: &mut Vec<HirId>) -> Taint {
            if depth > 6 || self.defs.borrowed.contains(&local) {
                return Taint::Clean;
            }
            let mut out = Taint::Clean;
            for &(definition, compound) in self.defs.values.get(&local).into_iter().flatten() {
                let taint = if masked_by(definition, self.companion) {
                    if self.companion_written {
                        Taint::Bad
                    } else {
                        Taint::Masked
                    }
                } else if masked_below(definition, self.companion, self.typeck) {
                    Taint::Bad
                } else if let Some(copy) = locals_in(definition, self.params)
                    .into_iter()
                    .find(|l| exactly(definition, *l) && *l != local)
                {
                    if seen.contains(&copy) {
                        Taint::Clean
                    } else {
                        seen.push(copy);
                        let taint = self.local_taint(copy, depth + 1, seen);
                        seen.pop();
                        taint
                    }
                } else if companion_pure(definition, self.companion, local) {
                    match companion_index(definition, self.companion, self.typeck) {
                        None => Taint::Clean,
                        Some(CompanionIndex::Below) if !self.companion_written => Taint::Below,
                        Some(CompanionIndex::Masked) if !self.companion_written => Taint::Masked,
                        Some(_) => Taint::Bad,
                    }
                } else {
                    Taint::Clean
                };
                out = join(
                    out,
                    if compound && taint != Taint::Clean {
                        Taint::Bad
                    } else {
                        taint
                    },
                );
            }
            out
        }

        /// An index that names no other parameter, under a companion that is
        /// not mask-named (relay 068 and its review).
        fn classify(&mut self, e: &'tcx Expr<'tcx>, index: &'tcx Expr<'tcx>, offset: bool) {
            if offset
                && is_binding(index, self.companion)
                && !self.companion_written
                && end_pointer_let(self.tcx, self.body, self.defs, e)
            {
                return;
            }
            match self.taint(index, 0, &mut Vec::new()) {
                Taint::Clean | Taint::Below => {}
                Taint::Masked => self.masked = true,
                Taint::Bad => self.bound = false,
            }
        }
    }
    impl<'tcx> Visitor<'tcx> for Indexes<'_, 'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            match e.kind {
                ExprKind::MethodCall(segment, receiver, [index], _)
                    if super::emitability::SLICE_ARITHMETIC_OPS
                        .contains(&segment.ident.name.as_str())
                        && is_binding(receiver, self.binding) =>
                {
                    if names(index, self.others) {
                        if masked_by(index, self.companion) && !self.companion_written {
                            self.masked = true;
                        } else {
                            self.bound = false;
                        }
                    } else if !self.mask_formal {
                        // Relay 068 and its review: the companion itself only
                        // masked or below, a local through its definitions,
                        // and the end pointer `let end = p.offset(n)`.
                        let offset = segment.ident.name.as_str() == "offset";
                        self.classify(e, index, offset);
                    } else {
                        if !read_in_place(self.tcx, e) {
                            // A masked address handed on, or read wide through
                            // a cast, reads past `mask` (relay 065, the final
                            // probe on `FindLongestMatchHROLLING_FAST`).
                            self.unproven = true;
                        } else if masked_local(self.tcx, self.body, index, self.companion) {
                            self.local_masked = true;
                        } else if !pure_inline_mask(index, self.companion) {
                            // (the third review's B-2) `data[(v & mask)]` is
                            // proven in place too; it neither makes nor unmakes
                            // the in-place verdict.
                            self.unproven = true;
                        }
                    }
                }
                ExprKind::Index(base, index, _) if is_binding(base, self.binding) => {
                    if names(index, self.others) {
                        if masked_by(index, self.companion) && !self.companion_written {
                            self.masked = true;
                        } else {
                            self.bound = false;
                        }
                    } else if !self.mask_formal {
                        self.classify(e, index, false);
                    } else {
                        if !read_in_place(self.tcx, e) {
                            // A masked address handed on, or read wide through
                            // a cast, reads past `mask` (relay 065, the final
                            // probe on `FindLongestMatchHROLLING_FAST`).
                            self.unproven = true;
                        } else if masked_local(self.tcx, self.body, index, self.companion) {
                            self.local_masked = true;
                        } else if !pure_inline_mask(index, self.companion) {
                            // (the third review's B-2) `data[(v & mask)]` is
                            // proven in place too; it neither makes nor unmakes
                            // the in-place verdict.
                            self.unproven = true;
                        }
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, e);
        }
    }
    let params: Vec<HirId> = body.params.iter().map(|p| p.pat.hir_id).collect();
    let defs = Defs::of(tcx, function);
    let mut visitor = Indexes {
        tcx,
        body,
        binding,
        others: &others,
        params: &params,
        typeck: tcx.typeck(function),
        companion_written: defs.written(companion),
        defs: &defs,
        companion,
        bound: true,
        masked: false,
        mask_formal,
        local_masked: false,
        unproven: false,
    };
    visitor.visit_body(body);
    match (
        visitor.bound,
        visitor.masked || (visitor.local_masked && !visitor.unproven),
    ) {
        (false, _) => IndexBound::No,
        (true, true) => IndexBound::MaskedByCompanion,
        (true, false) if mask_formal && visitor.unproven => IndexBound::MaskUnproven,
        (true, false) => IndexBound::ByCompanion,
    }
}

impl Hold {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::OutsideScope => "outside-scope",
            Self::CalleeNotFat => "callee-not-fat",
            Self::CallerNotSupplied => "caller-not-supplied",
            Self::CallerNullable => "caller-nullable",
            Self::IncompleteCallers => "incomplete-callers",
            Self::CompanionNotIndexBound => "companion-not-the-index-bound",
        }
    }
}
