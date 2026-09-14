//! Caller array/count evidence for typed thin forwarding parameters.
use rustc_hir::{
    Expr, ExprKind, HirId, Node, PatKind, StmtKind,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{IntTy, TyCtxt, TyKind, UintTy};

use super::{
    Subject, SubjectKind,
    emitability::{EmitabilityFacts, RefKind},
    thin_counted_entropy,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Hold {
    OutsideScope,
    CalleeAccess(thin_counted_entropy::Hold),
    CallerSource,
    CallerCount,
    IncompleteCallers,
}
#[derive(Debug, Clone)]
pub(crate) struct Proof {
    pub count_parameter: usize,
    pub callers: usize,
    pub reader: Option<thin_counted_entropy::ReaderProof>,
}
fn peel<'a>(mut e: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::DropTemps(x) = e.kind {
        e = x;
    }
    e
}
fn max(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> Option<u128> {
    let (bits, signed) = match ty.kind() {
        TyKind::Uint(k) => (
            match k {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => tcx.data_layout.pointer_size.bits(),
            },
            false,
        ),
        TyKind::Int(k) => (
            match k {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => tcx.data_layout.pointer_size.bits(),
            },
            true,
        ),
        _ => return None,
    };
    Some(if bits == 128 && !signed {
        u128::MAX
    } else {
        (1u128 << (bits - u64::from(signed))) - 1
    })
}
fn constant(tcx: TyCtxt<'_>, owner: LocalDefId, e: &Expr<'_>, fuel: usize) -> Option<u128> {
    if fuel == 0 {
        return None;
    }
    let e = peel(e);
    let types = tcx.typeck(owner);
    let value = match e.kind {
        ExprKind::Lit(l) => match l.node {
            rustc_ast::LitKind::Int(n, _) => n.get(),
            _ => return None,
        },
        ExprKind::Cast(inner, _) => constant(tcx, owner, inner, fuel - 1)?,
        ExprKind::Binary(op, l, r) => {
            let l = constant(tcx, owner, l, fuel - 1)?;
            let r = constant(tcx, owner, r, fuel - 1)?;
            match op.node {
                rustc_hir::BinOpKind::Add => l.checked_add(r)?,
                rustc_hir::BinOpKind::Sub => l.checked_sub(r)?,
                rustc_hir::BinOpKind::Mul => l.checked_mul(r)?,
                _ => return None,
            }
        }
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
            let Res::Local(id) = path.res else { return None };
            let Node::Pat(pat) = tcx.hir_node(id) else { return None };
            if !matches!(
                pat.kind,
                PatKind::Binding(
                    rustc_hir::BindingMode(_, rustc_hir::Mutability::Not),
                    _,
                    _,
                    None
                )
            ) {
                return None;
            }
            let Node::LetStmt(stmt) = tcx.parent_hir_node(id) else { return None };
            constant(tcx, owner, stmt.init?, fuel - 1)?
        }
        ExprKind::Call(f, args) if args.is_empty() => {
            let TyKind::FnDef(d, _) = types.expr_ty(f).kind() else { return None };
            let callee = d.as_local()?;
            if callee == owner || !tcx.hir_body_owners().any(|x| x == callee) {
                return None;
            }
            let ExprKind::Block(b, _) = peel(tcx.hir_body_owned_by(callee).value).kind else {
                return None;
            };
            let value = match (b.stmts, b.expr) {
                ([], Some(e)) => e,
                ([s], None) => match s.kind {
                    StmtKind::Semi(e) | StmtKind::Expr(e) => e,
                    _ => return None,
                },
                _ => return None,
            };
            let value = match value.kind {
                ExprKind::Ret(Some(e)) => e,
                _ => value,
            };
            constant(tcx, callee, value, fuel - 1)?
        }
        _ => return None,
    };
    (value <= max(tcx, types.expr_ty(e))?).then_some(value)
}
struct Find<'tcx> {
    span: rustc_span::Span,
    found: Vec<&'tcx Expr<'tcx>>,
}
impl<'tcx> Visitor<'tcx> for Find<'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if e.span == self.span && !matches!(e.kind, ExprKind::DropTemps(..)) {
            self.found.push(e);
        }
        intravisit::walk_expr(self, e);
    }
}
fn expression<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    span: rustc_span::Span,
) -> Option<&'tcx Expr<'tcx>> {
    if span.from_expansion() {
        return None;
    }
    let mut find = Find {
        span,
        found: vec![],
    };
    find.visit_body(tcx.hir_body_owned_by(owner));
    match find.found.as_slice() {
        [e] => Some(*e),
        _ => None,
    }
}
fn array_capacity(tcx: TyCtxt<'_>, owner: LocalDefId, e: &Expr<'_>) -> Option<u128> {
    let e = peel(e);
    let ExprKind::MethodCall(_, receiver, [], _) = e.kind else { return None };
    let did = tcx.typeck(owner).type_dependent_def_id(e.hir_id)?;
    if tcx.crate_name(did.krate).as_str() != "core"
        || !matches!(tcx.item_name(did).as_str(), "as_ptr" | "as_mut_ptr")
    {
        return None;
    }
    let mut ty = tcx.typeck(owner).expr_ty(receiver);
    while let TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    let TyKind::Array(element, n) = ty.kind() else { return None };
    if !matches!(element.kind(), TyKind::Uint(UintTy::U32)) {
        return None;
    }
    Some(n.try_to_target_usize(tcx)? as u128)
}
fn closed_calls<'a>(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    facts: &'a EmitabilityFacts,
) -> Result<&'a [super::emitability::CallSite], Hold> {
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
    let attrs = tcx.codegen_fn_attrs(owner);
    if tcx.visibility(owner).is_public()
        || attrs.export_name.is_some()
        || attrs.flags.contains(CodegenFnAttrFlags::NO_MANGLE)
    {
        return Err(Hold::IncompleteCallers);
    }
    let refs = facts
        .referenced
        .get(&owner)
        .ok_or(Hold::IncompleteCallers)?;
    if !RefKind::is_adaptable(refs) {
        return Err(Hold::IncompleteCallers);
    }
    let calls = facts
        .call_args
        .get(&owner)
        .filter(|s| !s.is_empty())
        .ok_or(Hold::IncompleteCallers)?;
    if calls.len() != refs.len() {
        return Err(Hold::IncompleteCallers);
    }
    Ok(calls)
}

// Source capacity is checked independently of the reader's access proof.
fn forwarder_source(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    parameter: usize,
    facts: &EmitabilityFacts,
) -> Result<(thin_counted_entropy::ForwarderProof, usize), Hold> {
    let sig = tcx.fn_sig(owner).skip_binder().skip_binder();
    if sig.inputs().len() != 2 {
        return Err(Hold::OutsideScope);
    }
    let forwarder =
        thin_counted_entropy::forwarder(tcx, owner, parameter).map_err(Hold::CalleeAccess)?;
    if forwarder.count_parameter != parameter + 1 {
        return Err(Hold::CallerCount);
    }
    let calls = closed_calls(tcx, owner, facts)?;
    for call in calls {
        let source = call
            .args
            .iter()
            .find(|a| a.index == parameter)
            .and_then(|a| expression(tcx, call.caller, a.span))
            .ok_or(Hold::CallerSource)?;
        let capacity = array_capacity(tcx, call.caller, source).ok_or(Hold::CallerSource)?;
        let value = call
            .args
            .iter()
            .find(|a| a.index == forwarder.count_parameter)
            .and_then(|a| expression(tcx, call.caller, a.span))
            .and_then(|e| constant(tcx, call.caller, e, 24))
            .ok_or(Hold::CallerCount)?;
        if value > capacity
            || value > ((1u128 << (tcx.data_layout.pointer_size.bits() - 1)) - 1) / 4
        {
            return Err(Hold::CallerCount);
        }
    }
    Ok((forwarder, calls.len()))
}

// A reader's safe signature affects every incoming call. Admit only complete
// array -> forwarding parameter -> reader chains, including sibling wrappers.
fn reader_sources(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    parameter: usize,
    facts: &EmitabilityFacts,
) -> Result<usize, Hold> {
    let calls = closed_calls(tcx, owner, facts)?;
    for call in calls {
        let arg = call
            .args
            .iter()
            .find(|a| a.index == parameter)
            .ok_or(Hold::CallerSource)?;
        let super::emitability::ArgShape::BareLocal(binding) = arg.shape else {
            return Err(Hold::CallerSource);
        };
        let body = tcx.hir_body_owned_by(call.caller);
        let index = body
            .params
            .iter()
            .position(|p| p.pat.hir_id == binding)
            .ok_or(Hold::CallerSource)?;
        let (forwarder, _) = forwarder_source(tcx, call.caller, index, facts).map_err(|hold| {
            if hold == Hold::OutsideScope {
                Hold::CallerSource
            } else {
                hold
            }
        })?;
        if forwarder.callee != owner || forwarder.callee_parameter != parameter {
            return Err(Hold::CallerSource);
        }
    }
    Ok(calls.len())
}

pub(crate) fn prove(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
) -> Result<Proof, Hold> {
    let SubjectKind::Param { hir_index } = subject.kind else { return Err(Hold::OutsideScope) };
    if subject.ptr_depth != 1 || subject.mutable {
        return Err(Hold::OutsideScope);
    }
    let sig = tcx.fn_sig(subject.fn_did).skip_binder().skip_binder();
    if !sig.inputs().get(hir_index).is_some_and(|ty|matches!(ty.kind(),TyKind::RawPtr(p,rustc_hir::Mutability::Not) if matches!(p.kind(),TyKind::Uint(UintTy::U32)))){return Err(Hold::OutsideScope);}
    if let Ok(reader) = thin_counted_entropy::reader(tcx, subject.fn_did, hir_index) {
        if reader.count_parameter != hir_index + 1 {
            return Err(Hold::CallerCount);
        }
        let callers = reader_sources(tcx, subject.fn_did, hir_index, facts)?;
        return Ok(Proof {
            count_parameter: reader.count_parameter,
            callers,
            reader: Some(reader),
        });
    }
    let (forwarder, callers) = forwarder_source(tcx, subject.fn_did, hir_index, facts)?;
    reader_sources(tcx, forwarder.callee, forwarder.callee_parameter, facts)?;
    Ok(Proof {
        count_parameter: forwarder.count_parameter,
        callers,
        reader: None,
    })
}

pub(crate) fn enabled_proof(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
    policy: &crate::bo_rewriter::additive::FamilyPolicy,
) -> Option<Proof> {
    policy
        .enabled(
            subject.fn_did,
            crate::bo_rewriter::additive::FamilyStage::SliceUse,
        )
        .then(|| prove(tcx, subject, facts).ok())
        .flatten()
}
pub(crate) fn covers_comparison(proof: Option<&Proof>, span: rustc_span::Span) -> bool {
    proof
        .and_then(|p| p.reader.as_ref())
        .is_some_and(|p| p.comparison == span)
}
pub(crate) fn slice_uses(
    proof: Option<&Proof>,
    original: super::emitability::SliceUses,
) -> super::emitability::SliceUses {
    match proof.and_then(|p| p.reader.as_ref()) {
        Some(reader) => super::emitability::SliceUses {
            rewrites: reader.rewrites.clone(),
            ..Default::default()
        },
        None => original,
    }
}

impl Hold {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::OutsideScope => "outside-scope",
            Self::CalleeAccess(_) => "callee-access",
            Self::CallerSource => "caller-source",
            Self::CallerCount => "caller-count",
            Self::IncompleteCallers => "incomplete-callers",
        }
    }
}
pub(crate) fn missing_evidence(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
) -> Option<Hold> {
    prove(tcx, subject, facts)
        .err()
        .filter(|h| *h != Hold::OutsideScope)
}
pub(crate) fn hold_detail(
    access: &super::local_callee_extent::LocalCalleeAccess,
    count: Option<Hold>,
) -> String {
    match count {
        Some(hold) => format!(
            "held:local-callee-access-extent:{};{:?};{}",
            hold.key(),
            hold,
            access.detail()
        ),
        None => access.detail(),
    }
}
