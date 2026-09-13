//! Shared-call permissions: native call inventory, reader proof, and source plan.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, Mutability, UnOp,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    mir::{Location, Operand, TerminatorKind, visit::Visitor as MirVisitor},
    ty::{TyCtxt, TyKind},
};
use rustc_span::Span;
use sha2::{Digest, Sha256};

use super::{
    super::{
        DecisionTable, SubjectKind,
        a5_site_proof::{
            A5ProofSiteKey, A5SeamProofIndex, A5SiteProofVerdict, ATTESTED_GUARD, ATTESTED_WORLD,
        },
        emitability::{ArgShape, CallSite, EmitabilityFacts, RefKind},
        exposure::{ExposurePolicy, ExposureSurfacePlan},
        lifetime::LifetimeEligibility,
        seam::{Form, form_of},
    },
    reader,
};
use crate::analyses::borrow_ownership::mutability_facts::MutFacts;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Permission {
    pub request: reader::Request,
    pub certificate: reader::Certificate,
    pub required_sites: Vec<A5ProofSiteKey>,
    pub seal: String,
    pub call_span: Span,
    pub caller: String,
    pub callee: String,
    pub sources: Vec<Source>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Source {
    pub index: usize,
    pub argument_span: Span,
    pub operand_span: Span,
    pub original: String,
    pub operand: String,
    pub mutable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SharedAddress {
    pub argument_span: Span,
    pub operand_span: Span,
    pub original: String,
    pub operand: String,
    pub permission: Permission,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    MissingWorld,
    Exposed,
    PointerComponent,
    ExpectedForm,
    MissingMutability,
    MutableFormal,
    MissingInventory,
    SiteMismatch,
    SourceShape,
    SourceText,
    Reader(reader::Hold),
    NoNewSite,
    SourceRoots,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Call {
    pub permission: Permission,
    pub addresses: FxHashMap<usize, SharedAddress>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Discovery {
    pub calls: FxHashMap<(LocalDefId, LocalDefId, u32, u32), Call>,
    pub holds: FxHashMap<LocalDefId, Hold>,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn discover(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
    table: &DecisionTable,
    exposure: Option<&ExposurePolicy>,
    a5: &A5SeamProofIndex,
    lifetimes: &LifetimeEligibility,
    mutability: &MutFacts,
) -> Discovery {
    let mut out = Discovery::default();
    for (&callee, sites) in &facts.call_args {
        if !sites.iter().any(|site| {
            site.args
                .iter()
                .any(|arg| matches!(arg.shape, ArgShape::AddrOf { mutable: true, .. }))
        }) {
            continue;
        }
        match candidate(
            tcx, callee, sites, facts, table, exposure, a5, lifetimes, mutability,
        ) {
            Ok(calls) => out.calls.extend(calls),
            Err(why) => {
                out.holds.insert(callee, why);
            }
        }
    }
    out
}

type CallKey = (LocalDefId, LocalDefId, u32, u32);

pub(crate) fn call_key(callee: LocalDefId, site: &CallSite) -> CallKey {
    let span = site.span.source_callsite();
    (site.caller, callee, span.lo().0, span.hi().0)
}

#[allow(clippy::too_many_arguments)]
fn candidate(
    tcx: TyCtxt<'_>,
    callee: LocalDefId,
    sites: &[CallSite],
    facts: &EmitabilityFacts,
    table: &DecisionTable,
    exposure: Option<&ExposurePolicy>,
    a5: &A5SeamProofIndex,
    lifetimes: &LifetimeEligibility,
    mutability: &MutFacts,
) -> Result<FxHashMap<CallKey, Call>, Hold> {
    if a5.world() != ATTESTED_WORLD || a5.guard() != ATTESTED_GUARD {
        return Err(Hold::MissingWorld);
    }
    if exposure.is_none_or(|policy| policy.plan(callee) != ExposureSurfacePlan::ClosedWorldDirect)
        || facts
            .referenced
            .get(&callee)
            .is_some_and(|refs| refs.iter().any(|(kind, _)| *kind != RefKind::Call))
    {
        return Err(Hold::Exposed);
    }
    let stored = tcx.mir_drops_elaborated_and_const_checked(callee);
    if stored.is_stolen() {
        return Err(Hold::MissingInventory);
    }
    let body = stored.borrow();
    // This first consumer covers two pointer arguments. It cannot hide a
    // third writer or an effectful scalar argument between shared creations.
    if body.arg_count != 2 {
        return Err(Hold::PointerComponent);
    }
    for (index, local) in body.args_iter().enumerate() {
        if !matches!(body.local_decls[local].ty.kind(), TyKind::RawPtr(..)) {
            return Err(Hold::PointerComponent);
        }
        if mutability.is_defaulted(callee, local) {
            return Err(Hold::MissingMutability);
        }
        if mutability.is_mutable(callee, local) {
            return Err(Hold::MutableFormal);
        }
        if !table.entries.iter().any(|(subject, decision)| {
            subject.fn_did == callee
                && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == index)
                && form_of(decision) == (Form::Ref { mutable: false })
        }) {
            return Err(Hold::ExpectedForm);
        }
    }
    let web = lifetimes.fnptr_web().ok_or(Hold::MissingInventory)?;
    if web.contains(callee) {
        return Err(Hold::Exposed);
    }
    let native = native_calls(tcx, callee)?;
    let web_sites = web
        .mir_call_sites()
        .iter()
        .filter(|site| site.callee == callee)
        .map(|site| (site.caller, site.block))
        .collect::<FxHashSet<_>>();
    let native_sites = native
        .iter()
        .map(|(caller, block)| (*caller, *block))
        .collect::<FxHashSet<_>>();
    if native_sites != web_sites || native.len() != sites.len() || native.is_empty() {
        return Err(Hold::MissingInventory);
    }
    let mut consumed = FxHashSet::default();
    let mut pending = Vec::new();
    let mut required = Vec::new();
    let mut has_new_site = false;
    let sm = tcx.sess.source_map();
    for site in sites {
        let [left, right] = site.args.as_slice() else {
            return Err(Hold::SiteMismatch);
        };
        if left.index != 0 || right.index != 1 {
            return Err(Hold::SiteMismatch);
        }
        if left.shape.place_root().is_none() || left.shape.place_root() != right.shape.place_root()
        {
            return Err(Hold::SourceRoots);
        }
        let peer = a5.lookup(
            site.caller.local_def_index.as_u32(),
            callee.local_def_index.as_u32(),
            0,
            1,
            left.span,
            right.span,
        );
        if peer.verdict == A5SiteProofVerdict::Undeterminable {
            return Err(Hold::SiteMismatch);
        }
        let request = reader::Request {
            left: peer.left_site.ok_or(Hold::SiteMismatch)?,
            right: peer.right_site.ok_or(Hold::SiteMismatch)?,
            world: a5.world(),
            guard: a5.guard(),
        };
        let location = (request.left.caller, request.left.location.block);
        if !native_sites.contains(&location) || !consumed.insert(location) {
            return Err(Hold::SiteMismatch);
        }
        let certificate = reader::prove(tcx, &request).map_err(Hold::Reader)?;
        reader::replay(tcx, &request, Some(&certificate)).map_err(Hold::Reader)?;
        let mut drafts = Vec::new();
        for arg in &site.args {
            match arg.shape {
                ArgShape::AddrOf { mutable, .. } => {
                    let (operand_span, operand) = address(tcx, site.caller, arg.span, mutable)?;
                    drafts.push(Source {
                        index: arg.index,
                        argument_span: arg.span,
                        operand_span,
                        original: sm.span_to_snippet(arg.span).map_err(|_| Hold::SourceText)?,
                        operand,
                        mutable,
                    });
                }
                // Original reference constructions supply validity even if a
                // caller is reverted. A bare raw-input twin needs its own
                // source license; a form label is not that license.
                ArgShape::BareLocal(_) => return Err(Hold::SourceShape),
                _ => return Err(Hold::SourceShape),
            }
        }
        has_new_site |= drafts.iter().any(|source| source.mutable)
            && peer.verdict == A5SiteProofVerdict::Overlapping;
        required.extend([request.left, request.right]);
        pending.push((
            call_key(callee, site),
            site.span,
            request,
            certificate,
            drafts,
        ));
    }
    if consumed != native_sites {
        return Err(Hold::MissingInventory);
    }
    if !has_new_site {
        return Err(Hold::NoNewSite);
    }
    required.sort_by_key(|key| key.receipt_key());
    let mut calls = FxHashMap::default();
    for (key, call_span, request, certificate, sources) in pending {
        let mut permission = Permission {
            request,
            certificate,
            required_sites: required.clone(),
            seal: String::new(),
            call_span,
            caller: tcx.def_path_str(key.0.to_def_id()),
            callee: tcx.def_path_str(callee.to_def_id()),
            sources,
        };
        permission.seal = permission.digest();
        let addresses = permission
            .sources
            .iter()
            .filter(|source| source.mutable)
            .map(|source| {
                (
                    source.index,
                    SharedAddress {
                        argument_span: source.argument_span,
                        operand_span: source.operand_span,
                        original: source.original.clone(),
                        operand: source.operand.clone(),
                        permission: permission.clone(),
                    },
                )
            })
            .collect();
        calls.insert(
            key,
            Call {
                permission,
                addresses,
            },
        );
    }
    Ok(calls)
}

fn native_calls(tcx: TyCtxt<'_>, callee: LocalDefId) -> Result<Vec<(LocalDefId, u32)>, Hold> {
    struct Mention<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'a rustc_middle::mir::Body<'tcx>,
        callee: LocalDefId,
        escaped: bool,
    }
    impl<'tcx> MirVisitor<'tcx> for Mention<'_, 'tcx> {
        fn visit_operand(&mut self, operand: &Operand<'tcx>, _location: Location) {
            self.escaped |= matches!(operand.ty(&self.body.local_decls, self.tcx).kind(), TyKind::FnDef(did, _) if *did == self.callee.to_def_id());
        }
    }
    let mut calls = Vec::new();
    for owner in tcx.hir_body_owners() {
        if !tcx.is_mir_available(owner.to_def_id()) {
            return Err(Hold::MissingInventory);
        }
        let stored = tcx.mir_drops_elaborated_and_const_checked(owner);
        if stored.is_stolen() {
            return Err(Hold::MissingInventory);
        }
        let body = stored.borrow();
        let mut mention = Mention {
            tcx,
            body: &body,
            callee,
            escaped: false,
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                mention.visit_statement(
                    statement,
                    Location {
                        block,
                        statement_index,
                    },
                );
            }
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind {
                if matches!(func.ty(&body.local_decls, tcx).kind(), TyKind::FnDef(did, _) if *did == callee.to_def_id())
                {
                    calls.push((owner, block.as_u32()));
                }
                for arg in args {
                    mention.visit_operand(&arg.node, location);
                }
            } else {
                mention.visit_terminator(data.terminator(), location);
            }
        }
        if mention.escaped {
            return Err(Hold::Exposed);
        }
    }
    Ok(calls)
}

fn address(
    tcx: TyCtxt<'_>,
    caller: LocalDefId,
    span: Span,
    mutable: bool,
) -> Result<(Span, String), Hold> {
    fn stable<'tcx>(tcx: TyCtxt<'tcx>, caller: LocalDefId, expr: &Expr<'tcx>) -> bool {
        let types = tcx.typeck(caller);
        if types.type_dependent_def_id(expr.hir_id).is_some()
            || !types.expr_adjustments(expr).is_empty()
        {
            return false;
        }
        match expr.kind {
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                matches!(path.res, rustc_hir::def::Res::Local(_))
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                matches!(inner.kind, ExprKind::Path(_)) && stable(tcx, caller, inner)
            }
            ExprKind::Field(inner, _) => stable(tcx, caller, inner),
            _ => false,
        }
    }
    struct Find<'tcx> {
        tcx: TyCtxt<'tcx>,
        caller: LocalDefId,
        span: Span,
        mutable: bool,
        found: Vec<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if expr.span.source_callsite() == self.span.source_callsite()
                && let ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, mutable, inner) = expr.kind
                && (mutable == Mutability::Mut) == self.mutable
                && stable(self.tcx, self.caller, inner)
            {
                self.found.push(inner);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        tcx,
        caller,
        span,
        mutable,
        found: Vec::new(),
    };
    find.visit_body(tcx.hir_body_owned_by(caller));
    let [operand] = find.found.as_slice() else {
        return Err(Hold::SourceShape);
    };
    if span.from_expansion() || operand.span.from_expansion() {
        return Err(Hold::SourceShape);
    }
    Ok((
        operand.span,
        tcx.sess
            .source_map()
            .span_to_snippet(operand.span)
            .map_err(|_| Hold::SourceText)?,
    ))
}

impl SharedAddress {
    pub(crate) fn valid(&self) -> bool {
        self.permission.valid()
            && self.permission.sources.iter().any(|source| {
                source.mutable
                    && source.argument_span == self.argument_span
                    && source.operand_span == self.operand_span
                    && source.original == self.original
                    && source.operand == self.operand
            })
    }

    pub(crate) fn render(&self, original: &str) -> Option<String> {
        (original == self.original && self.valid()).then(|| format!("&({})", self.operand))
    }
}

impl Permission {
    fn digest(&self) -> String {
        format!(
            "{:x}",
            Sha256::digest(
                format!(
                    "shared-pair/v1:{:?}:{:?}:{:?}:{:?}",
                    self.request, self.required_sites, self.call_span, self.sources
                )
                .as_bytes()
            )
        )
    }

    pub(crate) fn valid(&self) -> bool {
        self.certificate.matches(&self.request)
            && self.seal == self.digest()
            && self.required_sites.contains(&self.request.left)
            && self.required_sites.contains(&self.request.right)
            && self.sources.len() == 2
            && self.sources[0].index == 0
            && self.sources[1].index == 1
    }

    pub(crate) fn receipt(&self) -> String {
        format!(
            "shared-pair-object-no-write/v1:{}:required={}:{}",
            self.seal,
            self.required_sites.len(),
            self.request.left.receipt_key()
        )
    }
}

impl Discovery {
    pub(crate) fn at(&self, callee: LocalDefId, site: &CallSite) -> Option<&Call> {
        self.calls.get(&call_key(callee, site))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn w5p_address_rejects_overloaded_deref() {
        ::utils::compilation::run_compiler_on_str(r#"
            struct Value(i32);
            impl core::ops::Deref for Value { type Target=i32; fn deref(&self)->&i32 { &self.0 } }
            impl core::ops::DerefMut for Value { fn deref_mut(&mut self)->&mut i32 { self.0 += 1; &mut self.0 } }
            fn target(_: *mut i32) {}
            fn caller(mut value: Value) { target(&mut *value); }
        "#, |tcx| {
            let caller = tcx.hir_body_owners().find(|did| tcx.item_name(did.to_def_id()).as_str()=="caller").unwrap();
            struct Find(Vec<Span>);
            impl<'tcx> Visitor<'tcx> for Find {
                fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                    if matches!(expr.kind, ExprKind::AddrOf(_, Mutability::Mut, _)) { self.0.push(expr.span); }
                    intravisit::walk_expr(self, expr);
                }
            }
            let mut found=Find(Vec::new()); found.visit_body(tcx.hir_body_owned_by(caller));
            assert_eq!(found.0.len(),1);
            assert_eq!(address(tcx,caller,found.0[0],true),Err(Hold::SourceShape));
        }).unwrap();
    }
}
