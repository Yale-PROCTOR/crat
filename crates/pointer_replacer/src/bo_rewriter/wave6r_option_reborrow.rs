//! Reborrow an admitted optional mutable argument at a local call.
//!
//! Moving the Option consumes its reference. `as_deref_mut` lends the same
//! payload and preserves None; the ordinary compiler checks the shorter loan.
//! Only scalar-result calls with a later use of this binding are repaired. A
//! call inside a loop that the binding outlives has one: the loop's next pass.
//! Final transfers and calls returning a possible borrow keep their value flow.

use rustc_ast::mut_visit::MutVisitor;
use rustc_hir::{
    ExprKind, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    ast_transform::{Composition, RevertSet},
    decision::{Decision, DecisionTable, SubjectKind},
};

pub(super) fn apply(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let mut sources = rustc_hash::FxHashMap::default();
    let mut targets = rustc_hash::FxHashMap::default();
    for (subject, decision) in &table.entries {
        if reverts.keeps_subject(subject.fn_did, subject.hir_id)
            && let Decision::Opt {
                mutable: true,
                slice,
                ..
            } = decision
        {
            sources.insert((subject.fn_did, subject.hir_id), *slice);
            if let SubjectKind::Param { hir_index } = subject.kind {
                targets.insert((subject.fn_did, hir_index), *slice);
            }
        }
    }
    struct Candidate {
        binding: rustc_hir::HirId,
        argument: Span,
        call: Span,
        index: usize,
        repeats: bool,
    }
    struct Calls<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sources: &'a rustc_hash::FxHashMap<(LocalDefId, rustc_hir::HirId), bool>,
        targets: &'a rustc_hash::FxHashMap<(LocalDefId, usize), bool>,
        owner: LocalDefId,
        uses: rustc_hash::FxHashMap<rustc_hir::HirId, rustc_span::BytePos>,
        loops: Vec<Span>,
        candidates: Vec<Candidate>,
    }
    impl<'tcx> Visitor<'tcx> for Calls<'_, 'tcx> {
        fn visit_expr(&mut self, call: &'tcx rustc_hir::Expr<'tcx>) {
            if let ExprKind::Loop(..) = call.kind {
                self.loops.push(call.span);
                intravisit::walk_expr(self, call);
                self.loops.pop();
                return;
            }
            if let ExprKind::Path(QPath::Resolved(_, path)) = call.kind
                && let Res::Local(binding) = path.res
            {
                self.uses
                    .entry(binding)
                    .and_modify(|last| *last = (*last).max(call.span.hi()))
                    .or_insert(call.span.hi());
            }
            intravisit::walk_expr(self, call);
            let ExprKind::Call(callee, args) = call.kind else { return };
            let ExprKind::Path(ref path) = callee.kind else { return };
            let Res::Def(_, did) = self.tcx.typeck(self.owner).qpath_res(path, callee.hir_id)
            else {
                return;
            };
            let Some(callee) = did.as_local() else { return };
            use rustc_middle::ty::TyKind;
            match self
                .tcx
                .fn_sig(did)
                .skip_binder()
                .skip_binder()
                .output()
                .kind()
            {
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_)
                | TyKind::Never => {}
                TyKind::Tuple(fields) if fields.is_empty() => {}
                _ => return,
            }
            for (index, arg) in args.iter().enumerate() {
                let ExprKind::Path(QPath::Resolved(_, path)) = arg.kind else { continue };
                let Res::Local(binding) = path.res else { continue };
                let Some(source_slice) = self.sources.get(&(self.owner, binding)) else { continue };
                if self.targets.get(&(callee, index)) == Some(source_slice) {
                    // R738-1 (brotli `BrotliDecoderDecompressStream::next_out`):
                    // a binding declared outside an enclosing loop is moved
                    // again by the call's next pass.
                    let declared = self.tcx.hir_span(binding);
                    let repeats = self.loops.iter().any(|body| !body.contains(declared));
                    self.candidates.push(Candidate {
                        binding,
                        argument: arg.span,
                        call: call.span,
                        index,
                        repeats,
                    });
                }
            }
        }
    }
    let mut sites = rustc_hash::FxHashSet::default();
    // An A5 / PAIR raw-view wrapper re-parses the call it wraps (`{ let
    // __crat_a5_raw_N = ..; callee(..) }`), so its arguments no longer carry
    // their source spans: those are found by the call's span and position.
    let mut wrapped: rustc_hash::FxHashMap<Span, Vec<usize>> = Default::default();
    let mut owners = rustc_hash::FxHashSet::default();
    for &(owner, _) in sources.keys() {
        if owners.insert(owner)
            && let Some(body) = tcx.hir_node_by_def_id(owner).body_id()
        {
            let mut calls = Calls {
                tcx,
                sources: &sources,
                targets: &targets,
                owner,
                uses: Default::default(),
                loops: Vec::new(),
                candidates: Vec::new(),
            };
            calls.visit_body(tcx.hir_body(body));
            for candidate in calls.candidates {
                if candidate.repeats
                    || calls
                        .uses
                        .get(&candidate.binding)
                        .is_some_and(|last| *last > candidate.argument.hi())
                {
                    sites.insert(candidate.argument);
                    wrapped
                        .entry(candidate.call)
                        .or_default()
                        .push(candidate.index);
                }
            }
        }
    }
    struct Apply<'a> {
        sites: &'a rustc_hash::FxHashSet<Span>,
        wrapped: &'a rustc_hash::FxHashMap<Span, Vec<usize>>,
        guard: &'a mut Composition,
        failure: Option<String>,
    }
    impl Apply<'_> {
        /// Parse only the new method shell, retaining the original argument as
        /// its receiver. No source expression is printed and re-parsed.
        fn lend(&mut self, argument: &mut rustc_ast::Expr) {
            let Ok(mut replacement) = super::ast_transform::graft_expr("__crat_arg.as_deref_mut()")
            else {
                self.failure = Some("optional-call-reborrow-template".into());
                return;
            };
            let rustc_ast::ExprKind::MethodCall(call) = &mut replacement.kind else {
                unreachable!()
            };
            call.receiver = rustc_ast::ptr::P(argument.clone());
            *argument = replacement;
        }
    }
    impl MutVisitor for Apply<'_> {
        fn visit_expr(&mut self, expr: &mut rustc_ast::Expr) {
            rustc_ast::mut_visit::walk_expr(self, expr);
            if self.sites.contains(&expr.span) && matches!(expr.kind, rustc_ast::ExprKind::Path(..))
            {
                if !self
                    .guard
                    .claim(expr.id, expr.span, "optional-call-reborrow")
                {
                    self.failure = Some("optional-call-reborrow-collision".into());
                    return;
                }
                self.lend(expr);
                return;
            }
            let Some(arguments) = self.wrapped.get(&expr.span) else { return };
            let rustc_ast::ExprKind::Block(block, _) = &mut expr.kind else { return };
            let Some(rustc_ast::Stmt {
                kind: rustc_ast::StmtKind::Expr(call),
                ..
            }) = block.stmts.last_mut()
            else {
                return;
            };
            let rustc_ast::ExprKind::Call(_, args) = &mut call.kind else { return };
            // The wrapper's claim on the call covers its spanless arguments; a
            // view replaces only raw formals, so an optional keeps its position.
            for &index in arguments {
                if let Some(arg) = args.get_mut(index) {
                    self.lend(arg);
                }
            }
        }
    }
    let mut apply = Apply {
        sites: &sites,
        wrapped: &wrapped,
        guard,
        failure: None,
    };
    apply.visit_crate(krate);
    apply.failure.map_or(Ok(()), Err)
}
