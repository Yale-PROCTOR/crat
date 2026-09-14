//! Place the index declarations carried by surviving forward slice parameters.

use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    ast_transform::{Composition, RevertSet, graft_expr},
    bridge_receipt::SignatureClassId,
    decision::DecisionTable,
};

/// Wrap the already selected argument subtree, preserving its exact source
/// identity. The same carried view renders the byte-plan operand.
pub(super) fn argument(
    original: rustc_ast::Expr,
    view: Option<&super::decision::slice_forms::ForwardView>,
) -> Option<rustc_ast::Expr> {
    let Some(view) = view else { return Some(original) };
    const PLACEHOLDER: &str = "__CRAT_FORWARD_SLICE_ARGUMENT";
    let mut expression = graft_expr(&view.render(PLACEHOLDER)).ok()?;
    struct Replace {
        original: rustc_ast::Expr,
        hits: usize,
    }
    impl MutVisitor for Replace {
        fn visit_expr(&mut self, expression: &mut rustc_ast::Expr) {
            if matches!(&expression.kind, rustc_ast::ExprKind::Path(None, path)
                if path.segments.len() == 1 && path.segments[0].ident.name.as_str() == PLACEHOLDER)
            {
                *expression = self.original.clone();
                self.hits += 1;
                return;
            }
            mut_visit::walk_expr(self, expression);
        }
    }
    let mut replace = Replace { original, hits: 0 };
    replace.visit_expr(&mut expression);
    (replace.hits == 1).then_some(expression)
}

pub(super) fn apply(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    struct OriginalNames<'a> {
        wanted: &'a str,
        collision: bool,
    }
    impl<'tcx> Visitor<'tcx> for OriginalNames<'_> {
        fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
            if let rustc_hir::PatKind::Binding(_, _, ident, _) = pat.kind {
                self.collision |= ident.name.as_str() == self.wanted;
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let mut bodies = FxHashMap::<Span, Vec<String>>::default();
    let mut subjects = FxHashSet::default();
    for parameter in &table.forward_slice_parameters {
        let (owner, binding) = parameter.node;
        if !reverts.keeps(SignatureClassId::of(owner))
            || !reverts.keeps_subject(owner, binding)
            || !table.entries.iter().any(|(subject, decision)| {
                (subject.fn_did, subject.hir_id) == parameter.node
                    && matches!(
                        super::decision::seam::form_of(decision),
                        super::decision::seam::Form::Slice { .. }
                    )
            })
        {
            continue;
        }
        if !subjects.insert(parameter.node) {
            return Err("forward-slice-index:duplicate-subject".into());
        }
        if parameter.body_span.is_dummy() {
            return Err("forward-slice-index:missing-body-span".into());
        }
        let mut original_names = OriginalNames {
            wanted: &parameter.index_name,
            collision: false,
        };
        original_names.visit_body(tcx.hir_body_owned_by(owner));
        if original_names.collision {
            return Err(format!(
                "forward-slice-index:name-collision:{}",
                parameter.index_name
            ));
        }
        let names = bodies.entry(parameter.body_span).or_default();
        if names.contains(&parameter.index_name) {
            return Err(format!(
                "forward-slice-index:duplicate-name:{}",
                parameter.index_name
            ));
        }
        names.push(parameter.index_name.clone());
    }
    for names in bodies.values_mut() {
        names.sort();
    }

    struct CurrentNames<'a> {
        wanted: &'a [String],
        collision: Option<String>,
    }
    impl<'ast> rustc_ast::visit::Visitor<'ast> for CurrentNames<'_> {
        fn visit_pat(&mut self, pat: &'ast rustc_ast::Pat) {
            if let rustc_ast::PatKind::Ident(_, ident, _) = &pat.kind
                && self.wanted.iter().any(|name| ident.name.as_str() == name)
            {
                self.collision = Some(ident.name.to_string());
            }
            rustc_ast::visit::walk_pat(self, pat);
        }
    }

    struct Insert<'a> {
        bodies: &'a FxHashMap<Span, Vec<String>>,
        placed: FxHashSet<Span>,
        guard: &'a mut Composition,
        failure: Option<String>,
    }
    impl MutVisitor for Insert<'_> {
        fn visit_block(&mut self, block: &mut rustc_ast::Block) {
            if self.failure.is_some() {
                return;
            }
            mut_visit::walk_block(self, block);
            if self.failure.is_some() {
                return;
            }
            let Some(names) = self.bodies.get(&block.span) else { return };
            if self.placed.contains(&block.span) {
                self.failure = Some("forward-slice-index:duplicate-body-placement".into());
                return;
            }
            let mut current_names = CurrentNames {
                wanted: names,
                collision: None,
            };
            rustc_ast::visit::Visitor::visit_block(&mut current_names, block);
            if let Some(name) = current_names.collision {
                self.failure = Some(format!("forward-slice-index:name-collision:{name}"));
                return;
            }
            let declarations = names
                .iter()
                .map(|name| format!("let mut {name}: usize = 0;"))
                .collect::<Vec<_>>()
                .join(" ");
            let parsed = match graft_expr(&format!("{{ {declarations} }}")) {
                Ok(parsed) => parsed,
                Err(_) => {
                    self.failure = Some("forward-slice-index:unparseable-declaration".into());
                    return;
                }
            };
            let rustc_ast::ExprKind::Block(mut prefix, _) = parsed.kind else {
                self.failure = Some("forward-slice-index:declaration-not-block".into());
                return;
            };
            if !self
                .guard
                .claim(block.id, block.span, "forward-slice-index")
            {
                self.failure = Some("forward-slice-index:composition-refused".into());
                return;
            }
            // Keep every existing statement and its identity, including the
            // already transformed uses and boundary adapters inside the body.
            prefix.stmts.append(&mut block.stmts);
            block.stmts = std::mem::take(&mut prefix.stmts);
            self.placed.insert(block.span);
        }
    }

    let mut insert = Insert {
        bodies: &bodies,
        placed: FxHashSet::default(),
        guard,
        failure: None,
    };
    insert.visit_crate(krate);
    if let Some(failure) = insert.failure {
        return Err(failure);
    }
    let unmatched = bodies
        .keys()
        .filter(|span| !insert.placed.contains(span))
        .count();
    if unmatched != 0 {
        return Err(format!("forward-slice-index:unmatched-bodies:{unmatched}"));
    }
    Ok(())
}
