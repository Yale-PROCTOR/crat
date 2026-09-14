//! Realize parameter cursors after use grafts and before the safe-body split.

use rustc_ast::{ItemKind, PatKind, mut_visit::MutVisitor};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;

use crate::bo_rewriter::{
    ast_transform::{Composition, RevertSet, graft_expr},
    decision::{Decision, DecisionTable, SubjectKind},
};

pub(crate) fn apply(
    table: &DecisionTable,
    reverts: &RevertSet,
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let expected = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| {
            let selected = match decision {
                Decision::Cursor { plan, .. } => plan.wrapper && plan.parameter,
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::NestedSlice { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => false,
            };
            (selected && reverts.keeps_subject(subject.fn_did, subject.hir_id))
                .then_some((subject.fn_did, subject.hir_id))
        })
        .collect::<FxHashSet<_>>();
    if expected.is_empty() {
        return Ok(());
    }
    struct Shadows<'a> {
        table: &'a DecisionTable,
        expected: &'a FxHashSet<(LocalDefId, rustc_hir::HirId)>,
        global_map: &'a rustc_ast::node_id::NodeMap<LocalDefId>,
        guard: &'a mut Composition,
        placed: FxHashSet<(LocalDefId, rustc_hir::HirId)>,
        failure: Option<String>,
    }
    impl MutVisitor for Shadows<'_> {
        fn visit_item(&mut self, item: &mut rustc_ast::Item) {
            rustc_ast::mut_visit::walk_item(self, item);
            if self.failure.is_some() {
                return;
            }
            let Some(&owner) = self.global_map.get(&item.id) else { return };
            let ItemKind::Fn(function) = &mut item.kind else { return };
            let mut statements = Vec::new();
            let mut nodes = Vec::new();
            for (subject, decision) in &self.table.entries {
                let node = (subject.fn_did, subject.hir_id);
                if subject.fn_did != owner || !self.expected.contains(&node) {
                    continue;
                }
                let (mutable, plan) = match decision {
                    Decision::Cursor { mutable, plan } => (mutable, plan),
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::NestedSlice { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. }
                    | Decision::Box(_)
                    | Decision::Degraded(_) => unreachable!("selected cursor parameter"),
                };
                let SubjectKind::Param { hir_index } = subject.kind else {
                    self.failure = Some("cursor-parameter-shadow-nonparameter".into());
                    return;
                };
                let Some(parameter) = function.sig.decl.inputs.get(hir_index) else {
                    self.failure = Some("cursor-parameter-shadow-missing-parameter".into());
                    return;
                };
                let PatKind::Ident(_, name, None) = &parameter.pat.kind else {
                    self.failure = Some("cursor-parameter-shadow-nonidentifier".into());
                    return;
                };
                let wrapper = if *mutable {
                    "SliceCursorMut"
                } else {
                    "SliceCursor"
                };
                let constructor = format!("crate::slice_cursor::{wrapper}::new");
                let value = if plan.optional {
                    format!("{name}.map({constructor})")
                } else {
                    format!("{constructor}({name})")
                };
                let expression = match graft_expr(&format!("{{ let mut {name} = {value}; }}")) {
                    Ok(expression) => expression,
                    Err(error) => {
                        self.failure = Some(format!("cursor-parameter-shadow-parse:{error}"));
                        return;
                    }
                };
                let rustc_ast::ExprKind::Block(block, _) = expression.kind else { unreachable!() };
                statements.extend(block.stmts.iter().cloned());
                nodes.push(node);
            }
            if statements.is_empty() {
                return;
            }
            let Some(body) = function.body.as_mut() else {
                self.failure = Some("cursor-parameter-shadow-missing-body".into());
                return;
            };
            if !self
                .guard
                .claim(body.id, body.span, "cursor-parameter-shadow")
            {
                self.failure = Some("cursor-parameter-shadow-composition-refused".into());
                return;
            }
            statements.extend(body.stmts.iter().cloned());
            body.stmts = statements.into_iter().collect();
            self.placed.extend(nodes);
        }
    }
    let mut visitor = Shadows {
        table,
        expected: &expected,
        global_map,
        guard,
        placed: FxHashSet::default(),
        failure: None,
    };
    visitor.visit_crate(krate);
    if let Some(error) = visitor.failure {
        return Err(error);
    }
    if visitor.placed != expected {
        return Err("cursor-parameter-shadow-unmatched".into());
    }
    Ok(())
}
