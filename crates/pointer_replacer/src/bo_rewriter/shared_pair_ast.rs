//! Structural shared-address rendering and final AST custody.

use rustc_ast::{
    BorrowKind, Expr, ExprKind, Mutability,
    ptr::P,
    visit::{self, Visitor},
};

use super::{
    ast_transform::RevertSet,
    bridge_receipt::SignatureClassId,
    decision::{
        DecisionTable,
        overlapping_pairs::consumer::{Permission, SharedAddress},
    },
};

fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

pub(crate) fn build(expr: &Expr, address: &SharedAddress) -> Option<ExprKind> {
    if !address.valid() || expr.span != address.argument_span {
        return None;
    }
    let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, operand) = &expr.kind else {
        return None;
    };
    if operand.span != address.operand_span
        || compact(&rustc_ast_pretty::pprust::expr_to_string(operand)) != compact(&address.operand)
    {
        return None;
    }
    let mut paren = (**operand).clone();
    paren.id = rustc_ast::node_id::DUMMY_NODE_ID;
    paren.attrs = Default::default();
    paren.tokens = None;
    paren.kind = ExprKind::Paren(operand.clone());
    Some(ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, P(paren)))
}

pub(crate) fn validate(
    krate: &rustc_ast::Crate,
    table: &DecisionTable,
    reverts: &RevertSet,
    owners: &rustc_ast::node_id::NodeMap<rustc_hir::def_id::LocalDefId>,
) -> Result<(), String> {
    // Reconcile independently observed permission carriers with the required
    // manifest. Removing the manifest cannot erase outstanding obligations.
    for permission in table
        .seams
        .overlap_proofs
        .iter()
        .filter_map(|proof| proof.shared_permission.as_ref())
        .chain(table.seams.edits.iter().filter_map(|edit| {
            edit.spec
                .shared_address
                .as_ref()
                .map(|address| &address.permission)
        }))
    {
        let owner = SignatureClassId::of(
            permission
                .request
                .left
                .callee
                .as_local()
                .ok_or("shared-pair:nonlocal")?,
        );
        if reverts.keeps(owner) && !table.seams.shared_required.contains(permission) {
            return Err("shared-pair:missing-required-manifest".into());
        }
    }
    for permission in &table.seams.shared_required {
        let owner = SignatureClassId::of(
            permission
                .request
                .left
                .callee
                .as_local()
                .ok_or("shared-pair:nonlocal")?,
        );
        if !reverts.keeps(owner) {
            continue;
        }
        if !permission.valid() {
            return Err("shared-pair:stale-permission".into());
        }
        struct Declaration<'a> {
            owners: &'a rustc_ast::node_id::NodeMap<rustc_hir::def_id::LocalDefId>,
            callee: rustc_hir::def_id::LocalDefId,
            matched: usize,
        }
        impl<'a, 'ast> Visitor<'ast> for Declaration<'a> {
            fn visit_item(&mut self, item: &'ast rustc_ast::Item) {
                if self.owners.get(&item.id) == Some(&self.callee)
                    && let rustc_ast::ItemKind::Fn(function) = &item.kind
                    && function.sig.decl.inputs.len() == 2
                    && function.sig.decl.inputs.iter().all(|arg| {
                        matches!(&arg.ty.kind,
                        rustc_ast::TyKind::Ref(_, mutable) if mutable.mutbl == Mutability::Not)
                    })
                {
                    self.matched += 1;
                }
                visit::walk_item(self, item);
            }
        }
        let mut declarations = Declaration {
            owners,
            callee: owner.local_def_id(),
            matched: 0,
        };
        declarations.visit_crate(krate);
        if declarations.matched != 1 {
            return Err("shared-pair:declaration-not-shared".into());
        }
        for key in [permission.request.left, permission.request.right] {
            if !table.seams.overlap_proofs.iter().any(|proof| {
                proof.proof_site_key == Some(key)
                    && proof.shared_permission.as_ref() == Some(permission)
            }) {
                return Err("shared-pair:missing-proof".into());
            }
        }
        for source in &permission.sources {
            if source.mutable
                && !table.seams.edits.iter().any(|edit| {
                    edit.span == source.argument_span
                        && edit
                            .spec
                            .shared_address
                            .as_ref()
                            .is_some_and(|address| address.permission == *permission)
                })
            {
                return Err("shared-pair:missing-render-plan".into());
            }
            struct Find<'a> {
                source: &'a super::decision::overlapping_pairs::consumer::Source,
                matched: usize,
            }
            impl<'a, 'ast> Visitor<'ast> for Find<'a> {
                fn visit_expr(&mut self, expr: &'ast Expr) {
                    if expr.span == self.source.argument_span {
                        let expected = if self.source.mutable {
                            format!("&({})", self.source.operand)
                        } else {
                            self.source.original.clone()
                        };
                        if matches!(
                            expr.kind,
                            ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, _)
                        ) && compact(&rustc_ast_pretty::pprust::expr_to_string(expr))
                            == compact(&expected)
                        {
                            self.matched += 1;
                        }
                    }
                    visit::walk_expr(self, expr);
                }
            }
            let mut find = Find { source, matched: 0 };
            find.visit_crate(krate);
            if find.matched != 1 {
                return Err(format!(
                    "shared-pair:terminal-render-count:{}",
                    find.matched
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn terminal(
    permissions: &[Permission],
    withheld: &std::collections::BTreeSet<SignatureClassId>,
    renders: &std::collections::BTreeMap<(u32, u32), String>,
) -> String {
    if permissions.is_empty() {
        return String::new();
    }
    let mut out = String::from("caller\tcallee\tpermission\tstate\trendered_call\n");
    for permission in permissions {
        let owner = SignatureClassId::of(
            permission
                .request
                .left
                .callee
                .as_local()
                .expect("native permission"),
        );
        let render = renders.get(&(permission.call_span.lo().0, permission.call_span.hi().0));
        let state = if withheld.contains(&owner) {
            "retracted"
        } else if render.is_some() {
            "applied"
        } else {
            "held:no-terminal-render"
        };
        out.push_str(&format!(
            "{}\t{}\t{}\t{state}\t{}\n",
            permission.caller,
            permission.callee,
            permission.receipt(),
            render.map_or("-".into(), |text| text
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" "))
        ));
    }
    out
}
