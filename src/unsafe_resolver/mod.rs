//! Remove unnecessary `unsafe`.

use rustc_ast::{
    self as ast, DUMMY_NODE_ID,
    mut_visit::{self, MutVisitor as _},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_index::bit_set::ChunkedBitSet;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, def_id::LocalDefId, symbol::sym};
use serde::Deserialize;
use utils::{path, unsafety};

use crate::{ast_utils, graph_utils};

#[derive(Debug, Default, Deserialize)]
pub struct Config {
    pub remove_no_mangle: bool,
    pub replace_pub: bool,
}

pub fn resolve_unsafe(config: &Config, tcx: TyCtxt<'_>) {
    let unsafe_fns = find_unsafe_fns(tcx)
        .into_iter()
        .map(|def_id| {
            let hir::Node::Item(item) = tcx.hir_node_by_def_id(def_id) else { panic!() };
            let hir::ItemKind::Fn { ident, .. } = &item.kind else { panic!() };
            ident.span
        })
        .collect();
    let mut visitor = AstVisitor {
        unsafe_fns,
        remove_no_mangle: config.remove_no_mangle,
        replace_pub: config.replace_pub,
        updated: false,
    };
    let res = ast_utils::transform_ast(
        |krate| {
            visitor.updated = false;
            visitor.visit_crate(krate);
            visitor.updated
        },
        tcx,
    );
    res.apply();
}

struct AstVisitor {
    unsafe_fns: FxHashSet<Span>,
    remove_no_mangle: bool,
    replace_pub: bool,
    updated: bool,
}

impl mut_visit::MutVisitor for AstVisitor {
    fn visit_item(&mut self, item: &mut ast::Item) {
        let path = path!("crate");
        if self.replace_pub && item.vis.kind.is_pub() {
            if let ast::ItemKind::Fn(box ast::Fn { ident, .. }) = item.kind
                && ident.name == sym::main
            {
            } else {
                item.vis.kind = ast::VisibilityKind::Restricted {
                    path: ast::ptr::P::new(path),
                    id: DUMMY_NODE_ID,
                    shorthand: true,
                };
                self.updated = true;
            }
        }

        if self.remove_no_mangle {
            item.attrs.retain(|attr| {
                let ast::AttrKind::Normal(normal) = &attr.kind else { return true };
                let b = normal.item.path.segments.last().unwrap().ident.name != sym::no_mangle;
                self.updated |= !b;
                b
            });
        }

        if let ast::ItemKind::Fn(box ast::Fn { ident, sig, .. }) = &mut item.kind
            && !self.unsafe_fns.contains(&ident.span)
            && matches!(sig.header.safety, ast::Safety::Unsafe(_))
        {
            sig.header.safety = ast::Safety::Default;
            self.updated = true;
        }

        mut_visit::walk_item(self, item);
    }
}

#[derive(Default)]
struct UnsafetyHandler {
    callees: FxHashSet<LocalDefId>,
    is_unsafe: bool,
}

impl unsafety::UnsafetyHandler for UnsafetyHandler {
    fn handle_unsafety(&mut self, kind: unsafety::UnsafeOpKind, _: Span, tcx: TyCtxt<'_>) {
        if let unsafety::UnsafeOpKind::CallToUnsafeFunction(Some(def_id)) = kind
            && let Some(def_id) = def_id.as_local()
            && let hir::Node::Item(item) = tcx.hir_node_by_def_id(def_id)
            && matches!(item.kind, hir::ItemKind::Fn { .. })
        {
            self.callees.insert(def_id);
            return;
        }
        self.is_unsafe = true;
    }
}

fn find_unsafe_fns(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    let mut call_graph = FxHashMap::default();
    let mut self_unsafe_fns = FxHashSet::default();
    for item_id in tcx.hir_free_items() {
        let def_id = item_id.owner_id.def_id;
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::Fn { sig, .. } = item.kind else { continue };
        let mut handler = UnsafetyHandler::default();
        unsafety::check_unsafety(def_id, &mut handler, tcx);
        call_graph.insert(def_id, handler.callees);
        if handler.is_unsafe || sig.decl.c_variadic {
            self_unsafe_fns.insert(def_id);
        }
    }

    let sccs: graph_utils::Sccs<_, true> = graph_utils::sccs_copied(&call_graph);

    let mut is_scc_unsafe = ChunkedBitSet::new_empty(sccs.scc_elems.len());
    for scc_id in sccs.post_order() {
        if !is_scc_unsafe.contains(scc_id) {
            let scc = &sccs.scc_elems[scc_id];
            if scc.intersection(&self_unsafe_fns).next().is_some() {
                is_scc_unsafe.insert(scc_id);
            } else {
                continue;
            }
        }
        for pred in sccs.predecessors(scc_id) {
            is_scc_unsafe.insert(*pred);
        }
    }

    let mut unsafe_fns: FxHashSet<LocalDefId> = FxHashSet::default();
    for scc_id in is_scc_unsafe.iter() {
        unsafe_fns.extend(&sccs.scc_elems[scc_id]);
    }
    unsafe_fns
}

#[cfg(test)]
mod tests;
