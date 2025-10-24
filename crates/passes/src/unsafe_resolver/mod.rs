//! Remove unnecessary `unsafe`.

use rustc_ast::{
    self as ast, DUMMY_NODE_ID,
    mut_visit::{self, MutVisitor as _},
    ptr::P,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::Res,
    def_id::DefId,
    intravisit::{self, VisitorExt},
};
use rustc_index::bit_set::ChunkedBitSet;
use rustc_middle::{hir::nested_filter, thir, ty::TyCtxt};
use rustc_span::{Span, def_id::LocalDefId, symbol::sym};
use serde::Deserialize;
use smallvec::smallvec;
use utils::{path, unsafety};

#[derive(Clone, Copy, Debug, Default, Deserialize)]
pub struct Config {
    pub remove_unused: bool,
    pub remove_no_mangle: bool,
    pub replace_pub: bool,
}

pub fn resolve_unsafe(config: &Config, tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut visitor = HirVisitor {
        tcx,
        mains: vec![],
        fns: vec![],
        uses: vec![],
        used: FxHashMap::default(),
        item_mods: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    let mut used = visitor.used;

    // trait method calls are not resolved in HIR, so we visit THIR
    for def_id in tcx.hir_body_owners() {
        let (thir, expr_id) = tcx.thir_body(def_id).unwrap();
        let thir = thir.borrow();
        let mut visitor = ThirVisitor {
            thir: &thir,
            callees: vec![],
        };
        use thir::visit::Visitor as _;
        visitor.visit_expr(&thir[expr_id]);
        used.entry(def_id).or_default().extend(visitor.callees);
    }

    let entries = if visitor.mains.is_empty() {
        // when no main, consider all functions as entry points
        &visitor.fns
    } else {
        &visitor.mains
    };
    let used_items: FxHashSet<_> = entries
        .iter()
        .flat_map(|def_id| utils::graph::reachable_vertices(&used, *def_id))
        .collect();

    let mut def_ids = vec![];
    for ids in used.values() {
        def_ids.extend(ids.iter().copied());
    }
    for def_id in def_ids {
        used.entry(def_id).or_default();
    }

    let used_inv = utils::graph::inverse(&used);
    let removable_uses: FxHashSet<_> = visitor
        .uses
        .iter()
        .filter_map(|(use_def_id, def_ids)| {
            let use_mod = visitor.item_mods.get(use_def_id);
            // for each def_id imported by the use, check if all def_id is local and each item
            // using this def_id is unused or in a different module
            def_ids
                .iter()
                .all(|def_id| {
                    def_id.as_local().is_some_and(|def_id| {
                        !used_inv.get(&def_id).is_some_and(|using_items| {
                            using_items.iter().any(|item| {
                                used_items.contains(item) && use_mod == visitor.item_mods.get(item)
                            })
                        })
                    })
                })
                .then_some(*use_def_id)
        })
        .collect();

    let unsafe_fns = find_unsafe_fns(tcx);

    let mut visitor = AstVisitor {
        ast_to_hir,
        unsafe_fns,
        used_items,
        removable_uses,
        config: *config,
    };
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

struct AstVisitor {
    ast_to_hir: utils::ir::AstToHir,
    unsafe_fns: FxHashSet<LocalDefId>,
    used_items: FxHashSet<LocalDefId>,
    removable_uses: FxHashSet<LocalDefId>,
    config: Config,
}

impl mut_visit::MutVisitor for AstVisitor {
    fn flat_map_foreign_item(
        &mut self,
        item: P<ast::ForeignItem>,
    ) -> smallvec::SmallVec<[P<ast::ForeignItem>; 1]> {
        if self.config.remove_unused
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && !self.used_items.contains(def_id)
        {
            return smallvec![];
        }
        mut_visit::walk_flat_map_foreign_item(self, item)
    }

    fn flat_map_assoc_item(
        &mut self,
        item: P<ast::AssocItem>,
        ctxt: ast::visit::AssocCtxt,
    ) -> smallvec::SmallVec<[P<ast::AssocItem>; 1]> {
        if self.config.remove_unused
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && !self.used_items.contains(def_id)
        {
            return smallvec![];
        }
        mut_visit::walk_flat_map_assoc_item(self, item, ctxt)
    }

    fn flat_map_item(&mut self, item: P<ast::Item>) -> smallvec::SmallVec<[P<ast::Item>; 1]> {
        if self.config.remove_unused
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
        {
            match &item.kind {
                ast::ItemKind::ExternCrate(..)
                | ast::ItemKind::Mod(..)
                | ast::ItemKind::ForeignMod(..)
                | ast::ItemKind::GlobalAsm(..)
                | ast::ItemKind::MacroDef(..)
                | ast::ItemKind::Delegation(..)
                | ast::ItemKind::DelegationMac(..) => {}
                ast::ItemKind::Use(tree) => {
                    if self.removable_uses.contains(def_id)
                        || matches!(tree.kind, ast::UseTreeKind::Simple(None))
                            && tree.prefix.segments.last().unwrap().ident.name == sym::libc
                    {
                        return smallvec![];
                    }
                }
                _ => {
                    if !self.used_items.contains(def_id) {
                        return smallvec![];
                    }
                }
            }
        }
        let mut items = mut_visit::walk_flat_map_item(self, item);
        items.retain(|item| match &item.kind {
            ast::ItemKind::Mod(_, _, ast::ModKind::Loaded(items, _, _, _)) => !items.is_empty(),
            ast::ItemKind::ForeignMod(md) => !md.items.is_empty(),
            _ => true,
        });
        items
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        let path = path!("crate");
        if self.config.replace_pub && item.vis.kind.is_pub() {
            if let ast::ItemKind::Fn(box ast::Fn { ident, .. }) = item.kind
                && ident.name == sym::main
            {
            } else {
                item.vis.kind = ast::VisibilityKind::Restricted {
                    path: ast::ptr::P::new(path),
                    id: DUMMY_NODE_ID,
                    shorthand: true,
                };
            }
        }

        if self.config.remove_no_mangle {
            item.attrs.retain(|attr| {
                let ast::AttrKind::Normal(normal) = &attr.kind else { return true };
                normal.item.path.segments.last().unwrap().ident.name != sym::no_mangle
            });
        }

        if let ast::ItemKind::Fn(box ast::Fn { sig, .. }) = &mut item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && !self.unsafe_fns.contains(def_id)
            && matches!(sig.header.safety, ast::Safety::Unsafe(_))
        {
            sig.header.safety = ast::Safety::Default;
        }

        mut_visit::walk_item(self, item);
    }
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    mains: Vec<LocalDefId>,
    fns: Vec<LocalDefId>,
    uses: Vec<(LocalDefId, Vec<DefId>)>,
    used: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    item_mods: FxHashMap<LocalDefId, LocalDefId>,
}

impl HirVisitor<'_> {
    fn add_item_mod(&mut self, def_id: LocalDefId) {
        let module = self
            .tcx
            .hir_parent_iter(HirId::make_owner(def_id))
            .find_map(|(hir_id, node)| {
                let hir::Node::Item(item) = node else { return None };
                let hir::ItemKind::Mod(_, _) = item.kind else { return None };
                Some(hir_id.owner.def_id)
            });
        if let Some(module) = module {
            self.item_mods.insert(def_id, module);
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem<'tcx>) {
        self.add_item_mod(item.owner_id.def_id);
        intravisit::walk_foreign_item(self, item);
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        self.add_item_mod(item.owner_id.def_id);
        match item.kind {
            hir::ItemKind::Fn { ident, .. } => {
                self.fns.push(item.owner_id.def_id);
                if ident.name == sym::main {
                    self.mains.push(item.owner_id.def_id);
                }
            }
            hir::ItemKind::Impl(imp) => {
                if let Some(of_trait) = imp.of_trait
                    && let Some(def_id) = of_trait.trait_def_id()
                {
                    if let Some(def_id) = def_id.as_local() {
                        // if a trait is used, then the impl is considered used
                        self.used
                            .entry(def_id)
                            .or_default()
                            .insert(item.owner_id.def_id);
                    } else {
                        // if a trait is not local, all the associated items are considered used
                        self.used
                            .entry(item.owner_id.def_id)
                            .or_default()
                            .extend(imp.items.iter().map(|id| id.id.owner_id.def_id));
                    }
                }

                let mut visitor = HirTyVisitor {
                    tcx: self.tcx,
                    def_ids: vec![],
                };
                visitor.visit_ty_unambig(imp.self_ty);
                for def_id in visitor.def_ids {
                    // if a type is used, then the impl is considered used
                    self.used
                        .entry(def_id)
                        .or_default()
                        .insert(item.owner_id.def_id);
                }

                for item_ref in imp.items {
                    let assoc_item = self.tcx.hir_impl_item(item_ref.id);
                    // if an associated item is used, then the impl is considered used
                    self.used
                        .entry(assoc_item.owner_id.def_id)
                        .or_default()
                        .insert(item.owner_id.def_id);
                    if let Some(trait_item_def_id) = item_ref.trait_item_def_id
                        && let Some(trait_item_def_id) = trait_item_def_id.as_local()
                    {
                        // if an associated item is used, then the corresponding trait item is
                        // considered used, and vice versa
                        self.used
                            .entry(assoc_item.owner_id.def_id)
                            .or_default()
                            .insert(trait_item_def_id);
                        self.used
                            .entry(trait_item_def_id)
                            .or_default()
                            .insert(assoc_item.owner_id.def_id);
                    }
                }
            }
            hir::ItemKind::Trait(_, _, _, _, _, items) => {
                for item_ref in items {
                    // if an associated item is used, then the trait is considered used
                    self.used
                        .entry(item_ref.id.owner_id.def_id)
                        .or_default()
                        .insert(item.owner_id.def_id);
                }
            }
            hir::ItemKind::Use(path, _) => {
                let def_ids: Vec<_> = [path.res.value_ns, path.res.type_ns, path.res.macro_ns]
                    .into_iter()
                    .filter_map(|res| {
                        if let Some(Res::Def(_, def_id)) = res {
                            Some(def_id)
                        } else {
                            None
                        }
                    })
                    .collect();
                self.uses.push((item.owner_id.def_id, def_ids));
            }
            _ => {}
        }
        intravisit::walk_item(self, item)
    }

    fn visit_variant_data(&mut self, vd: &'tcx hir::VariantData<'tcx>) {
        if let Some((_, hir_id, def_id)) = vd.ctor() {
            // if a constructor is used, then the struct is considered used
            self.used
                .entry(def_id)
                .or_default()
                .insert(hir_id.owner.def_id);
        }
        intravisit::walk_struct_def(self, vd)
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, hir_id: HirId) {
        if let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            self.used
                .entry(hir_id.owner.def_id)
                .or_default()
                .insert(def_id);
        }
        intravisit::walk_path(self, path)
    }
}

struct HirTyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_ids: Vec<LocalDefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirTyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _: HirId) {
        if let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            self.def_ids.push(def_id);
        }
        intravisit::walk_path(self, path)
    }
}

struct ThirVisitor<'thir, 'tcx> {
    thir: &'thir thir::Thir<'tcx>,
    callees: Vec<LocalDefId>,
}

impl<'thir, 'tcx> thir::visit::Visitor<'thir, 'tcx> for ThirVisitor<'thir, 'tcx> {
    fn thir(&self) -> &'thir thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        if let rustc_middle::ty::TyKind::FnDef(def_id, _) = expr.ty.kind()
            && let Some(def_id) = def_id.as_local()
        {
            self.callees.push(def_id);
        }
        thir::visit::walk_expr(self, expr);
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
        let hir::ItemKind::Fn { sig, .. } = item.kind else { continue };
        let mut handler = UnsafetyHandler::default();
        unsafety::check_unsafety(def_id, &mut handler, tcx);
        call_graph.insert(def_id, handler.callees);
        if handler.is_unsafe || sig.decl.c_variadic {
            self_unsafe_fns.insert(def_id);
        }
    }

    let sccs: utils::graph::Sccs<_, true> = utils::graph::sccs_copied(&call_graph);

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
