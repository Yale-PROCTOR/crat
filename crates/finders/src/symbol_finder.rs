use std::{fs, path::Path};

use rustc_ast::{Extern, ItemKind, TyKind, VisibilityKind, visit::Visitor};
use rustc_ast_pretty::pprust::item_to_string;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

pub fn run(file: &Path, kind: &str, name: &str, _tcx: TyCtxt<'_>) {
    let code = fs::read_to_string(file).unwrap();
    let mut krate = utils::ast::parse_crate(code);

    let mut unnamed_graph = FxHashMap::default();
    let mut unnamed_code = FxHashMap::default();
    let mut unnameds = FxHashSet::default();
    let mut found = false;

    for item in &mut krate.items {
        item.vis.kind = VisibilityKind::Public;
        if let ItemKind::Fn(f) = &mut item.kind {
            item.attrs.clear();
            f.sig.header.ext = Extern::None;
        }
        if matches!(item.kind, ItemKind::Struct(..) | ItemKind::Union(..)) {
            item.attrs.retain(|attr| {
                if let Some(name) = attr.name()
                    && name.as_str() == "repr"
                {
                    false
                } else {
                    true
                }
            });
        }

        if let Some(ident) = item.kind.ident()
            && ident.name.as_str().starts_with("C2RustUnnamed")
            && matches!(item.kind, ItemKind::Struct(..) | ItemKind::Union(..))
        {
            let mut visitor = UnnamedVisitor::default();
            visitor.visit_item(item);
            unnamed_graph.insert(ident.name, visitor.unnameds);
            unnamed_code.insert(ident.name, item_to_string(item));
        }

        if found {
            continue;
        }

        if let Some(ident) = item.kind.ident()
            && ident.name.as_str() == name
            && (kind == "type")
                == matches!(
                    item.kind,
                    ItemKind::TyAlias(_) | ItemKind::Struct(..) | ItemKind::Union(..)
                )
        {
            println!("{}", item_to_string(item));

            let mut visitor = UnnamedVisitor::default();
            visitor.visit_item(item);
            unnameds = visitor.unnameds;

            found = true;
        }
    }

    if !found {
        panic!("{kind} {name} not found in {file:?}")
    }

    if !unnameds.is_empty() {
        let closure = utils::graph::reflexive_transitive_closure(&unnamed_graph);
        let all: FxHashSet<_> = unnameds.iter().flat_map(|s| &closure[s]).collect();
        for symbol in all {
            println!("{}", unnamed_code[symbol]);
        }
    }
}

#[derive(Default)]
struct UnnamedVisitor {
    unnameds: FxHashSet<Symbol>,
}

impl<'a> Visitor<'a> for UnnamedVisitor {
    fn visit_ty(&mut self, ty: &'a rustc_ast::Ty) -> Self::Result {
        if let TyKind::Path(_, path) = &ty.kind {
            let name = path.segments.last().unwrap().ident.name;
            if name.as_str().starts_with("C2RustUnnamed") {
                self.unnameds.insert(name);
            }
        }
    }
}
