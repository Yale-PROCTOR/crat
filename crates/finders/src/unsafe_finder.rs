use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use utils::unsafety::{self, UnsafeOpKind};

struct UnsafetyHandler;

impl unsafety::UnsafetyHandler for UnsafetyHandler {
    fn handle_unsafety(&mut self, kind: UnsafeOpKind, _: Span, tcx: TyCtxt<'_>) {
        if let UnsafeOpKind::CallToUnsafeFunction(Some(def_id)) = kind {
            if let Some(def_id) = def_id.as_local()
                && let rustc_hir::Node::Item(item) = tcx.hir_node_by_def_id(def_id)
                && matches!(item.kind, rustc_hir::ItemKind::Fn { .. })
            {
            } else {
                println!("{}", utils::ir::def_id_to_symbol(def_id, tcx).unwrap());
            }
        } else {
            println!("{kind:?}");
        }
    }
}

pub fn find_unsafe(tcx: TyCtxt<'_>) {
    for item_id in tcx.hir_free_items() {
        let def_id = item_id.owner_id.def_id;
        let item = tcx.hir_item(item_id);
        if !matches!(
            item.kind,
            rustc_hir::ItemKind::Fn { .. } | rustc_hir::ItemKind::Static(_, _, _, _)
        ) {
            continue;
        }
        unsafety::check_unsafety(def_id, &mut UnsafetyHandler, tcx);
    }
}
