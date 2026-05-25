use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, def_id::DefId};
use utils::unsafety::{self, UnsafeOpKind};

struct UnsafetyHandler(bool);

fn unsafe_call_label(def_id: DefId, tcx: TyCtxt<'_>) -> String {
    let name = utils::ir::def_id_to_symbol(def_id, tcx).unwrap();
    if name.as_str() == "from_raw" && tcx.def_path_str(def_id).contains("boxed") {
        "Box::from_raw".to_string()
    } else {
        name.to_string()
    }
}

impl unsafety::UnsafetyHandler for UnsafetyHandler {
    fn handle_unsafety(&mut self, kind: UnsafeOpKind, span: Span, tcx: TyCtxt<'_>) {
        if let UnsafeOpKind::CallToUnsafeFunction(Some(def_id)) = kind {
            if let Some(def_id) = def_id.as_local()
                && let rustc_hir::Node::Item(item) = tcx.hir_node_by_def_id(def_id)
                && matches!(item.kind, rustc_hir::ItemKind::Fn { .. })
            {
            } else if self.0 {
                println!("{} {span:?}", unsafe_call_label(def_id, tcx));
            } else {
                println!("{}", unsafe_call_label(def_id, tcx));
            }
        } else if self.0 {
            println!("{kind:?} {span:?}");
        } else {
            println!("{kind:?}");
        }
    }
}

pub fn find_unsafe(show_spans: bool, tcx: TyCtxt<'_>) {
    for item_id in tcx.hir_free_items() {
        let def_id = item_id.owner_id.def_id;
        let item = tcx.hir_item(item_id);
        if !matches!(
            item.kind,
            rustc_hir::ItemKind::Fn { .. } | rustc_hir::ItemKind::Static(_, _, _, _)
        ) {
            continue;
        }
        unsafety::check_unsafety(def_id, &mut UnsafetyHandler(show_spans), tcx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct LabelCollector(Vec<String>);

    impl unsafety::UnsafetyHandler for LabelCollector {
        fn handle_unsafety(&mut self, kind: UnsafeOpKind, _span: Span, tcx: TyCtxt<'_>) {
            if let UnsafeOpKind::CallToUnsafeFunction(Some(def_id)) = kind {
                self.0.push(unsafe_call_label(def_id, tcx));
            }
        }
    }

    #[test]
    fn labels_box_from_raw_explicitly() {
        let labels = utils::compilation::run_compiler_on_str(
            r#"
pub unsafe fn free_boxed(p: *mut i32) {
    drop(Box::from_raw(p));
}
"#,
            |tcx| {
                let mut labels = Vec::new();
                for item_id in tcx.hir_free_items() {
                    let def_id = item_id.owner_id.def_id;
                    let item = tcx.hir_item(item_id);
                    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
                        continue;
                    }
                    let mut collector = LabelCollector(Vec::new());
                    unsafety::check_unsafety(def_id, &mut collector, tcx);
                    labels.extend(collector.0);
                }
                labels
            },
        )
        .unwrap();

        assert!(labels.iter().any(|label| label == "Box::from_raw"));
        assert!(!labels.iter().any(|label| label == "from_raw"));
    }
}
