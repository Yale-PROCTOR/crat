use rustc_middle::{mir::StatementKind, ty::TyCtxt};

pub fn run(tcx: TyCtxt<'_>) {
    for def_id in tcx.hir_body_owners() {
        println!("{}", tcx.def_path_str(def_id));
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        for bb in body.basic_blocks.reverse_postorder() {
            println!(" {bb:?}");
            let bbd = &body[*bb];
            for stmt in &bbd.statements {
                if matches!(stmt.kind, StatementKind::Assign(_)) {
                    println!("  {stmt:?} ({:?})", stmt.source_info.span);
                }
            }
            let term = bbd.terminator();
            println!("  {:?} ({:?})", term.kind, term.source_info.span);
        }
    }
}
