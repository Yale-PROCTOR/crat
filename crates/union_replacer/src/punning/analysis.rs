use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{Body, StatementKind},
    ty::TyCtxt,
};

#[derive(Debug, Clone)]
pub struct AnalysisResult {}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResult {
    for def_id in tcx.hir_body_owners() {
        if tcx.def_kind(def_id) != DefKind::Fn {
            continue;
        }
        println!("{def_id:?}");
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();
        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            println!("{bb:?}");
            for stmt in &bbd.statements {
                if matches!(stmt.kind, StatementKind::Assign(_)) {
                    println!("{stmt:?}");
                }
            }
            println!("{:?}", bbd.terminator().kind);
        }
    }

    AnalysisResult {}
}
