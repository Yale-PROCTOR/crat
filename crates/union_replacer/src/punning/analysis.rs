use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Local, ProjectionElem, Rvalue, Statement, StatementKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};

#[derive(Debug, Clone)]
pub struct AnalysisResult {}
enum UnionUseKind<'a> {
    InitUnion(TyKind<'a>, ProjectionElem<Local, Ty<'a>>),
    WriteField(TyKind<'a>, ProjectionElem<Local, Ty<'a>>),
    ReadField(TyKind<'a>, ProjectionElem<Local, Ty<'a>>),
}

struct UnionUseInfo<'a> {
    kind: UnionUseKind<'a>,
    basic_block: BasicBlock,
    statement: Statement<'a>,
}

impl<'a> std::fmt::Debug for UnionUseKind<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnionUseKind::InitUnion(ty, proj) => write!(f, "InitUnion({:?}, {:?})", ty, proj),
            UnionUseKind::WriteField(ty, proj) => write!(f, "WriteField({:?}, {:?})", ty, proj),
            UnionUseKind::ReadField(ty, proj) => write!(f, "ReadField({:?}, {:?})", ty, proj),
        }
    }
}

impl<'a> std::fmt::Debug for UnionUseInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "UnionUseInfo {{ kind: {:?}, basic_block: {:?}, statement: {:?} }}",
            self.kind, self.basic_block, self.statement
        )
    }
}

fn collect_union_uses<'a>(
    mut union_related: Vec<UnionUseInfo<'a>>,
    tcx: TyCtxt<'a>,
) -> Vec<UnionUseInfo<'a>> {
    for def_id in tcx.hir_body_owners() {
        if tcx.def_kind(def_id) != DefKind::Fn {
            continue;
        }
        // println!("DEF: {def_id:?}");
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();
        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            // println!("BB: {bb:?}");
            for stmt in &bbd.statements {
                if let StatementKind::Assign(box (place, value)) = &stmt.kind {
                    // println!("STMT: {:?}", stmt);
                    // Initialize a Union Field
                    if place.ty(body, tcx).ty.is_union() {
                        if let Rvalue::Aggregate(box aggregate_kind, index_vec) = value {
                            if let AggregateKind::Adt(_, _, _, _, Some(field_idx)) = aggregate_kind
                            {
                                let op_type = index_vec.iter().next().unwrap().ty(body, tcx);
                                let project_elem = ProjectionElem::Field(*field_idx, op_type);
                                // Safe to unwrap as index_vec must have only one element
                                assert_eq!(
                                    op_type,
                                    place.project_deeper(&[project_elem], tcx).ty(body, tcx).ty
                                );

                                union_related.push(UnionUseInfo {
                                    kind: UnionUseKind::InitUnion(
                                        place.ty(body, tcx).ty.kind().clone(),
                                        project_elem,
                                    ),
                                    basic_block: bb,
                                    statement: stmt.clone(),
                                });
                            }
                        }
                    } else {
                        // Write to a Union Field (Some projection iteration of Lvalue is a Union)
                        for (place_ref, project_elem) in place.iter_projections() {
                            if place_ref.ty(body, tcx).ty.is_union() {
                                union_related.push(UnionUseInfo {
                                    kind: UnionUseKind::WriteField(
                                        place_ref.ty(body, tcx).ty.kind().clone(),
                                        project_elem.clone(),
                                    ),
                                    basic_block: bb,
                                    statement: stmt.clone(),
                                });
                            }
                        }
                        // Read from a Union Field (Rvalue is a Rvalue::Use of an union field)
                        if let Rvalue::Use(operand) = value {
                            if let Some(rplace) = operand.place() {
                                for (rplace_ref, project_elem) in rplace.iter_projections() {
                                    if rplace_ref.ty(body, tcx).ty.is_union() {
                                        union_related.push(UnionUseInfo {
                                            kind: UnionUseKind::ReadField(
                                                rplace_ref.ty(body, tcx).ty.kind().clone(),
                                                project_elem.clone(),
                                            ),
                                            basic_block: bb,
                                            statement: stmt.clone(),
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // println!("TERM: {:?}", bbd.terminator().kind);
        }
    }
    union_related
}

fn print_union_uses<'a>(union_related: &Vec<UnionUseInfo<'a>>) {
    for use_info in union_related {
        println!("UNION USE: {:?}", use_info);
    }
}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResult {
    let mut union_related = Vec::new();
    union_related = collect_union_uses(union_related, tcx);

    print_union_uses(&union_related);
    AnalysisResult {}
}
