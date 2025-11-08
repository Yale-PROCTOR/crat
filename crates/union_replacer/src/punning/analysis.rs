use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BasicBlocks, Body, Local, Place, ProjectionElem, Rvalue,
        StatementKind, traversal::Preorder,
    },
    ty::{Ty, TyCtxt, TypingEnv},
};
use rustc_span::def_id::LocalDefId;

#[derive(Debug, Clone)]
pub struct AnalysisResult {}

#[derive(Clone, PartialEq, Eq, Hash)]
/// Union Place, Union Type, Field Projection
// ### TODO: Remove Ty from this enum (as it is only for debug logging)
enum UnionUseKind<'a> {
    InitUnion(Place<'a>, Ty<'a>, ProjectionElem<Local, Ty<'a>>),
    WriteField(Place<'a>, Ty<'a>, ProjectionElem<Local, Ty<'a>>),
    ReadField(Place<'a>, Ty<'a>, ProjectionElem<Local, Ty<'a>>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// All useinfo related operations are considered only within the same function(def id) for now.
struct UnionUseInfo<'a> {
    kind: UnionUseKind<'a>,
    basic_block: BasicBlock,
    stmt_idx: usize,
    // statement: Statement<'a>,
}

impl<'a> std::fmt::Debug for UnionUseKind<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnionUseKind::InitUnion(place, ty, proj) => {
                write!(f, "InitUnion({place:?}, {ty:?}, {proj:?})")
            }
            UnionUseKind::WriteField(place, ty, proj) => {
                write!(f, "WriteField({place:?}, {ty:?}, {proj:?})")
            }
            UnionUseKind::ReadField(place, ty, proj) => {
                write!(f, "ReadField({place:?}, {ty:?}, {proj:?})")
            }
        }
    }
}

impl<'a> std::fmt::Debug for UnionUseInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // write!(
        //     f,
        //     "UnionUseInfo: kind: {:?}, location: {:?}-{:?}, statement: {:?}",
        //     self.kind, self.basic_block, self.stmt_idx, self.statement
        // )
        write!(
            f,
            "{:?} at {:?}-{:?}",
            self.kind, self.basic_block, self.stmt_idx
        )
    }
}

fn collect_union_uses_map<'a>(tcx: TyCtxt<'a>) -> HashMap<LocalDefId, HashSet<UnionUseInfo<'a>>> {
    let mut union_uses_map: HashMap<LocalDefId, HashSet<UnionUseInfo<'a>>> = HashMap::new();
    for def_id in tcx.hir_body_owners() {
        if let Some(uses) = collect_union_uses(def_id, tcx) {
            union_uses_map.insert(def_id, uses);
        }
    }
    union_uses_map
}

fn collect_union_uses<'a>(
    def_id: LocalDefId,
    tcx: TyCtxt<'a>,
) -> Option<HashSet<UnionUseInfo<'a>>> {
    let mut union_uses = HashSet::new();
    if tcx.def_kind(def_id) != DefKind::Fn {
        return None;
    }
    println!("DEF: {def_id:?}");
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body: &Body<'_> = &body.borrow();
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        println!("\tBB: {bb:?}");
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, value)) = &stmt.kind {
                println!("\t\tSTMT: {stmt:?}");
                // Initialize a Union Field
                if place.ty(body, tcx).ty.is_union() {
                    if let Rvalue::Aggregate(
                        box AggregateKind::Adt(_, _, _, _, Some(field_idx)),
                        index_vec,
                    ) = value
                    {
                        let op_type = index_vec.iter().next().unwrap().ty(body, tcx);
                        let project_elem = ProjectionElem::Field(*field_idx, op_type);
                        // Safe to unwrap as index_vec must have only one element
                        assert_eq!(
                            op_type,
                            place.project_deeper(&[project_elem], tcx).ty(body, tcx).ty
                        );
                        let ty = place.ty(body, tcx).ty;
                        union_uses.insert(UnionUseInfo {
                            // kind: UnionUseKind::InitUnion(place.ty(body, tcx).ty, project_elem),
                            kind: UnionUseKind::InitUnion(*place, ty, project_elem),
                            basic_block: bb,
                            stmt_idx,
                            // statement: stmt.clone(),
                        });
                    }
                } else {
                    // ### Ignore nested union accesses for both reads and writes for now
                    // Write to a Union Field (Some projection iteration of Lvalue is a Union)
                    for (place_ref, project_elem) in place.iter_projections() {
                        if place_ref.ty(body, tcx).ty.is_union() {
                            union_uses.insert(UnionUseInfo {
                                kind: UnionUseKind::WriteField(
                                    // place_ref.ty(body, tcx).ty,
                                    place_ref.to_place(tcx),
                                    place_ref.ty(body, tcx).ty,
                                    project_elem,
                                ),
                                basic_block: bb,
                                stmt_idx,
                                // statement: stmt.clone(),
                            });
                        }
                    }
                    // Read from a Union Field (Rvalue is a Rvalue::Use of an union field)
                    if let Rvalue::Use(operand) = value
                        && let Some(rplace) = operand.place()
                    {
                        for (rplace_ref, project_elem) in rplace.iter_projections() {
                            if rplace_ref.ty(body, tcx).ty.is_union() {
                                union_uses.insert(UnionUseInfo {
                                    kind: UnionUseKind::ReadField(
                                        // rplace_ref.ty(body, tcx).ty,
                                        rplace_ref.to_place(tcx),
                                        rplace_ref.ty(body, tcx).ty,
                                        project_elem,
                                    ),
                                    basic_block: bb,
                                    stmt_idx,
                                    // statement: stmt.clone(),
                                });
                            }
                        }
                    }
                }
            }
        }
        println!("\t\tTERM: {:?}", bbd.terminator().kind);
    }
    if union_uses.is_empty() {
        None
    } else {
        Some(union_uses)
    }
}

fn print_union_uses_map<'a>(union_uses: &HashMap<LocalDefId, HashSet<UnionUseInfo<'a>>>) {
    for (def_id, uses) in union_uses {
        println!("Union Uses for {def_id:?}:");
        for use_info in uses {
            println!("\t{use_info:?}");
        }
    }
}

impl<'a> UnionUseInfo<'a> {
    /// Return if Use1 dominates Use2
    /// - Ignore unreachable basic blocks for now
    fn dominates(use1: &UnionUseInfo, use2: &UnionUseInfo, basic_blocks: &BasicBlocks) -> bool {
        if use1.basic_block == use2.basic_block {
            use1.stmt_idx <= use2.stmt_idx
        } else {
            basic_blocks
                .dominators()
                .dominates(use1.basic_block, use2.basic_block)
        }
    }

    /// Find dominatees of self (except self)
    fn extract_dominated(
        &self,
        union_uses: &HashSet<UnionUseInfo<'a>>,
        basic_blocks: &BasicBlocks,
    ) -> HashSet<UnionUseInfo<'a>> {
        union_uses
            .clone()
            .into_iter()
            .filter(|u| *u != *self && UnionUseInfo::dominates(self, u, basic_blocks))
            .collect()
    }
}

fn collect_relations<'a>(
    union_uses: &HashSet<UnionUseInfo<'a>>,
    basic_blocks: &BasicBlocks,
) -> HashSet<(UnionUseInfo<'a>, UnionUseInfo<'a>)> {
    let mut relations = HashSet::new();
    for use1 in union_uses {
        let dominated = use1.extract_dominated(union_uses, basic_blocks);
        for use2 in dominated {
            relations.insert((use1.clone(), use2));
        }
    }
    relations
}

impl<'a> UnionUseInfo<'a> {
    /// Return if Use2 is reachable from Use1
    fn reachable(use1: &UnionUseInfo, use2: &UnionUseInfo, body: &Body<'a>) -> bool {
        if use1.basic_block == use2.basic_block {
            use1.stmt_idx <= use2.stmt_idx
        } else {
            let preorder = Preorder::new(body, use1.basic_block);
            preorder.into_iter().any(|(bb, _)| bb == use2.basic_block)
        }
    }

    fn is_between_dominance(
        &self,
        dominator: &UnionUseInfo,
        dominatee: &UnionUseInfo,
        body: &Body<'a>,
    ) -> Option<bool> {
        if !UnionUseInfo::dominates(dominator, dominatee, &body.basic_blocks) {
            None
        } else {
            Some(
                UnionUseInfo::reachable(dominator, self, body)
                    && UnionUseInfo::reachable(self, dominatee, body),
            )
        }
    }
}

// fn print_dominance_relations<'a>(
//     union_uses: &HashSet<UnionUseInfo<'a>>,
//     body: &Body<'a>,
// ) {
//     let basic_blocks = &body.basic_blocks;
//     let relations = collect_relations(union_uses, basic_blocks);
//     for (use1, use2) in relations {
//         println!("\t{use1:?}\n\t--> {use2:?}\n");
//     }
// }

impl<'a> UnionUseKind<'a> {
    fn is_punning(
        write_use: &UnionUseKind<'a>,
        read_use: &UnionUseKind<'a>,
        def_id: LocalDefId,
        tcx: TyCtxt<'a>,
    ) -> (bool, u64) {
        match read_use {
            UnionUseKind::ReadField(u1, tu, proj1) => match write_use {
                UnionUseKind::WriteField(u2, _, proj2) | UnionUseKind::InitUnion(u2, _, proj2) => {
                    if u1 != u2 || proj1 == proj2 {
                        (false, 0)
                    } else {
                        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
                        let body: &Body<'_> = &body.borrow();
                        let typing_env = TypingEnv::post_analysis(tcx, def_id);
                        let t1 = u1.project_deeper(&[*proj1], tcx).ty(body, tcx).ty;
                        let t2 = u2.project_deeper(&[*proj2], tcx).ty(body, tcx).ty;

                        let is_sized1 = t1.is_sized(tcx, typing_env);
                        let is_sized2 = t2.is_sized(tcx, typing_env);
                        let is_sized_u = tu.is_sized(tcx, typing_env);
                        if !is_sized1 || !is_sized2 || !is_sized_u {
                            return (false, 0);
                        }

                        let layout1 = tcx.layout_of(typing_env.as_query_input(t1)).unwrap();
                        let layout2 = tcx.layout_of(typing_env.as_query_input(t2)).unwrap();
                        let layout_u = tcx.layout_of(typing_env.as_query_input(*tu)).unwrap();

                        (
                            layout1.size.bytes() == layout2.size.bytes()
                                && layout1.size.bytes() == layout_u.size.bytes(),
                            layout1.size.bytes(),
                        )
                    }
                }
                _ => (false, 0),
            },
            _ => (false, 0),
        }
    }
}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResult {
    let union_uses_map = collect_union_uses_map(tcx);
    println!();
    print_union_uses_map(&union_uses_map);
    println!();

    for (def_id, union_uses) in &union_uses_map {
        println!("Dominance Relations for {def_id:?}");
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();

        let relations = collect_relations(union_uses, &body.basic_blocks);
        for (use1, use2) in relations {
            let between_uses: HashSet<_> = union_uses
                .iter()
                .filter(|u| {
                    **u != use1
                        && **u != use2
                        && u.is_between_dominance(&use1, &use2, body).unwrap()
                })
                .collect();
            println!("\t{use1:?}");
            for between_use in between_uses {
                println!("\t|-- {between_use:?}");
            }
            println!("\t|-> {use2:?}");
            let (is_punning, size) = UnionUseKind::is_punning(&use1.kind, &use2.kind, *def_id, tcx);
            let s = if is_punning {
                format!("Punning of {size} bytes")
            } else {
                "No Punning".to_string()
            };
            println!("\t{s}");
            println!();
        }
    }
    AnalysisResult {}
}
