use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlocks, Body, Local, Location, Place, ProjectionElem, Rvalue,
        StatementKind,
    },
    ty::{Ty, TyCtxt},
};
use rustc_span::def_id::LocalDefId;

pub struct AnalysisResult<'a> {
    pub map: FxHashMap<
        LocalDefId,
        FxHashMap<Place<'a>, FxHashMap<UnionUseInfo<'a>, (bool, Vec<UnionUseInfo<'a>>)>>,
    >,
}

impl<'a> std::fmt::Debug for AnalysisResult<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut nowrite = false;
        for (def_id, place_to_rw) in &self.map {
            if place_to_rw.is_empty() {
                continue;
            } else {
                nowrite = true;
                writeln!(f, "At Function {def_id:?}:")?;
                for (place, rw) in place_to_rw {
                    writeln!(f, "\tFor Place {place:?}")?;
                    for (read_use, (is_replacable, write_uses)) in rw {
                        writeln!(f, "\t\tRead Use: {read_use:?}, Replacable: {is_replacable}",)?;
                        for write_use in write_uses {
                            writeln!(f, "\t\t\tFrom Write Use: {write_use:?}")?;
                        }
                    }
                }
            }
        }
        if !nowrite {
            write!(f, "No reads")?;
        }
        Ok(())
    }
}

// #[derive(Clone, PartialEq, Eq)]
// pub struct PunningInfo<'a> {
//     size: u64,
//     replacable_uses: FxHashSet<UnionUseInfo<'a>>,
// }

// impl<'a> std::fmt::Debug for PunningInfo<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let use_str = self
//             .replacable_uses
//             .iter()
//             .map(|u| format!("\t{u:?}\n"))
//             .collect::<Vec<String>>()
//             .join("");

//         write!(
//             f,
//             "Punning of {} bytes, Replacable uses:\n{}",
//             self.size, use_str
//         )
//     }
// }

#[derive(Clone, PartialEq, Eq, Hash)]
/// Union Place, Union Type, Field Projection
enum UnionUseKind<'a> {
    InitUnion(Place<'a>, Ty<'a>, ProjectionElem<Local, Ty<'a>>),
    WriteField(Place<'a>, Ty<'a>, ProjectionElem<Local, Ty<'a>>),
    ReadField(Place<'a>, Ty<'a>, ProjectionElem<Local, Ty<'a>>),
}

impl<'a> UnionUseKind<'a> {
    fn place(&self) -> &Place<'a> {
        match self {
            UnionUseKind::InitUnion(place, _, _) => place,
            UnionUseKind::WriteField(place, _, _) => place,
            UnionUseKind::ReadField(place, _, _) => place,
        }
    }

    fn is_write(&self) -> bool {
        match self {
            UnionUseKind::InitUnion(_, _, _) | UnionUseKind::WriteField(_, _, _) => true,
            UnionUseKind::ReadField(_, _, _) => false,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// All useinfo related operations are considered only within the same function(def id) for now.
pub struct UnionUseInfo<'a> {
    kind: UnionUseKind<'a>,
    location: Location,
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
        write!(f, "{:?} at {:?}", self.kind, self.location)
    }
}

/// def_id -> (Place -> [UnionUseInfo])
fn collect_union_uses_map<'a>(
    tcx: TyCtxt<'a>,
) -> FxHashMap<LocalDefId, FxHashMap<Place<'a>, Vec<UnionUseInfo<'a>>>> {
    let mut union_uses_map: FxHashMap<LocalDefId, FxHashMap<Place<'a>, Vec<UnionUseInfo<'a>>>> =
        FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        if let Some(uses) = collect_union_uses(def_id, tcx) {
            union_uses_map.insert(def_id, uses);
        }
    }
    // union_uses_map
    todo!()
}

/// Place -> [UnionUseInfo] for each def_id (function)
fn collect_union_uses<'a>(
    def_id: LocalDefId,
    tcx: TyCtxt<'a>,
) -> Option<FxHashMap<Place<'a>, Vec<UnionUseInfo<'a>>>> {
    let mut union_uses: FxHashMap<Place<'a>, Vec<UnionUseInfo<'a>>> = FxHashMap::default();
    if tcx.def_kind(def_id) != DefKind::Fn {
        return None;
    }
    // println!("DEF: {def_id:?}");
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body: &Body<'_> = &body.borrow();
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        // println!("\tBB: {bb:?}");
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, value)) = &stmt.kind {
                // println!("\t\tSTMT: {stmt:?}");
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
                        union_uses.entry(*place).or_default().push(UnionUseInfo {
                            kind: UnionUseKind::InitUnion(*place, ty, project_elem),
                            location: Location {
                                block: bb,
                                statement_index: stmt_idx,
                            },
                        });
                    }
                } else {
                    // Ignore nested union accesses for both reads and writes for now
                    // Write to a Union Field (Some projection iteration of Lvalue is a Union)
                    for (place_ref, project_elem) in place.iter_projections() {
                        if place_ref.ty(body, tcx).ty.is_union() {
                            union_uses.entry(place_ref.to_place(tcx)).or_default().push(
                                UnionUseInfo {
                                    kind: UnionUseKind::WriteField(
                                        place_ref.to_place(tcx),
                                        place_ref.ty(body, tcx).ty,
                                        project_elem,
                                    ),
                                    location: Location {
                                        block: bb,
                                        statement_index: stmt_idx,
                                    },
                                },
                            );
                        }
                    }
                    // Read from a Union Field (Rvalue is a Rvalue::Use of an union field)
                    if let Rvalue::Use(operand) = value
                        && let Some(rplace) = operand.place()
                    {
                        for (rplace_ref, project_elem) in rplace.iter_projections() {
                            if rplace_ref.ty(body, tcx).ty.is_union() {
                                union_uses
                                    .entry(rplace_ref.to_place(tcx))
                                    .or_default()
                                    .push(UnionUseInfo {
                                        kind: UnionUseKind::ReadField(
                                            rplace_ref.to_place(tcx),
                                            rplace_ref.ty(body, tcx).ty,
                                            project_elem,
                                        ),
                                        location: Location {
                                            block: bb,
                                            statement_index: stmt_idx,
                                        },
                                    });
                            }
                        }
                    }
                }
            }
        }
        // println!("\t\tTERM: {:?}", bbd.terminator().kind);
    }
    if union_uses.is_empty() {
        None
    } else {
        Some(union_uses)
    }
}

fn print_union_uses_map<'a>(
    union_uses: &FxHashMap<LocalDefId, FxHashMap<Place<'a>, Vec<UnionUseInfo<'a>>>>,
) {
    for (def_id, uses) in union_uses {
        println!("Union Uses for {def_id:?}:");
        for (place, use_infos) in uses {
            println!("\tPlace: {place:?}");
            for use_info in use_infos {
                println!("\t\t{use_info:?}");
            }
        }
    }
}

impl<'a> UnionUseInfo<'a> {
    /// Find dominatees of self (except self)
    fn extract_dominated(
        &self,
        union_uses: &[UnionUseInfo<'a>],
        basic_blocks: &BasicBlocks,
    ) -> FxHashSet<UnionUseInfo<'a>> {
        union_uses
            .iter()
            .filter(|&u| {
                *u != *self
                    && self
                        .location
                        .dominates(u.location, basic_blocks.dominators())
            })
            .cloned()
            .collect()
    }
}

/// Assume all union uses are for the same union place
fn collect_dominance_relations<'a>(
    union_uses: &Vec<UnionUseInfo<'a>>,
    basic_blocks: &BasicBlocks,
) -> FxHashSet<(UnionUseInfo<'a>, UnionUseInfo<'a>)> {
    let mut relations = FxHashSet::default();
    for use1 in union_uses {
        let dominated = use1.extract_dominated(union_uses, basic_blocks);
        for use2 in dominated {
            if use1.kind.place() == use2.kind.place() {
                relations.insert((use1.clone(), use2));
            }
        }
    }
    relations
}

/// Assume all union uses are for the same union place
/// Return: Read -> Latest Dominator Write (w dom r)
fn filter_closest_w_dom_r<'a>(
    dominance_relations: FxHashSet<(UnionUseInfo<'a>, UnionUseInfo<'a>)>,
) -> FxHashMap<UnionUseInfo<'a>, UnionUseInfo<'a>> {
    let w_dom_r: Vec<(UnionUseInfo<'a>, UnionUseInfo<'a>)> = dominance_relations
        .clone()
        .into_iter()
        .filter(|(u1, u2)| u1.kind.is_write() && !u2.kind.is_write())
        .collect();

    let mut closest_w_dom_r: FxHashMap<UnionUseInfo<'a>, UnionUseInfo<'a>> = FxHashMap::default();
    for (w_use, r_use) in w_dom_r {
        if let Some(existing_w_use) = closest_w_dom_r.get(&r_use) {
            if dominance_relations.contains(&(existing_w_use.clone(), w_use.clone())) {
                closest_w_dom_r.insert(r_use, w_use);
            }
        } else {
            closest_w_dom_r.insert(r_use, w_use);
        }
    }

    closest_w_dom_r
}

fn collect_readable_writes<'a>(
    w_dom_r: FxHashMap<UnionUseInfo<'a>, UnionUseInfo<'a>>,
    tcx: TyCtxt<'a>,
) -> FxHashSet<(UnionUseInfo<'a>, Vec<UnionUseInfo<'a>>)> {
    todo!()
}

fn is_replacable_read(read_use: &UnionUseInfo, write_use: &Vec<UnionUseInfo>, tcx: TyCtxt) -> bool {
    todo!()
}

// impl<'a> UnionUseInfo<'a> {
//     fn is_between_dominance(
//         &self,
//         dominator: &UnionUseInfo,
//         dominatee: &UnionUseInfo,
//         body: &Body<'a>,
//     ) -> Option<bool> {
//         if !dominator
//             .location
//             .dominates(dominatee.location, body.basic_blocks.dominators())
//         {
//             None
//         } else {
//             Some(
//                 dominator.location.is_predecessor_of(self.location, body)
//                     && self.location.is_predecessor_of(dominatee.location, body),
//             )
//         }
//     }
// }

// impl<'a> UnionUseKind<'a> {
//     fn is_replacable_punning(
//         write_use: &UnionUseKind<'a>,
//         read_use: &UnionUseKind<'a>,
//         between_set: &Vec<&UnionUseInfo<'a>>,
//         def_id: LocalDefId,
//         _tcx: TyCtxt<'a>,
//     ) -> Option<u64> {
//         match read_use {
//             UnionUseKind::ReadField(u1, tu, proj1) => match write_use {
//                 UnionUseKind::WriteField(u2, _, proj2) | UnionUseKind::InitUnion(u2, _, proj2) => {
//                     // Punning check by pattern matching and projection comparison
//                     if u1 != u2
//                         || (proj1 == proj2
//                             && between_set.iter().all(|u| match u.kind {
//                                 UnionUseKind::InitUnion(_, _, p)
//                                 | UnionUseKind::WriteField(_, _, p)
//                                 | UnionUseKind::ReadField(_, _, p) => p == *proj2,
//                             }))
//                     {
//                         None
//                     } else {
//                         // Replacable check here
//                         // TODO: Check if to/from_bytes are implemented
//                         let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
//                         let body: &Body<'_> = &body.borrow();
//                         let typing_env = TypingEnv::post_analysis(tcx, def_id);
//                         let t1 = u1.project_deeper(&[*proj1], tcx).ty(body, tcx).ty;
//                         let t2 = u2.project_deeper(&[*proj2], tcx).ty(body, tcx).ty;

//                         let is_sized1 = t1.is_sized(tcx, typing_env);
//                         let is_sized2 = t2.is_sized(tcx, typing_env);
//                         let is_sized_u = tu.is_sized(tcx, typing_env);
//                         if !is_sized1 || !is_sized2 || !is_sized_u {
//                             return None;
//                         }

//                         let layout1 = tcx.layout_of(typing_env.as_query_input(t1)).unwrap();
//                         let layout2 = tcx.layout_of(typing_env.as_query_input(t2)).unwrap();
//                         let layout_u = tcx.layout_of(typing_env.as_query_input(*tu)).unwrap();

//                         if layout1.size.bytes() == layout2.size.bytes()
//                             && layout1.size.bytes() == layout_u.size.bytes()
//                         {
//                             Some(layout1.size.bytes())
//                         } else {
//                             None
//                         }
//                     }
//                 }
//                 _ => None,
//             },
//             _ => None,
//         }
//     }
// }

pub fn analyze(tcx: TyCtxt) -> AnalysisResult {
    let union_uses_map = collect_union_uses_map(tcx);
    println!();
    print_union_uses_map(&union_uses_map);
    println!();
    let mut result_map = FxHashMap::default();

    for (def_id, union_uses) in union_uses_map {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();

        let mut place_map = FxHashMap::default();

        for (place, uses) in &union_uses {
            println!("For Place {place:?}:");
            let dominance_relations = collect_dominance_relations(uses, &body.basic_blocks);

            // r -> w where w closest dominator write of r
            let w_dom_r = filter_closest_w_dom_r(dominance_relations);

            // r -> [w1, w2, ...] where r can read from w1, w2, ...
            let read_write_map = collect_readable_writes(w_dom_r, tcx);

            let read_write_map = read_write_map
                .into_iter()
                .map(|(read_use, write_uses)| {
                    (
                        read_use.clone(),
                        (is_replacable_read(&read_use, &write_uses, tcx), write_uses),
                    )
                })
                .collect::<FxHashMap<UnionUseInfo, (bool, Vec<UnionUseInfo>)>>();

            place_map.insert(*place, read_write_map);
        }

        result_map.insert(def_id, place_map);
    }
    AnalysisResult { map: result_map }
}
