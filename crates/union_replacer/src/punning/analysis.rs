use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlocks, Body, Local, Location, Place, ProjectionElem, Rvalue,
        StatementKind, traversal::Preorder,
    },
    ty::{Ty, TyCtxt, TypingEnv},
};
use rustc_span::def_id::LocalDefId;

pub struct AnalysisResult<'a> {
    pub punning_map: FxHashMap<LocalDefId, FxHashMap<Place<'a>, PunningInfo<'a>>>,
}

impl<'a> std::fmt::Debug for AnalysisResult<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut nowrite = false;
        for (def_id, punning_infos) in &self.punning_map {
            if punning_infos.is_empty() {
                continue;
            } else {
                nowrite = true;
                writeln!(f, "At Function {def_id:?}:")?;
                for (place, info) in punning_infos {
                    writeln!(f, "For Place {place:?}, {info:?}")?;
                }
            }
        }
        if !nowrite {
            write!(f, "No Punnings")?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct PunningInfo<'a> {
    size: u64,
    replacable_uses: FxHashSet<UnionUseInfo<'a>>,
}

impl<'a> std::fmt::Debug for PunningInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let use_str = self
            .replacable_uses
            .iter()
            .map(|u| format!("\t{u:?}\n"))
            .collect::<Vec<String>>()
            .join("");

        write!(
            f,
            "Punning of {} bytes, Replacable uses:\n{}",
            self.size, use_str
        )
    }
}

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
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// All useinfo related operations are considered only within the same function(def id) for now.
struct UnionUseInfo<'a> {
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

fn collect_union_uses_map<'a>(tcx: TyCtxt<'a>) -> FxHashMap<LocalDefId, Vec<UnionUseInfo<'a>>> {
    let mut union_uses_map: FxHashMap<LocalDefId, Vec<UnionUseInfo<'a>>> = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        if let Some(uses) = collect_union_uses(def_id, tcx) {
            union_uses_map.insert(def_id, uses);
        }
    }
    union_uses_map
}

fn collect_union_uses<'a>(def_id: LocalDefId, tcx: TyCtxt<'a>) -> Option<Vec<UnionUseInfo<'a>>> {
    let mut union_uses = Vec::new();
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
                        union_uses.push(UnionUseInfo {
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
                            union_uses.push(UnionUseInfo {
                                kind: UnionUseKind::WriteField(
                                    place_ref.to_place(tcx),
                                    place_ref.ty(body, tcx).ty,
                                    project_elem,
                                ),
                                location: Location {
                                    block: bb,
                                    statement_index: stmt_idx,
                                },
                            });
                        }
                    }
                    // Read from a Union Field (Rvalue is a Rvalue::Use of an union field)
                    if let Rvalue::Use(operand) = value
                        && let Some(rplace) = operand.place()
                    {
                        for (rplace_ref, project_elem) in rplace.iter_projections() {
                            if rplace_ref.ty(body, tcx).ty.is_union() {
                                union_uses.push(UnionUseInfo {
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

fn print_union_uses_map<'a>(union_uses: &FxHashMap<LocalDefId, Vec<UnionUseInfo<'a>>>) {
    for (def_id, uses) in union_uses {
        println!("Union Uses for {def_id:?}:");
        for use_info in uses {
            println!("\t{use_info:?}");
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

fn collect_relations<'a>(
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

impl<'a> UnionUseInfo<'a> {
    /// Return if Use2 is reachable from Use1
    fn reachable(use1: &UnionUseInfo, use2: &UnionUseInfo, body: &Body<'a>) -> bool {
        if use1.location.block == use2.location.block {
            use1.location.statement_index <= use2.location.statement_index
        } else {
            let preorder = Preorder::new(body, use1.location.block);
            preorder
                .into_iter()
                .any(|(bb, _)| bb == use2.location.block)
        }
    }

    fn is_between_dominance(
        &self,
        dominator: &UnionUseInfo,
        dominatee: &UnionUseInfo,
        body: &Body<'a>,
    ) -> Option<bool> {
        if !dominator
            .location
            .dominates(dominatee.location, body.basic_blocks.dominators())
        {
            None
        } else {
            Some(
                UnionUseInfo::reachable(dominator, self, body)
                    && UnionUseInfo::reachable(self, dominatee, body),
            )
        }
    }
}

impl<'a> UnionUseKind<'a> {
    fn is_replacable_punning(
        write_use: &UnionUseKind<'a>,
        read_use: &UnionUseKind<'a>,
        between_set: &Vec<&UnionUseInfo<'a>>,
        def_id: LocalDefId,
        tcx: TyCtxt<'a>,
    ) -> Option<u64> {
        match read_use {
            UnionUseKind::ReadField(u1, tu, proj1) => match write_use {
                UnionUseKind::WriteField(u2, _, proj2) | UnionUseKind::InitUnion(u2, _, proj2) => {
                    // Punning check by pattern matching and projection comparison
                    if u1 != u2
                        || (proj1 == proj2
                            && between_set.iter().all(|u| match u.kind {
                                UnionUseKind::InitUnion(_, _, p)
                                | UnionUseKind::WriteField(_, _, p)
                                | UnionUseKind::ReadField(_, _, p) => p == *proj2,
                            }))
                    {
                        None
                    } else {
                        // Replacable check here
                        // TODO: Check if to/from_bytes are implemented
                        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
                        let body: &Body<'_> = &body.borrow();
                        let typing_env = TypingEnv::post_analysis(tcx, def_id);
                        let t1 = u1.project_deeper(&[*proj1], tcx).ty(body, tcx).ty;
                        let t2 = u2.project_deeper(&[*proj2], tcx).ty(body, tcx).ty;

                        let is_sized1 = t1.is_sized(tcx, typing_env);
                        let is_sized2 = t2.is_sized(tcx, typing_env);
                        let is_sized_u = tu.is_sized(tcx, typing_env);
                        if !is_sized1 || !is_sized2 || !is_sized_u {
                            return None;
                        }

                        let layout1 = tcx.layout_of(typing_env.as_query_input(t1)).unwrap();
                        let layout2 = tcx.layout_of(typing_env.as_query_input(t2)).unwrap();
                        let layout_u = tcx.layout_of(typing_env.as_query_input(*tu)).unwrap();

                        if layout1.size.bytes() == layout2.size.bytes()
                            && layout1.size.bytes() == layout_u.size.bytes()
                        {
                            Some(layout1.size.bytes())
                        } else {
                            None
                        }
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }
}

pub fn analyze(tcx: TyCtxt) -> AnalysisResult {
    let union_uses_map = collect_union_uses_map(tcx);
    println!();
    print_union_uses_map(&union_uses_map);
    println!();
    let mut result_map = FxHashMap::default();

    for (def_id, union_uses) in union_uses_map {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();

        let relations = collect_relations(&union_uses, &body.basic_blocks);
        let punning_relations = relations
            .into_iter()
            .filter_map(|(dominator, dominatee)| {
                // Assume write dominates read and this relation is punning and replacable
                // Collect (read, punning_size, (write, between_set))
                let between_set: Vec<_> = union_uses
                    .iter()
                    .filter(|u| {
                        u.kind.place() == dominator.kind.place()
                            && **u != dominator
                            && **u != dominatee
                            && u.is_between_dominance(&dominator, &dominatee, body)
                                .unwrap()
                    })
                    .collect();
                let punning = UnionUseKind::is_replacable_punning(
                    &dominator.kind,
                    &dominatee.kind,
                    &between_set,
                    def_id,
                    tcx,
                );
                punning.map(|psize| (dominatee, psize, (dominator, between_set)))
            })
            .fold(
                FxHashMap::default(),
                |mut acc, (r, psize, (w, between_set))| {
                    // Merge punning relations (find maximum dominating write)
                    if let UnionUseKind::InitUnion(_, _, _) = w.kind {
                        if between_set.len() + 2 == union_uses.len() {
                            acc.insert(r, (psize, w, between_set));
                            acc
                        } else {
                            acc
                        }
                    } else {
                        let (_, max_w, max_between_set) =
                            acc.entry(r)
                                .or_insert((psize, w.clone(), between_set.clone()));
                        if *max_w == w || max_between_set.contains(&&w) {
                            acc
                        } else if between_set.contains(&&max_w.clone()) {
                            *max_w = w;
                            *max_between_set = between_set;
                            acc
                        } else {
                            // Multiple dominators always form a chain
                            unreachable!("Merge failed!")
                        }
                    }
                },
            );

        // For each place, union all replacable uses
        // TODO: This drops maximum dominating write information for now -> Fix later if needed
        let punning_infos: FxHashMap<Place<'_>, PunningInfo<'_>> = punning_relations
            .into_iter()
            .map(|(r, (psize, w, between_set))| {
                let place = *r.kind.place();
                let info = PunningInfo {
                    size: psize,
                    replacable_uses: {
                        let mut set = FxHashSet::default();
                        set.insert(r);
                        set.insert(w);
                        for u in between_set {
                            set.insert(u.clone());
                        }
                        set
                    },
                };
                (place, info)
            })
            .fold(FxHashMap::default(), |mut acc, (place, info)| {
                match acc.get(&place) {
                    Some(pre_info) => {
                        if pre_info.size == info.size {
                            acc.insert(
                                place,
                                PunningInfo {
                                    size: info.size,
                                    replacable_uses: pre_info
                                        .replacable_uses
                                        .union(&info.replacable_uses)
                                        .cloned()
                                        .collect(),
                                },
                            );
                            acc
                        } else {
                            panic!("Merge failed")
                        }
                    }
                    None => {
                        acc.insert(place, info);
                        acc
                    }
                }
            });

        result_map.insert(def_id, punning_infos);
    }
    AnalysisResult {
        punning_map: result_map,
    }
}
