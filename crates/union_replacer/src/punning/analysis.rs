use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{AggregateKind, Body, Local, Location, Place, ProjectionElem, Rvalue, StatementKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

pub type AnalysisMap<'a> = FxHashMap<
    Place<'a>,
    (
        UnionUseInfo<'a>,
        FxHashMap<UnionUseInfo<'a>, (bool, FxHashSet<UnionUseInfo<'a>>)>,
    ),
>;
pub struct AnalysisResult<'a> {
    pub map: FxHashMap<LocalDefId, AnalysisMap<'a>>,
}

impl<'a> std::fmt::Debug for AnalysisResult<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut nowrite = true;
        for (def_id, place_to_rw) in &self.map {
            if place_to_rw.is_empty() {
                continue;
            } else {
                let mut fb = false;
                for (place, rw) in place_to_rw {
                    let mut pb = false;
                    for (read_use, (is_replacable, write_uses)) in &rw.1 {
                        if write_uses.is_empty() {
                            continue;
                        }
                        if !is_replacable {
                            continue;
                        }
                        if !pb {
                            if !fb {
                                writeln!(f, "At Function {def_id:?}:")?;
                                fb = true;
                                nowrite = false;
                            }
                            writeln!(f, "\tFor Place {place:?}")?;
                            writeln!(f, "\t\t(Init Use: {:?})", rw.0)?;
                            pb = true;
                        }
                        writeln!(f, "\t\tRead Use: {read_use:?}")?;
                        writeln!(f, "\t\tReplacable: {is_replacable}")?;
                        for write_use in write_uses {
                            writeln!(f, "\t\tFrom Write Use: {write_use:?}")?;
                        }
                        writeln!(f)?;
                    }
                }
            }
        }
        if nowrite {
            write!(f, "No Punnings")?;
        }
        Ok(())
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
    #[allow(dead_code)]
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

    fn field_type(&self, body: &Body<'a>, tcx: TyCtxt<'a>) -> Ty<'a> {
        match self {
            UnionUseKind::InitUnion(u, _, proj)
            | UnionUseKind::WriteField(u, _, proj)
            | UnionUseKind::ReadField(u, _, proj) => {
                u.project_deeper(&[*proj], tcx).ty(body, tcx).ty
            }
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
    union_uses_map
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
    println!("DEF: {def_id:?}");
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body: &Body<'_> = &body.borrow();
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        println!("\tBB: {bb:?}");
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            println!("\t\tSTMT {stmt_idx}: {stmt:?}");
            if let StatementKind::Assign(box (place, value)) = &stmt.kind {
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
        println!("\t\tTERM: {:?}", bbd.terminator().kind);
    }
    if union_uses.is_empty() {
        None
    } else {
        Some(union_uses)
    }
}

fn _print_union_uses_map<'a>(
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

fn pred_locations<'a>(loc: Location, body: &Body<'a>) -> Vec<Location> {
    if loc.statement_index > 0 {
        return vec![Location {
            block: loc.block,
            statement_index: loc.statement_index - 1,
        }];
    }

    body.basic_blocks.predecessors()[loc.block]
        .iter()
        .map(|&pred_bb| body.terminator_loc(pred_bb))
        .collect()
}

fn collect_readable_writes<'a>(
    uses: &[UnionUseInfo<'a>],
    body: &Body<'a>,
) -> FxHashMap<UnionUseInfo<'a>, FxHashSet<UnionUseInfo<'a>>> {
    // loc -> write use if it is a write
    let mut loc_to_write: FxHashMap<Location, &UnionUseInfo<'a>> = FxHashMap::default();
    for u in uses {
        if u.kind.is_write() {
            loc_to_write.insert(u.location, u);
        }
    }

    let mut result: FxHashMap<UnionUseInfo<'a>, FxHashSet<UnionUseInfo<'a>>> = FxHashMap::default();

    let read_uses = uses
        .iter()
        .filter(|u| !u.kind.is_write())
        .cloned()
        .collect::<Vec<_>>();

    for read_use in read_uses {
        let mut reachable_writes: FxHashSet<UnionUseInfo<'a>> = FxHashSet::default();
        let mut stack: Vec<Location> = Vec::new();
        let mut visited: FxHashSet<Location> = FxHashSet::default();

        stack.extend(pred_locations(read_use.location, body));

        while let Some(loc) = stack.pop() {
            if !visited.insert(loc) {
                continue;
            }

            if let Some(write_use) = loc_to_write.get(&loc) {
                reachable_writes.insert((*write_use).clone());
                continue;
            }

            for pred in pred_locations(loc, body) {
                stack.push(pred);
            }
        }

        result.insert(read_use.clone(), reachable_writes);
    }

    result
}

/// TODO: consider more types
/// Currently, only primitive types can pass
fn is_byte_implemented_ty<'a>(ty: Ty<'a>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
    )
}

fn is_replacable_read<'a>(
    read_use: &UnionUseInfo<'a>,
    write_use: &FxHashSet<UnionUseInfo<'a>>,
    body: &Body<'a>,
    tcx: TyCtxt<'a>,
) -> bool {
    let rt = read_use.kind.field_type(body, tcx);
    if !is_byte_implemented_ty(rt) {
        return false;
    }
    for w in write_use {
        let wt = w.kind.field_type(body, tcx);
        if !is_byte_implemented_ty(wt) {
            return false;
        }
    }
    true
}

pub fn analyze(tcx: TyCtxt) -> AnalysisResult {
    let union_uses_map = collect_union_uses_map(tcx);
    // println!();
    // _print_union_uses_map(&union_uses_map);
    // println!();
    let mut result_map = FxHashMap::default();

    for (def_id, union_uses) in union_uses_map {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();

        let mut place_map = FxHashMap::default();

        for (place, uses) in &union_uses {
            // println!("For Place {place:?}:");
            let init_use = uses
                .iter()
                .find(|u| matches!(u.kind, UnionUseKind::InitUnion(_, _, _)))
                .unwrap();

            let read_write_map = collect_readable_writes(uses, body);

            let read_write_map = read_write_map
                .into_iter()
                .map(|(read_use, write_uses)| {
                    (
                        read_use.clone(),
                        (
                            is_replacable_read(&read_use, &write_uses, body, tcx),
                            write_uses,
                        ),
                    )
                })
                .collect::<FxHashMap<UnionUseInfo, (bool, FxHashSet<UnionUseInfo>)>>();

            place_map.insert(*place, (init_use.clone(), read_write_map));
        }

        result_map.insert(def_id, place_map);
    }
    AnalysisResult { map: result_map }
}
