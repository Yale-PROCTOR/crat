use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_index::Idx;
use rustc_middle::{
    mir::{Body, Location, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    analysis::{UnionInstanceUses, UnionMemoryInstance, UnionRead, UnionUseResult, UnionWrite},
    callgraph::CallGraph,
};

pub type ReadToWrites = FxHashMap<UnionRead, Vec<UnionWrite>>;

pub struct ReverseCfgResult {
    pub uses: FxHashMap<DefId, InstanceResult>,
}

#[derive(Default)]
pub struct InstanceResult {
    pub instances: FxHashMap<UnionMemoryInstance, ReadToWrites>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct CallSite {
    caller: LocalDefId,
    location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SearchPoint {
    Entry(LocalDefId),
    Location {
        def_id: LocalDefId,
        location: Location,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SearchState {
    point: SearchPoint,
    active_callsite: Option<CallSite>,
}

#[derive(Default)]
struct InstanceIndex {
    reads: Vec<UnionRead>,
    writes_by_loc: FxHashMap<(LocalDefId, Location), Vec<UnionWrite>>,
}

#[derive(Default)]
struct CallIndex {
    /// callee function -> callsites that invoke it.
    callers_of: FxHashMap<LocalDefId, Vec<CallSite>>,
    /// callsite -> direct local callees (filtered by union-related callgraph).
    callees_of: FxHashMap<CallSite, Vec<LocalDefId>>,
    /// callsite -> flattened (callee, callee return location) pairs used during backward entry.
    /// `callee return location` means the MIR location of a `Return` terminator in the callee:
    return_entries_of: FxHashMap<CallSite, Vec<(LocalDefId, Location)>>,
}

pub fn analyze_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_uses: &UnionUseResult,
    callgraphs: &FxHashMap<LocalDefId, CallGraph>,
    use_optimized_mir: bool,
) -> ReverseCfgResult {
    let mut result = FxHashMap::default();

    for (&union_ty, type_uses) in &union_uses.uses {
        let Some(local_union_ty) = union_ty.as_local() else {
            continue;
        };
        let Some(callgraph) = callgraphs.get(&local_union_ty) else {
            continue;
        };

        let mut instances = FxHashMap::default();
        for (&instance, instance_uses) in &type_uses.instances {
            let reaching =
                analyze_instance_reaching_writes(tcx, instance_uses, callgraph, use_optimized_mir);
            instances.insert(instance, reaching);
        }

        result.insert(union_ty, InstanceResult { instances });
    }

    ReverseCfgResult { uses: result }
}

fn analyze_instance_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_uses: &UnionInstanceUses,
    callgraph: &CallGraph,
    use_optimized_mir: bool,
) -> ReadToWrites {
    let instance_index = build_instance_index(instance_uses);
    let call_index = build_call_index(tcx, callgraph, use_optimized_mir);

    let mut reads = instance_index.reads.clone();
    reads.sort_by_key(|read| sort_location_key(read.site.def_id, read.site.location));

    let mut result = FxHashMap::default();
    for read in reads {
        let writes = collect_reaching_writes_for_read(
            tcx,
            read,
            &instance_index,
            &call_index,
            use_optimized_mir,
        );
        result.insert(read, writes);
    }
    result
}

fn collect_reaching_writes_for_read<'tcx>(
    tcx: TyCtxt<'tcx>,
    read: UnionRead,
    instance_index: &InstanceIndex,
    call_index: &CallIndex,
    use_optimized_mir: bool,
) -> Vec<UnionWrite> {
    let mut found = FxHashSet::default();
    let mut visited = FxHashSet::default();
    let mut entered_callsites = FxHashSet::default();
    let mut worklist = vec![SearchState {
        point: SearchPoint::Location {
            def_id: read.site.def_id,
            location: read.site.location,
        },
        active_callsite: None,
    }];

    while let Some(state) = worklist.pop() {
        if !visited.insert(state) {
            continue;
        }

        match state.point {
            SearchPoint::Entry(def_id) => {
                if let Some(active_callsite) = state.active_callsite {
                    // Check if that callsite is a write
                    if let Some(writes) = instance_index
                        .writes_by_loc
                        .get(&(active_callsite.caller, active_callsite.location))
                    {
                        found.extend(writes.iter().copied());
                    }
                    // Spread to the callsite
                    with_body(tcx, active_callsite.caller, use_optimized_mir, |body| {
                        for point in
                            previous_points(body, active_callsite.caller, active_callsite.location)
                        {
                            worklist.push(SearchState {
                                point,
                                active_callsite: None,
                            });
                        }
                    });
                    continue;
                }

                // If no callsites were specified, spread to all callers
                if let Some(callers) = call_index.callers_of.get(&def_id) {
                    for &callsite in callers {
                        if !entered_callsites.insert(callsite) {
                            continue;
                        }
                        // Check if that callsite is a write
                        if let Some(writes) = instance_index
                            .writes_by_loc
                            .get(&(callsite.caller, callsite.location))
                        {
                            found.extend(writes.iter().copied());
                        }
                        // Spread to the callsite
                        with_body(tcx, callsite.caller, use_optimized_mir, |body| {
                            for point in previous_points(body, callsite.caller, callsite.location) {
                                worklist.push(SearchState {
                                    point,
                                    active_callsite: None,
                                });
                            }
                        });
                    }
                }
            }
            SearchPoint::Location { def_id, location } => {
                // If current location is a write, add it to the results and stop analysis for current path
                if let Some(writes) = instance_index.writes_by_loc.get(&(def_id, location)) {
                    found.extend(writes.iter().copied());
                    continue;
                }

                // Check if current location is a callsite
                let callsite = CallSite {
                    caller: def_id,
                    location,
                };
                if call_index.callees_of.contains_key(&callsite) {
                    if entered_callsites.insert(callsite)
                        && let Some(entries) = call_index.return_entries_of.get(&callsite)
                    {
                        // Spread to all return points of each callee
                        for &(callee, return_location) in entries {
                            worklist.push(SearchState {
                                point: SearchPoint::Location {
                                    def_id: callee,
                                    location: return_location,
                                },
                                active_callsite: Some(callsite),
                            });
                        }
                    }
                    continue;
                }

                with_body(tcx, def_id, use_optimized_mir, |body| {
                    for point in previous_points(body, def_id, location) {
                        worklist.push(SearchState {
                            point,
                            active_callsite: state.active_callsite,
                        });
                    }
                });
            }
        }
    }

    let mut writes = found.into_iter().collect::<Vec<_>>();
    writes.sort_by_key(|write| sort_location_key(write.site.def_id, write.site.location));
    writes
}

fn build_instance_index(instance_uses: &UnionInstanceUses) -> InstanceIndex {
    let mut index = InstanceIndex {
        reads: instance_uses
            .reads
            .values()
            .flat_map(|reads| reads.iter().copied())
            .collect(),
        writes_by_loc: FxHashMap::default(),
    };

    for (&def_id, writes) in &instance_uses.writes {
        for &write in writes {
            index
                .writes_by_loc
                .entry((def_id, write.site.location))
                .or_default()
                .push(write);
        }
    }

    index
}

fn build_call_index<'tcx>(
    tcx: TyCtxt<'tcx>,
    callgraph: &CallGraph,
    use_optimized_mir: bool,
) -> CallIndex {
    let mut relevant_callees: FxHashMap<LocalDefId, FxHashSet<LocalDefId>> = FxHashMap::default();
    for (&caller, callees) in callgraph {
        let Some(caller) = caller.as_local() else {
            continue;
        };
        for callee in callees.iter().filter_map(|callee| callee.as_local()) {
            relevant_callees.entry(caller).or_default().insert(callee);
        }
    }

    let mut index = CallIndex::default();
    let mut return_cache: FxHashMap<LocalDefId, Vec<Location>> = FxHashMap::default();

    for (&caller, candidate_callees) in &relevant_callees {
        with_body(tcx, caller, use_optimized_mir, |body| {
            for (block, bbd) in body.basic_blocks.iter_enumerated() {
                let location = Location {
                    block,
                    statement_index: bbd.statements.len(),
                };
                let TerminatorKind::Call { func, .. } = &bbd.terminator().kind else {
                    continue;
                };
                let Some((callee, _)) = func.const_fn_def() else {
                    continue;
                };
                let Some(callee) = callee.as_local() else {
                    continue;
                };
                if !candidate_callees.contains(&callee) {
                    continue;
                }
                if !tcx.is_mir_available(callee.to_def_id()) {
                    continue;
                }

                let callsite = CallSite { caller, location };
                index.callees_of.entry(callsite).or_default().push(callee);
                index.callers_of.entry(callee).or_default().push(callsite);
            }
        });
    }

    for callees in index.callees_of.values_mut() {
        callees.sort_by_key(|def_id| def_id.index());
        callees.dedup();
    }
    for callers in index.callers_of.values_mut() {
        callers.sort_by_key(|callsite| {
            (
                callsite.caller.index(),
                callsite.location.block.index(),
                callsite.location.statement_index,
            )
        });
        callers.dedup();
    }

    for (&callsite, callees) in &index.callees_of {
        let mut entries = Vec::new();
        for &callee in callees {
            let returns = return_cache
                .entry(callee)
                .or_insert_with(|| collect_return_locations(tcx, callee, use_optimized_mir));
            for &ret in returns.iter() {
                entries.push((callee, ret));
            }
        }
        entries.sort_by_key(|(def_id, location)| {
            (
                def_id.index(),
                location.block.index(),
                location.statement_index,
            )
        });
        entries.dedup();
        index.return_entries_of.insert(callsite, entries);
    }

    index
}

fn collect_return_locations<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    use_optimized_mir: bool,
) -> Vec<Location> {
    with_body(tcx, def_id, use_optimized_mir, |body| {
        let mut returns = Vec::new();
        for (block, bbd) in body.basic_blocks.iter_enumerated() {
            if matches!(bbd.terminator().kind, TerminatorKind::Return) {
                returns.push(Location {
                    block,
                    statement_index: bbd.statements.len(),
                });
            }
        }
        returns.sort_by_key(|location| (location.block.index(), location.statement_index));
        returns.dedup();
        returns
    })
}

fn previous_points<'tcx>(
    body: &Body<'tcx>,
    def_id: LocalDefId,
    location: Location,
) -> Vec<SearchPoint> {
    if location.statement_index > 0 {
        return vec![SearchPoint::Location {
            def_id,
            location: Location {
                block: location.block,
                statement_index: location.statement_index - 1,
            },
        }];
    }

    let mut out = Vec::new();
    if location.block.index() == 0 {
        out.push(SearchPoint::Entry(def_id));
    }

    for pred_block in body.basic_blocks.predecessors()[location.block]
        .iter()
        .copied()
    {
        out.push(SearchPoint::Location {
            def_id,
            location: body.terminator_loc(pred_block),
        });
    }

    out.sort_by_key(sort_point_key);
    out.dedup();
    out
}

fn with_body<'tcx, R, F: FnOnce(&Body<'tcx>) -> R>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    use_optimized_mir: bool,
    f: F,
) -> R {
    debug_assert!(matches!(
        tcx.def_kind(def_id),
        DefKind::Fn | DefKind::AssocFn
    ));
    if use_optimized_mir {
        f(tcx.optimized_mir(def_id.to_def_id()))
    } else {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body = body.borrow();
        f(&body)
    }
}

fn sort_location_key(def_id: LocalDefId, location: Location) -> (usize, usize, usize) {
    (
        def_id.index(),
        location.block.index(),
        location.statement_index,
    )
}

fn sort_point_key(point: &SearchPoint) -> (usize, usize, usize, u8) {
    match point {
        SearchPoint::Entry(def_id) => (def_id.index(), 0, 0, 0),
        SearchPoint::Location { def_id, location } => (
            def_id.index(),
            location.block.index(),
            location.statement_index,
            1,
        ),
    }
}
