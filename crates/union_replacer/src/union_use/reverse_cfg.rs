use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{Body, Location},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    analysis::{
        UnionInstanceUses, UnionMemoryInstance, UnionRead, UnionUseResult, UnionWrite,
        format_access, union_field_ty,
    },
    callgraph::{CallIndex, CallSite, UnionCallContext},
    utils::with_body,
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

pub fn analyze_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_uses: &UnionUseResult,
    call_contexts: &FxHashMap<LocalDefId, UnionCallContext>,
    use_optimized_mir: bool,
) -> ReverseCfgResult {
    let mut result = FxHashMap::default();

    for (&union_ty, type_uses) in &union_uses.uses {
        let Some(local_union_ty) = union_ty.as_local() else {
            continue;
        };
        let Some(call_context) = call_contexts.get(&local_union_ty) else {
            continue;
        };

        let mut instances = FxHashMap::default();
        for (&instance, instance_uses) in &type_uses.instances {
            let reaching = analyze_instance_reaching_writes(
                tcx,
                instance_uses,
                &call_context.call_index,
                use_optimized_mir,
            );
            instances.insert(instance, reaching);
        }

        result.insert(union_ty, InstanceResult { instances });
    }

    ReverseCfgResult { uses: result }
}

pub fn detect_overlapping_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_uses: &UnionUseResult,
    analysis: &ReverseCfgResult,
    verbose: bool,
) -> Vec<LocalDefId> {
    let union_tys = union_uses.uses.keys().copied().collect::<Vec<_>>();
    let mut overlapping_tys: Vec<LocalDefId> = Vec::new();

    if verbose {
        println!("\nReaching Writes:");
    }

    for union_ty in union_tys {
        let Some(type_uses) = union_uses.uses.get(&union_ty) else {
            continue;
        };
        let Some(type_result) = analysis.uses.get(&union_ty) else {
            continue;
        };
        let mut is_overlapping = false;
        if verbose {
            println!("\t{}:", tcx.def_path_str(union_ty));
        }

        for instance in type_uses.instances.keys() {
            if verbose {
                println!(
                    "\t\tInstance L{}..=L{}:",
                    instance.root.index(),
                    instance.end.index()
                );
            }

            let Some(reaching) = type_result.instances.get(instance) else {
                if verbose {
                    println!("\t\t\t(no reads)");
                }
                continue;
            };

            let reads = reaching.iter().collect::<Vec<_>>();

            if reads.is_empty() {
                if verbose {
                    println!("\t\t\t(no reads)");
                }
                continue;
            }

            for (read, writes) in reads {
                let read_field = format_access(tcx, union_ty, read);
                let read_field_ty = union_field_ty(tcx, union_ty, read.field);
                let writes = writes.clone();

                let write_sites = writes
                    .into_iter()
                    .map(|write| {
                        if is_overlapping_pair(tcx, union_ty, read, &write) {
                            is_overlapping = true;
                        }
                        format!(
                            "{:?}@{:?}\n\t\t\t\t\tfield:\t{}",
                            write.site.def_id,
                            write.site.location,
                            format_access(tcx, union_ty, &write),
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n\t\t\t\t");

                if verbose {
                    println!(
                        "\t\t\tRead {:?}@{:?}\n\t\t\t\tfield:\t{}",
                        read.site.def_id, read.site.location, read_field
                    );
                    if let Some(ty) = read_field_ty {
                        println!("\t\t\t\ttype:\t{ty:?}");
                    }
                    if write_sites.is_empty() {
                        println!("\t\t\t\tWrites:\t(none)");
                    } else {
                        println!("\t\t\t\tWrites:\n\t\t\t\t{write_sites}");
                    }
                }
            }
        }

        if is_overlapping && let Some(local) = union_ty.as_local() {
            overlapping_tys.push(local);
        }
    }

    overlapping_tys
}

fn analyze_instance_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_uses: &UnionInstanceUses,
    call_index: &CallIndex,
    use_optimized_mir: bool,
) -> ReadToWrites {
    let instance_index = build_instance_index(instance_uses);

    let reads = instance_index.reads.clone();

    let mut result = FxHashMap::default();
    for read in reads {
        let writes = collect_reaching_writes_for_read(
            tcx,
            read,
            &instance_index,
            call_index,
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
                        .get(&(active_callsite.caller, active_callsite.call_location))
                    {
                        found.extend(writes.iter().copied());
                    }
                    // Spread to the callsite
                    with_body(tcx, active_callsite.caller, use_optimized_mir, |body| {
                        for point in previous_points(
                            body,
                            active_callsite.caller,
                            active_callsite.call_location,
                        ) {
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
                            .get(&(callsite.caller, callsite.call_location))
                        {
                            found.extend(writes.iter().copied());
                        }
                        // Spread to the callsite
                        with_body(tcx, callsite.caller, use_optimized_mir, |body| {
                            for point in
                                previous_points(body, callsite.caller, callsite.call_location)
                            {
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
                    call_location: location,
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

    found.into_iter().collect::<Vec<_>>()
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

    let mut seen = FxHashSet::default();
    out.retain(|p| seen.insert(*p));
    out
}

fn is_overlapping_pair<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: DefId,
    read: &UnionRead,
    write: &UnionWrite,
) -> bool {
    let Some(read_ty) = union_field_ty(tcx, union_ty, read.field) else {
        return false;
    };
    let Some(write_ty) = union_field_ty(tcx, union_ty, write.field) else {
        return false;
    };
    read_ty != write_ty
}
