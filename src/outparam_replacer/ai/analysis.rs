use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt::Write as _,
    path::Path,
};

use etrace::some_or;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_const_eval::interpret::{GlobalAlloc, Scalar};
use rustc_data_structures::graph::Successors;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::{DefKind, Res},
    intravisit::Visitor as HVisitor,
};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    hir::nested_filter,
    mir::{
        BasicBlock, Body, Const, ConstOperand, ConstValue, Local, Location, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor as MVisitor},
    },
    ty::{AdtKind, Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::Analysis as _;
use rustc_span::{
    Span,
    def_id::{DefId, LocalDefId},
    source_map::SourceMap,
};
use serde::{Deserialize, Serialize};
use serde_json;
use typed_arena::Arena;

use super::{
    domains::*,
    pre_analysis::{self, PreAnalysisContext},
    semantics::{CallKind, TransferedTerminator},
};
use crate::{
    compile_util, graph_util,
    points_to::andersen::{self, Loc},
    ty_shape,
};

// TODO: Remove span translation
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LoHi {
    pub lo: u32,
    pub hi: u32,
}

impl LoHi {
    #[inline]
    fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    #[inline]
    pub fn from_span(span: Span) -> Self {
        assert!(span.ctxt().is_root());
        assert!(span.parent().is_none());
        Self::new(span.lo().0, span.hi().0)
    }
}

// The result of the output parameter analysis
pub type AnalysisResult = FxHashMap<String, (FunctionSummary, FnAnalysisRes)>;

#[derive(Clone, Debug)]
pub struct FunctionSummary {
    pub init_state: AbsState,
    pub return_states: BTreeMap<(MustPathSet, AbsNulls), AbsState>,
    pub has_side_effects: bool,
}

impl FunctionSummary {
    fn new(
        init_state: AbsState,
        return_states: BTreeMap<(MustPathSet, AbsNulls), AbsState>,
        has_side_effects: bool,
    ) -> Self {
        Self {
            init_state,
            return_states,
            has_side_effects,
        }
    }

    fn bot() -> Self {
        Self {
            init_state: AbsState::bot(),
            return_states: BTreeMap::new(),
            has_side_effects: false,
        }
    }

    fn join(&self, other: &Self) -> Self {
        let init_state = self.init_state.join(&other.init_state);
        let keys: BTreeSet<_> = self
            .return_states
            .keys()
            .chain(other.return_states.keys())
            .cloned()
            .collect();
        let return_states = keys
            .into_iter()
            .map(|k| {
                let v = match (self.return_states.get(&k), other.return_states.get(&k)) {
                    (Some(v1), Some(v2)) => v1.join(v2),
                    (Some(v), None) | (None, Some(v)) => (*v).clone(),
                    _ => unreachable!(),
                };
                (k, v)
            })
            .collect();
        let has_side_effects = self.has_side_effects || other.has_side_effects;
        Self::new(init_state, return_states, has_side_effects)
    }

    fn ord(&self, other: &Self) -> bool {
        self.init_state.ord(&other.init_state)
            && {
                self.return_states
                    .iter()
                    .all(|(k, v)| other.return_states.get(k).is_some_and(|w| v.ord(w)))
            }
            && self.has_side_effects == other.has_side_effects
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FnAnalysisRes {
    pub output_params: Vec<OutputParam>,
    pub wbrs: Vec<WriteBeforeReturn>,
    pub rcfws: Rcfws,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OutputParam {
    pub index: usize,
    pub must: bool,
    pub return_values: ReturnValues,
    pub complete_writes: Vec<CompleteWrite>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WriteBeforeReturn {
    pub span: LoHi,
    pub mays: BTreeSet<usize>,
    pub musts: BTreeSet<usize>,
}

// Removable checks for Write s
pub type Rcfws = BTreeMap<usize, BTreeSet<LoHi>>;

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct CompleteWrite {
    pub block: usize,
    pub statement_index: usize,
    pub write_arg: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ReturnValues {
    None,
    Int(AbsInt, AbsInt),
    Uint(AbsUint, AbsUint),
    Bool(AbsBool, AbsBool),
}

pub fn write_analysis_result(path: &Path, result: &AnalysisResult) {
    let file = std::fs::File::create(path).unwrap();
    let writes = result
        .iter()
        .filter_map(|(def_id, (_summary, res))| {
            if res.output_params.is_empty() {
                None
            } else {
                Some((def_id, res))
            }
        })
        .collect::<BTreeMap<_, _>>();
    serde_json::to_writer_pretty(file, &writes).unwrap();
}

pub fn analyze(
    config: &crate::outparam_replacer::Config,
    verbose: bool,
    tcx: TyCtxt<'_>,
) -> AnalysisResult {
    let mut call_graph = FxHashMap::default();
    let mut inputs_map = FxHashMap::default();
    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        if let Some(ident) = item.kind.ident()
            && ident.name.as_str() == "main"
        {
            continue;
        }
        let inputs = if let rustc_hir::ItemKind::Fn { sig, .. } = &item.kind {
            sig.decl.inputs.len()
        } else {
            continue;
        };
        let def_id = item.item_id().owner_id.def_id.to_def_id();
        inputs_map.insert(def_id, inputs);
        let mut visitor = CallVisitor::new(tcx);
        visitor.visit_item(item);
        call_graph.insert(def_id, visitor.callees);
    }

    let funcs: FxHashSet<_> = call_graph.keys().cloned().collect();
    for callees in call_graph.values_mut() {
        callees.retain(|callee| funcs.contains(callee));
    }

    let sccs = graph_util::sccs_copied::<DefId, true>(&call_graph);
    let transitive = graph_util::reflexive_transitive_closure(&call_graph);
    let po: Vec<_> = sccs.post_order().collect();

    let mut visitor = FnPtrVisitor::new(tcx);
    let mut global_visitor = GlobalVisitor::new(tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    let info_map: FxHashMap<_, _> = funcs
        .iter()
        .map(|def_id| {
            let inputs = inputs_map[def_id];
            let body = tcx.optimized_mir(def_id);
            let param_tys = get_param_tys(body, inputs, tcx);
            let pre_rpo_map = get_rpo_map(body);
            let loop_blocks = get_loop_blocks(body, &pre_rpo_map);
            let rpo_map = compute_rpo_map(body, &loop_blocks);
            let dead_locals = get_dead_locals(body, tcx);
            let fn_ptr = visitor.fn_ptrs.contains(def_id);
            global_visitor.visit_body(body);
            let globals = std::mem::take(&mut global_visitor.globals);
            let info = FuncInfo {
                inputs,
                param_tys,
                loop_blocks,
                rpo_map,
                dead_locals,
                fn_ptr,
                globals,
            };
            (*def_id, info)
        })
        .collect();

    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx);
    let pre = andersen::pre_analyze(&tss, tcx);
    let solutions = if let Some(path) = &config.points_to_file {
        let arr = std::fs::read(path).unwrap();
        andersen::deserialize_solutions(&arr)
    } else {
        andersen::analyze(&pre, &tss, tcx)
    };

    let pre_data = pre_analysis::compute_alias(
        pre,
        &solutions,
        &inputs_map,
        tcx,
        config.check_global_alias,
        config.check_param_alias,
    );

    let mut ptr_params_map = FxHashMap::default();
    let mut ptr_params_inv_map = FxHashMap::default();
    let mut output_params_map = FxHashMap::default();
    let mut summaries = FxHashMap::default();
    let mut results = FxHashMap::default();
    let mut wm_map = FxHashMap::default();
    let mut call_args_map = FxHashMap::default();
    let mut analysis_times: FxHashMap<_, u128> = FxHashMap::default();

    let mut wbrs: FxHashMap<DefId, Vec<WriteBeforeReturn>> = FxHashMap::default();
    let mut bb_musts: FxHashMap<DefId, BTreeMap<BasicBlock, BTreeSet<usize>>> =
        FxHashMap::default();
    let mut is_units = FxHashMap::default();

    let mut rcfws = FxHashMap::default();
    for id in &po {
        let def_ids = &sccs.scc_elems[*id];
        let recursive = if def_ids.len() == 1 {
            let def_id = def_ids.iter().next().unwrap();
            call_graph[def_id].contains(def_id)
        } else {
            true
        };

        loop {
            if recursive {
                for def_id in def_ids {
                    let _ = summaries.try_insert(*def_id, FunctionSummary::bot());
                }
            }

            let mut need_rerun = false;
            for def_id in def_ids {
                let start = std::time::Instant::now();

                let pre_context = PreAnalysisContext::new(*def_id, &pre_data, &solutions);

                let mut analyzer =
                    Analyzer::new(tcx, &info_map[def_id], config, &summaries, pre_context);
                let body = tcx.optimized_mir(*def_id);
                if verbose {
                    println!(
                        "{:?} {} {}",
                        def_id,
                        body.basic_blocks.len(),
                        body.local_decls.len()
                    );
                }

                let AnalyzedBody {
                    states,
                    writes_map,
                    init_state,
                    call_info_map,
                    is_merged,
                } = analyzer.analyze_body(body);
                if config.print_functions.contains(&tcx.def_path_str(def_id)) {
                    tracing::info!(
                        "{:?}\n{}",
                        def_id,
                        analysis_result_to_string(body, &states, tcx.sess.source_map()).unwrap()
                    );
                }

                let ret_location = return_location(body);

                let mut return_states = ret_location
                    .and_then(|ret| states.get(&ret))
                    .cloned()
                    .unwrap_or_default();

                // If there is a merged block, always check all parameters
                let (candidates, nonnull_params) = if is_merged {
                    (
                        (1..=(analyzer.info.inputs))
                            .map(Local::from_usize)
                            .collect::<BTreeSet<Local>>(),
                        BTreeSet::new(),
                    )
                } else {
                    // If not, we filter the parameters which are implicity non-null
                    analyzer.get_nullable_candidates(&return_states)
                };

                let nullable_params = analyzer.find_nullable_params(
                    tcx,
                    &states,
                    body,
                    &writes_map,
                    &call_info_map,
                    candidates,
                );

                let alias_params = if config.check_global_alias {
                    analyzer.check_reachable_globals(
                        &info_map,
                        &pre_data.globals,
                        transitive.get(def_id).unwrap(),
                    )
                } else {
                    BTreeSet::new()
                };

                let null_exclude_paths: Vec<_> = nullable_params
                    .iter()
                    .flat_map(|p| analyzer.expands_path(&AbsPath::new(*p, vec![])))
                    .collect();
                let alias_exclude_paths: Vec<_> = alias_params
                    .iter()
                    .flat_map(|p| analyzer.expands_path(&AbsPath::new(*p, vec![])))
                    .collect();

                let mut wbr = vec![];
                let mut bb_must = BTreeMap::new();

                let mut stack = vec![];

                if let Some(ret_location) = ret_location {
                    if let Some((ret_loc_assign0, ret_loc)) =
                        exists_assign0(body, ret_location.block)
                    {
                        stack.push((ret_loc, ret_loc_assign0));
                    } else if let Some(v) = body.basic_blocks.predecessors().get(ret_location.block)
                    {
                        for i in v {
                            if let Some((sp, ret_loc)) = exists_assign0(body, *i) {
                                stack.push((ret_loc, sp));
                            }
                        }
                    }

                    let empty_map = BTreeMap::new();
                    for (loc, sp) in stack.iter() {
                        let writes: Vec<_> = states
                            .get(loc)
                            .unwrap_or(&empty_map)
                            .values()
                            .map(|st| st.writes.as_set())
                            .collect();
                        let musts: BTreeSet<_> = writes
                            .iter()
                            .copied()
                            .fold(None, |acc: Option<BTreeSet<_>>, ws| {
                                Some(match acc {
                                    Some(acc) => acc.intersection(ws).cloned().collect(),
                                    None => ws.clone(),
                                })
                            })
                            .unwrap_or_default()
                            .iter()
                            .map(|p| p.base.index() - 1)
                            .collect();
                        let mays: BTreeSet<_> = writes
                            .into_iter()
                            .flatten()
                            .map(|p| p.base.index() - 1)
                            .collect();
                        let span = LoHi::from_span(*sp);
                        bb_must.insert(loc.block, musts.clone());
                        wbr.push(WriteBeforeReturn { span, mays, musts });
                    }
                }

                wbrs.insert(*def_id, wbr);
                bb_musts.insert(*def_id, bb_must);
                is_units.insert(*def_id, stack.is_empty());

                // Handle unremovable parameters
                for st in return_states.values_mut() {
                    st.writes.remove(&nullable_params);
                    st.writes.remove(&alias_params);

                    st.add_excludes(alias_exclude_paths.iter().cloned());
                    st.add_null_excludes(null_exclude_paths.iter().cloned());

                    st.null_excludes.remove(&nonnull_params);
                }

                let mut has_side_effects = call_info_map.values().flatten().any(|kind| {
                    matches!(
                        kind,
                        CallKind::TOP
                            | CallKind::RustEffect(_)
                            | CallKind::CEffect
                            | CallKind::IntraEffect
                    )
                });

                has_side_effects = has_side_effects || analyzer.check_global_writes();

                let summary = FunctionSummary::new(init_state, return_states, has_side_effects);
                results.insert(*def_id, states);
                ptr_params_map.insert(*def_id, analyzer.ptr_params);
                ptr_params_inv_map.insert(*def_id, analyzer.ptr_params_inv);
                wm_map.insert(*def_id, writes_map);
                call_args_map.insert(*def_id, analyzer.call_args);

                let (summary, updated) = if let Some(old) = summaries.get(def_id) {
                    let new_summary = summary.join(old);
                    let updated = !new_summary.ord(old);
                    (new_summary, updated)
                } else {
                    (summary, false)
                };
                summaries.insert(*def_id, summary);
                need_rerun |= updated;

                *analysis_times.entry(*def_id).or_default() += start.elapsed().as_millis();
            }

            if !need_rerun {
                for def_id in def_ids {
                    let pre_context = PreAnalysisContext::new(*def_id, &pre_data, &solutions);
                    let mut analyzer =
                        Analyzer::new(tcx, &info_map[def_id], config, &summaries, pre_context);
                    analyzer.ptr_params = ptr_params_map.remove(def_id).unwrap();
                    analyzer.ptr_params_inv = ptr_params_inv_map.remove(def_id).unwrap();
                    let summary = &summaries[def_id];
                    let return_ptrs = analyzer.get_return_ptrs(summary);
                    let mut output_params =
                        analyzer.find_output_params(summary, &return_ptrs, *def_id);
                    let writes_map = wm_map.remove(def_id).unwrap();
                    let call_args = call_args_map.remove(def_id).unwrap();
                    let result = results.remove(def_id).unwrap();
                    for p in &mut output_params {
                        analyzer.find_complete_write(p, &result, &writes_map, &call_args, *def_id);
                    }

                    let body = tcx.optimized_mir(*def_id);
                    let bb_must = &bb_musts[def_id];
                    let mut rcfw: Rcfws = BTreeMap::new();

                    if !is_units[def_id] {
                        for p in &output_params {
                            let OutputParam {
                                index,
                                complete_writes,
                                ..
                            } = p;
                            for complete_write in complete_writes {
                                let CompleteWrite {
                                    block,
                                    statement_index,
                                    ..
                                } = complete_write;

                                let mut stack = vec![BasicBlock::from_usize(*block)];
                                let mut visited: BTreeSet<_> = stack.iter().cloned().collect();

                                let always_write = loop {
                                    if let Some(bb) = stack.pop() {
                                        if let Some(musts) = bb_must.get(&bb)
                                            && !musts.contains(index)
                                        {
                                            break false;
                                        }

                                        let term = body.basic_blocks[bb].terminator();
                                        for bb in term.successors() {
                                            if !visited.contains(&bb) {
                                                visited.insert(bb);
                                                stack.push(bb);
                                            }
                                        }
                                    } else {
                                        break true;
                                    }
                                };

                                if always_write {
                                    let location = Location {
                                        block: BasicBlock::from_usize(*block),
                                        statement_index: *statement_index,
                                    };
                                    let span = LoHi::from_span(body.source_info(location).span);
                                    let entry = rcfw.entry(*index);
                                    entry.or_default().insert(span);
                                }
                            }
                        }
                    }

                    rcfws.insert(*def_id, rcfw);
                    output_params_map.insert(*def_id, output_params);
                }
                break;
            }
        }
    }

    if config.max_loop_head_states <= 1 {
        wbrs.clear();
        rcfws.clear();
    }

    if let Some(n) = &config.function_times {
        let mut analysis_times: Vec<_> = analysis_times.into_iter().collect();
        analysis_times.sort_by_key(|(_, t)| u128::MAX - *t);
        for (def_id, t) in analysis_times.iter().take(*n) {
            let f = tcx.def_path(*def_id).to_string_no_crate_verbose();
            let body = tcx.optimized_mir(*def_id);
            let blocks = body.basic_blocks.len();
            let stmts = compile_util::body_size(body);
            println!("{:?} {} {} {:.3}", f, blocks, stmts, *t as f32 / 1000.0);
        }
    }

    summaries
        .into_iter()
        .map(|(def_id, summary)| {
            let output_params = output_params_map.remove(&def_id).unwrap();
            let wbrs = wbrs.remove(&def_id).unwrap_or_default();
            let rcfws = rcfws.remove(&def_id).unwrap_or_default();
            let res = FnAnalysisRes {
                output_params,
                wbrs,
                rcfws,
            };
            (tcx.def_path_str(def_id), (summary, res))
        })
        .collect()
}

fn return_location(body: &Body<'_>) -> Option<Location> {
    for block in body.basic_blocks.indices() {
        let bbd = &body.basic_blocks[block];
        if let Some(terminator) = &bbd.terminator
            && terminator.kind == TerminatorKind::Return
        {
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            return Some(location);
        }
    }
    None
}

fn exists_assign0(body: &Body<'_>, bb: BasicBlock) -> Option<(Span, Location)> {
    for (i, stmt) in body.basic_blocks[bb].statements.iter().enumerate() {
        if let StatementKind::Assign(rb) = &stmt.kind
            && (**rb).0.local.as_u32() == 0u32
        {
            return Some((
                stmt.source_info.span,
                Location {
                    block: bb,
                    statement_index: i,
                },
            ));
        }
    }
    let term = body.basic_blocks[bb].terminator();
    if let TerminatorKind::Call {
        func: _,
        args: _,
        destination,
        target,
        unwind: _,
        call_source: _,
        fn_span: _,
    } = term.kind
        && destination.local.as_u32() == 0u32
    {
        return Some((
            term.source_info.span,
            Location {
                block: target.unwrap(),
                statement_index: 0,
            },
        ));
    }
    None
}

pub struct Analyzer<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    info: &'a FuncInfo,
    config: &'a crate::outparam_replacer::Config,
    pub summaries: &'a FxHashMap<DefId, FunctionSummary>,
    pub ptr_params: IndexVec<ArgIdx, Local>,
    pub ptr_params_inv: FxHashMap<Local, ArgIdx>,
    pub call_args: BTreeMap<Location, BTreeMap<usize, usize>>,
    pub pre_context: PreAnalysisContext<'a>,
    pub indirect_assigns: BTreeSet<Local>,
    pub is_merged: bool,
}

struct AnalyzedBody {
    states: BTreeMap<Location, BTreeMap<(MustPathSet, AbsNulls), AbsState>>,
    writes_map: BTreeMap<Location, BTreeSet<AbsPath>>,
    init_state: AbsState,
    call_info_map: BTreeMap<Location, Vec<CallKind>>,
    is_merged: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Write {
    All,
    Partial,
    None,
}

impl<'a, 'tcx> Analyzer<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        info: &'a FuncInfo,
        config: &'a crate::outparam_replacer::Config,
        summaries: &'a FxHashMap<DefId, FunctionSummary>,
        pre_context: PreAnalysisContext<'a>,
    ) -> Self {
        Self {
            tcx,
            info,
            config,
            summaries,
            ptr_params: IndexVec::new(),
            ptr_params_inv: FxHashMap::default(),
            call_args: BTreeMap::new(),
            pre_context,
            indirect_assigns: BTreeSet::new(),
            is_merged: false,
        }
    }

    fn get_return_ptrs(&self, summary: &FunctionSummary) -> BTreeSet<Local> {
        summary
            .return_states
            .values()
            .flat_map(|st| {
                let v = st.local.get(Local::ZERO);
                self.get_read_paths_of_ptr(&v.ptrv, &[])
            })
            .map(|p| p.base)
            .collect()
    }

    // Check if any local is used in the following blocks
    fn check_local_uses(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        block: &BasicBlock,
        locs: &BTreeSet<Location>,
        locals: &BTreeSet<Local>,
    ) -> bool {
        if locals.is_empty() {
            return true;
        }

        for local in locals {
            let mut work_list = VecDeque::new();
            work_list.extend(body.basic_blocks.successors(*block));
            let mut visited = BTreeSet::new();
            let mut visitor = LocalVisitor::new(tcx, *local);

            'outer: while let Some(bb) = work_list.pop_front() {
                if visited.insert(bb) {
                    let bbd = &body.basic_blocks[bb];

                    for (i, stmt) in bbd.statements.iter().enumerate() {
                        let loc = Location {
                            block: bb,
                            statement_index: i,
                        };

                        if !locs.contains(&loc) {
                            visitor.clear();
                            visitor.visit_statement(stmt, loc);
                            match visitor.check_result {
                                StatementCheck::None => {} /* no use -- continue to check next statement */
                                StatementCheck::UseExist => return false, // found a use
                                StatementCheck::Overwritten => {
                                    continue 'outer;
                                } /* value is overwritten -- stop checking */
                            }
                        }
                    }

                    let term = bbd.terminator();
                    let loc = Location {
                        block: bb,
                        statement_index: bbd.statements.len(),
                    };

                    if !locs.contains(&loc) {
                        visitor.clear();
                        visitor.visit_terminator(term, loc);
                        match visitor.check_result {
                            StatementCheck::None => {}
                            StatementCheck::UseExist => return false,
                            StatementCheck::Overwritten => continue,
                        }
                    }
                    work_list.extend(body.basic_blocks.successors(bb));
                }
            }
        }
        true
    }

    fn check_indirect_pure(&self, local: Local, local_writes: &mut BTreeSet<Local>) -> bool {
        let var_nodes = self.pre_context.var_nodes;
        let loc = var_nodes[&(self.pre_context.local_def_id, local)].index;

        if self.check_may_points_global(loc) {
            return false;
        }

        let sol = self.pre_context.solutions[loc].clone();
        local_writes.extend(
            sol.iter()
                .flat_map(|loc| self.pre_context.index_local_map.get(&loc)),
        );
        true
    }

    fn check_terminator_pure(
        &self,
        loc: &Location,
        local_writes: &mut BTreeSet<Local>,
        param: Local,
        call_info_map: &BTreeMap<Location, Vec<CallKind>>,
        term: &Terminator<'_>,
    ) -> bool {
        match &term.kind {
            TerminatorKind::Call { destination, .. } => {
                let call_info = call_info_map.get(loc).unwrap();
                if destination.local == Local::ZERO {
                    return false;
                }

                let is_indirection = destination.is_indirect_first_projection();

                if is_indirection
                    && destination.local != param
                    && !self.check_indirect_pure(destination.local, local_writes)
                {
                    return false;
                }

                if !is_indirection {
                    local_writes.insert(destination.local);
                }

                // check the writes of callee
                call_info.iter().all(|kind| match kind {
                    CallKind::Method
                    | CallKind::RustPure
                    | CallKind::CPure
                    | CallKind::IntraPure => true,
                    CallKind::CEffect
                    | CallKind::TOP
                    | CallKind::RustEffect(None)
                    | CallKind::IntraEffect => false,
                    CallKind::RustEffect(Some(bases)) => {
                        bases.iter().all(|p| match p {
                            AbsBase::Local(idx) => {
                                // Defer the check to the caller
                                local_writes.insert(*idx);
                                true
                            }
                            AbsBase::Heap => false,
                            AbsBase::Null | AbsBase::Arg(_) => true,
                        })
                    }
                })
            }
            TerminatorKind::InlineAsm { .. } => false,
            _ => true,
        }
    }

    fn check_assign_pure(
        &self,
        local_writes: &mut BTreeSet<Local>,
        param: Local,
        stmt: &StatementKind<'_>,
    ) -> bool {
        if let StatementKind::Assign(box (place, _)) = stmt {
            let local = place.local;
            if local == Local::ZERO {
                return false;
            }
            if place.is_indirect_first_projection() {
                if local == param {
                    return true;
                }
                return self.check_indirect_pure(local, local_writes);
            }

            local_writes.insert(place.local);
            true
        } else {
            unreachable!("{:?}", stmt)
        }
    }

    // Compute locations where the parameters are non-null or null
    fn compute_nonnull_null_locs(
        &self,
        result: &BTreeMap<Location, BTreeMap<(MustPathSet, AbsNulls), AbsState>>,
        candidates: BTreeSet<Local>,
    ) -> Vec<(Local, BTreeSet<Location>, BTreeSet<Location>)> {
        let mut locs = vec![];

        for l in candidates {
            let mut nonnull_locs = BTreeSet::new();
            let mut null_locs = BTreeSet::new();
            // collection of locations except non-null or null
            let mut non_nonnull_locs = BTreeSet::new();
            let mut non_null_locs = BTreeSet::new();
            for (loc, sts) in result {
                for (_, nulls) in sts.keys() {
                    if let Some(arg) = self.ptr_params_inv.get(&l) {
                        match nulls.get(*arg) {
                            AbsNull::Null => {
                                null_locs.insert(*loc);
                                non_nonnull_locs.insert(*loc);
                            }
                            AbsNull::Nonnull => {
                                nonnull_locs.insert(*loc);
                                non_null_locs.insert(*loc);
                            }
                            AbsNull::Top => {
                                non_nonnull_locs.insert(*loc);
                                non_null_locs.insert(*loc);
                            }
                        }
                    }
                }
            }

            let nonnull_locs = nonnull_locs
                .difference(&non_nonnull_locs)
                .cloned()
                .collect();
            let null_locs = null_locs.difference(&non_null_locs).cloned().collect();
            locs.push((l, nonnull_locs, null_locs));
        }
        locs
    }

    // We consider a parameter to be nullable if below sets are not the same:
    // 1. The set of locations that are reachable when x is non-null and have side-effects
    // 2. The set of locations that are reachable when x is null and have side-effects
    fn find_nullable_params(
        &self,
        tcx: TyCtxt<'tcx>,
        result: &BTreeMap<Location, BTreeMap<(MustPathSet, AbsNulls), AbsState>>,
        body: &Body<'tcx>,
        writes_map: &BTreeMap<Location, BTreeSet<AbsPath>>,
        call_info_map: &BTreeMap<Location, Vec<CallKind>>,
        candidates: BTreeSet<Local>,
    ) -> BTreeSet<Local> {
        self.compute_nonnull_null_locs(result, candidates)
            .into_iter()
            .filter_map(|(param, nonnull, null)| {
                if null.is_empty() && nonnull.is_empty() {
                    return None;
                }

                let nonnull_diff = nonnull.iter().fold(
                    BTreeMap::new(),
                    |mut acc: BTreeMap<BasicBlock, BTreeSet<Location>>, loc| {
                        acc.entry(loc.block).or_default().insert(*loc);
                        acc
                    },
                );
                let null_diff = null.iter().fold(
                    BTreeMap::new(),
                    |mut acc: BTreeMap<BasicBlock, BTreeSet<Location>>, loc| {
                        acc.entry(loc.block).or_default().insert(*loc);
                        acc
                    },
                );

                let check = |block, locs: &BTreeSet<_>, diff_locs| {
                    let mut local_writes = BTreeSet::new();
                    locs.iter().all(|loc| {
                        let writes = writes_map.get(loc).unwrap();
                        let Location {
                            block,
                            statement_index,
                        } = loc;

                        if writes.iter().any(|p| p.base != param) {
                            return false;
                        }

                        let bbd = &body.basic_blocks[*block];
                        if *statement_index < bbd.statements.len() {
                            let stmt = &bbd.statements[*statement_index];
                            self.check_assign_pure(&mut local_writes, param, &stmt.kind)
                        } else {
                            let term = bbd.terminator();
                            self.check_terminator_pure(
                                loc,
                                &mut local_writes,
                                param,
                                call_info_map,
                                term,
                            )
                        }
                    }) && self.check_local_uses(tcx, body, block, diff_locs, &local_writes)
                };
                if nonnull_diff
                    .iter()
                    .all(|(b, locs)| check(b, locs, &nonnull))
                    && null_diff.iter().all(|(b, locs)| check(b, locs, &null))
                {
                    None
                } else {
                    Some(param)
                }
            })
            .collect::<BTreeSet<_>>()
    }

    // We consider a parameter p is implicitly non-null if every execution either:
    // 1. effectively writes to the parameter when p -> Top
    // 2. does not write to the parameter and p -> Top (no null check)
    fn get_nullable_candidates(
        &self,
        return_states: &BTreeMap<(MustPathSet, AbsNulls), AbsState>,
    ) -> (BTreeSet<Local>, BTreeSet<Local>) {
        let mut candidates = BTreeSet::new();
        let mut nonnull_params = BTreeSet::new();
        for i in 1..=(self.info.inputs) {
            let l = Local::from_usize(i);
            let Some(arg) = self.ptr_params_inv.get(&l) else {
                continue;
            };

            if return_states.values().all(|st| {
                let writes = st.writes.iter().map(|p| p.base).collect::<FxHashSet<_>>();
                (!writes.contains(&l) && st.nulls.is_top(*arg))
                    || (writes.contains(&l) && st.nonnulls.contains(l))
            }) {
                nonnull_params.insert(l);
            } else {
                candidates.insert(l);
            }
        }
        (candidates, nonnull_params)
    }

    // Check if the global variables that is reachable from the function
    // is an alias of the function parameters
    fn check_reachable_globals(
        &self,
        info_map: &FxHashMap<DefId, FuncInfo>,
        globals: &FxHashMap<LocalDefId, Loc>,
        reachables: &FxHashSet<DefId>,
    ) -> BTreeSet<Local> {
        let mut indexes = FxHashSet::default();

        for reachable in reachables {
            let globals = info_map[reachable]
                .globals
                .iter()
                .filter_map(|def_id| {
                    let local_id = def_id.as_local()?;
                    let start = globals.get(&local_id).copied()?;
                    let end = self.pre_context.ends[start];
                    Some(start..=end)
                })
                .flatten();
            indexes.extend(globals);
        }

        indexes
            .into_iter()
            .flat_map(|index| self.pre_context.check_index_global(index))
            .collect()
    }

    fn check_may_points_global(&self, loc: Loc) -> bool {
        let mut sol = self.pre_context.solutions[loc].clone();
        sol.intersect(self.pre_context.globals);

        if !sol.is_empty() {
            return true;
        }
        false
    }

    fn check_global_writes(&self) -> bool {
        self.indirect_assigns.iter().any(|local| {
            let var_nodes = self.pre_context.var_nodes;
            // We only check start since the local is a pointer
            // If the local is the first parameter of the function, ends[loc] may not be the same as start
            let start = var_nodes[&(self.pre_context.local_def_id, *local)].index;
            self.check_may_points_global(start)
        })
    }

    fn find_output_params(
        &self,
        summary: &FunctionSummary,
        return_ptrs: &BTreeSet<Local>,
        def_id: DefId,
    ) -> Vec<OutputParam> {
        if self.info.fn_ptr || summary.return_states.values().any(|st| st.writes.is_bot()) {
            return vec![];
        }

        let reads: BTreeSet<_> = summary
            .return_states
            .values()
            .flat_map(|st| st.reads.as_set())
            .map(|p| p.base)
            .collect();
        let null_excludes: BTreeSet<_> = summary
            .return_states
            .values()
            .flat_map(|st| st.null_excludes.as_set())
            .map(|p| p.base)
            .collect();
        let excludes: BTreeSet<_> = summary
            .return_states
            .values()
            .flat_map(|st| st.excludes.as_set())
            .map(|p| p.base)
            .collect();

        let body = self.tcx.optimized_mir(def_id);
        let mut writes = vec![];
        for i in 1..=self.info.inputs {
            let i = Local::from_usize(i);
            if reads.contains(&i)
                || excludes.contains(&i)
                || null_excludes.contains(&i)
                || return_ptrs.contains(&i)
                || self.info.param_tys[i] == TypeInfo::Union
            {
                continue;
            }

            let ty = &body.local_decls[i].ty;
            let TyKind::RawPtr(ty, ..) = ty.kind() else {
                continue;
            };
            if ty.is_c_void(self.tcx) {
                continue;
            }

            let expanded: BTreeSet<_> = self
                .expands_path(&AbsPath::new(i, vec![]))
                .into_iter()
                .collect();
            let wrs: Vec<_> = summary
                .return_states
                .values()
                .filter_map(|st| {
                    let arg = self.ptr_params_inv.get(&i).unwrap();
                    if st.nulls.is_null(*arg) {
                        None
                    } else {
                        let writes: BTreeSet<_> = st
                            .writes
                            .iter()
                            .filter_map(|p| if p.base == i { Some(p.clone()) } else { None })
                            .collect();
                        let w = if writes.is_empty() {
                            Write::None
                        } else if writes == expanded {
                            Write::All
                        } else {
                            Write::Partial
                        };
                        let rv = st.local.get(Local::ZERO).clone();
                        Some((w, rv))
                    }
                })
                .collect();

            if wrs.iter().any(|(w, _)| *w == Write::All)
                && wrs.iter().all(|(w, _)| *w != Write::Partial)
            {
                writes.push((i, wrs));
            }
        }
        if writes.is_empty() {
            return vec![];
        }

        let ret_ty = &body.local_decls[Local::from_usize(0)].ty;
        writes
            .into_iter()
            .map(|(index, wrs)| {
                let must = wrs.iter().all(|(w, _)| *w == Write::All);
                let return_values = if !must {
                    let (wst, nwst): (Vec<_>, Vec<_>) =
                        wrs.into_iter().partition(|(w, _)| *w == Write::All);
                    let w = wst
                        .into_iter()
                        .map(|(_, v)| v)
                        .reduce(|a, b| a.join(&b))
                        .unwrap();
                    let nw = nwst
                        .into_iter()
                        .map(|(_, v)| v)
                        .reduce(|a, b| a.join(&b))
                        .unwrap();
                    match ret_ty.kind() {
                        TyKind::Int(_) => ReturnValues::Int(w.intv.clone(), nw.intv.clone()),
                        TyKind::Uint(_) => ReturnValues::Uint(w.uintv.clone(), nw.uintv.clone()),
                        TyKind::Bool => ReturnValues::Bool(w.boolv, nw.boolv),
                        _ => ReturnValues::None,
                    }
                } else {
                    ReturnValues::None
                };
                OutputParam {
                    index: index.index() - 1,
                    must,
                    return_values,
                    complete_writes: vec![],
                }
            })
            .collect()
    }

    fn find_complete_write(
        &self,
        param: &mut OutputParam,
        result: &BTreeMap<Location, BTreeMap<(MustPathSet, AbsNulls), AbsState>>,
        writes_map: &BTreeMap<Location, BTreeSet<AbsPath>>,
        call_args: &BTreeMap<Location, BTreeMap<usize, usize>>,
        def_id: DefId,
    ) {
        if param.must {
            return;
        }

        let paths = self.expands_path(&AbsPath::new(Local::from_usize(param.index + 1), vec![]));

        let body = self.tcx.optimized_mir(def_id);
        let predecessors = body.basic_blocks.predecessors();
        for (location, sts) in result {
            let complete = sts.keys().any(|(w, _)| {
                let w = w.as_set();
                paths.iter().all(|p| w.contains(p))
            });
            if !complete {
                continue;
            }
            let prevs = if location.statement_index == 0 {
                predecessors[location.block]
                    .iter()
                    .map(|bb| {
                        let bbd = &body.basic_blocks[*bb];
                        Location {
                            block: *bb,
                            statement_index: bbd.statements.len(),
                        }
                    })
                    .collect()
            } else {
                let mut l = *location;
                l.statement_index -= 1;
                vec![l]
            };
            for prev in prevs {
                let sts = some_or!(result.get(&prev), continue);
                let pcomplete = sts.keys().all(|(w, _)| {
                    let w = w.as_set();
                    paths.iter().all(|p| w.contains(p))
                });
                if pcomplete {
                    continue;
                }
                let writes = some_or!(writes_map.get(&prev), continue);
                let pwrite = paths.iter().any(|p| writes.contains(p));
                if !pwrite {
                    continue;
                }
                let Location {
                    block,
                    statement_index,
                } = prev;
                let write_arg = call_args
                    .get(&prev)
                    .and_then(|call_args| call_args.get(&param.index))
                    .cloned();
                let block = block.as_usize();
                let cw = CompleteWrite {
                    block,
                    statement_index,
                    write_arg,
                };
                param.complete_writes.push(cw);
            }
        }
    }

    fn analyze_body(&mut self, body: &Body<'tcx>) -> AnalyzedBody {
        let mut start_state = AbsState::bot();
        start_state.writes = MustPathSet::top();
        start_state.nulls = AbsNulls::bot();
        start_state.nonnulls = MustLocalSet::top();

        for i in 1..=self.info.inputs {
            let local = Local::from_usize(i);
            let ty = &body.local_decls[local].ty;
            let v = if let TyKind::RawPtr(ty, ..) = ty.kind() {
                let v = self.top_value_of_ty(ty);
                let idx = start_state.args.push(v);
                start_state.nulls.push_top();
                self.ptr_params.push(local);
                self.ptr_params_inv.insert(local, idx);
                AbsValue::arg(idx)
            } else {
                self.top_value_of_ty(ty)
            };
            start_state.local.set(local, v);
        }

        if self.config.check_param_alias {
            for a in self.pre_context.alias {
                start_state.excludes.insert(AbsPath::new(*a, vec![]));
            }
        }

        let init_state = start_state.clone();

        let start_label = Label {
            location: Location::START,
            writes: start_state.writes.clone(),
            nulls: start_state.nulls.clone(),
        };
        let bot = AbsState::bot();

        let loop_heads: BTreeSet<Location> = self
            .info
            .loop_blocks
            .keys()
            .map(|bb| bb.start_location())
            .collect();
        let mut merging_blocks = if self.config.max_loop_head_states <= 1 {
            self.info.loop_blocks.values().flatten().cloned().collect()
        } else {
            BTreeSet::new()
        };

        let (states, writes_map, call_info_map) = 'analysis_loop: loop {
            if !merging_blocks.is_empty() {
                self.is_merged = true;
            }
            let mut work_list = WorkList::new(&self.info.rpo_map);
            work_list.push(start_label.clone());

            let mut states: BTreeMap<_, BTreeMap<_, _>> = BTreeMap::new();
            states.entry(start_label.location).or_default().insert(
                (start_label.writes.clone(), start_label.nulls.clone()),
                start_state.clone(),
            );
            let mut writes_map: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
            let mut call_info_map: BTreeMap<_, Vec<_>> = BTreeMap::new();

            self.call_args.clear();
            while let Some(label) = work_list.pop() {
                let state = states
                    .get(&label.location)
                    .and_then(|states| states.get(&(label.writes.clone(), label.nulls.clone())))
                    .unwrap_or(&bot);
                let Location {
                    block,
                    statement_index,
                } = label.location;
                let bbd = &body.basic_blocks[block];
                let (new_next_states, next_locations, writes) =
                    if statement_index < bbd.statements.len() {
                        let stmt = &bbd.statements[statement_index];
                        let (new_next_state, writes) = self.transfer_statement(stmt, state);
                        let next_location = Location {
                            block,
                            statement_index: statement_index + 1,
                        };
                        (vec![new_next_state], vec![next_location], writes)
                    } else {
                        let TransferedTerminator {
                            next_states,
                            next_locations,
                            writes,
                            call_info,
                        } = self.transfer_terminator(bbd.terminator(), state, label.location);
                        // Record locations and call info of function calls
                        call_info_map
                            .entry(label.location)
                            .or_default()
                            .extend(call_info);
                        (next_states, next_locations, writes)
                    };
                writes_map.entry(label.location).or_default().extend(writes);

                for location in &next_locations {
                    let dead_locals = &self.info.dead_locals[location.block];
                    if merging_blocks.contains(&location.block) {
                        let next_state = if let Some(states) = states.get(location) {
                            assert_eq!(states.len(), 1);
                            states.first_key_value().unwrap().1
                        } else {
                            &bot
                        };
                        let mut joined = next_state.clone();
                        if let Some(st) = new_next_states.first() {
                            let mut new_next_state = st.clone();
                            for st in new_next_states.iter().skip(1) {
                                new_next_state = new_next_state.join(st);
                            }
                            if loop_heads.contains(location) && !self.config.no_widening {
                                joined = joined.widen(&new_next_state);
                            } else {
                                joined = joined.join(&new_next_state);
                            }
                        }
                        if location.statement_index == 0 {
                            joined.local.clear_dead_locals(dead_locals);
                        }
                        if !joined.ord(next_state) {
                            work_list.remove_location(*location);
                            let next_label = Label {
                                location: *location,
                                writes: joined.writes.clone(),
                                nulls: joined.nulls.clone(),
                            };
                            work_list.push(next_label);

                            let mut new_map = BTreeMap::new();
                            new_map.insert((joined.writes.clone(), joined.nulls.clone()), joined);
                            states.insert(*location, new_map);
                        }
                    } else {
                        for new_next_state in &new_next_states {
                            let next_state = states
                                .get(location)
                                .and_then(|states| {
                                    states.get(&(
                                        new_next_state.writes.clone(),
                                        new_next_state.nulls.clone(),
                                    ))
                                })
                                .unwrap_or(&bot);

                            let mut joined =
                                if loop_heads.contains(location) && !self.config.no_widening {
                                    next_state.widen(new_next_state)
                                } else {
                                    next_state.join(new_next_state)
                                };
                            if location.statement_index == 0 {
                                joined.local.clear_dead_locals(dead_locals);
                            }
                            if !joined.ord(next_state) {
                                let next_label = Label {
                                    location: *location,
                                    writes: new_next_state.writes.clone(),
                                    nulls: new_next_state.nulls.clone(),
                                };
                                states.entry(*location).or_default().insert(
                                    (next_label.writes.clone(), next_label.nulls.clone()),
                                    joined,
                                );
                                work_list.push(next_label);
                            }
                        }
                    }
                }
                let mut restart = false;
                for next_location in next_locations {
                    for blocks in self.info.loop_blocks.values() {
                        if !blocks.contains(&next_location.block) {
                            continue;
                        }
                        let len = states[&next_location].keys().len();
                        if len > self.config.max_loop_head_states {
                            merging_blocks.extend(blocks);
                            restart = true;
                        }
                    }
                }
                if restart {
                    continue 'analysis_loop;
                }
            }
            break (states, writes_map, call_info_map);
        };

        AnalyzedBody {
            states,
            writes_map,
            init_state,
            call_info_map,
            is_merged: self.is_merged,
        }
    }

    pub fn expands_path(&self, place: &AbsPath) -> Vec<AbsPath> {
        self.info.expands_path(place)
    }

    pub fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }

    pub fn span_to_string(&self, span: Span) -> String {
        self.tcx.sess.source_map().span_to_snippet(span).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label {
    pub location: Location,
    pub writes: MustPathSet,
    pub nulls: AbsNulls,
}

#[derive(Debug)]
struct WorkList<'a> {
    rpo_map: &'a BTreeMap<BasicBlock, usize>,
    labels: BTreeMap<(usize, usize), Vec<Label>>,
}

impl<'a> WorkList<'a> {
    fn new(rpo_map: &'a BTreeMap<BasicBlock, usize>) -> Self {
        Self {
            rpo_map,
            labels: BTreeMap::new(),
        }
    }

    fn pop(&mut self) -> Option<Label> {
        let mut entry = self.labels.first_entry()?;
        let labels = entry.get_mut();
        let label = labels.pop().unwrap();
        if labels.is_empty() {
            entry.remove();
        }
        Some(label)
    }

    fn push(&mut self, label: Label) {
        let block_idx = self.rpo_map[&label.location.block];
        let labels = self
            .labels
            .entry((block_idx, label.location.statement_index))
            .or_default();
        if !labels.contains(&label) {
            labels.push(label)
        }
    }

    fn remove_location(&mut self, location: Location) {
        let block_idx = self.rpo_map[&location.block];
        self.labels.remove(&(block_idx, location.statement_index));
    }

    #[allow(unused)]
    fn len(&self) -> usize {
        self.labels.values().map(|v| v.len()).sum()
    }
}

// structs and functions used computing the FuncInfos
#[derive(Debug, Clone)]
struct FuncInfo {
    inputs: usize,
    param_tys: IndexVec<Local, TypeInfo>,
    loop_blocks: BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
    rpo_map: BTreeMap<BasicBlock, usize>,
    dead_locals: IndexVec<BasicBlock, DenseBitSet<Local>>,
    fn_ptr: bool,
    globals: FxHashSet<DefId>,
}

impl FuncInfo {
    fn expands_path(&self, place: &AbsPath) -> Vec<AbsPath> {
        if let Some(ty) = self.param_tys.get(place.base) {
            if let TypeInfo::Struct(fields) = ty {
                expand_projections(&place.projections, fields, vec![])
                    .into_iter()
                    .map(|projections| AbsPath::new(place.base, projections))
                    .collect()
            } else {
                vec![AbsPath::new(place.base, vec![])]
            }
        } else {
            vec![]
        }
    }
}

fn expand_projections(
    projections: &[FieldIdx],
    tys: &IndexVec<FieldIdx, TypeInfo>,
    mut curr: Vec<FieldIdx>,
) -> Vec<Vec<FieldIdx>> {
    if let Some(first) = projections.first() {
        curr.push(*first);
        if let Some(ty) = tys.get(*first) {
            if let TypeInfo::Struct(fields) = ty {
                expand_projections(&projections[1..], fields, curr)
            } else {
                vec![curr]
            }
        } else {
            vec![]
        }
    } else {
        tys.iter_enumerated()
            .flat_map(|(n, ty)| {
                let mut curr = curr.clone();
                curr.push(n);
                if let TypeInfo::Struct(fields) = ty {
                    expand_projections(projections, fields, curr)
                } else {
                    vec![curr]
                }
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeInfo {
    Struct(IndexVec<FieldIdx, TypeInfo>),
    Union,
    NonStruct,
}

impl TypeInfo {
    fn from_ty<'tcx>(ty: &Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        if let TyKind::Adt(adt_def, generic_args) = ty.kind() {
            match adt_def.adt_kind() {
                AdtKind::Struct => {
                    let variant = adt_def.variant(VariantIdx::from_usize(0));
                    let tys = variant
                        .fields
                        .iter()
                        .map(|field| Self::from_ty(&field.ty(tcx, generic_args), tcx))
                        .collect();
                    Self::Struct(tys)
                }
                AdtKind::Union => Self::Union,
                AdtKind::Enum => Self::NonStruct,
            }
        } else {
            Self::NonStruct
        }
    }
}

fn get_param_tys<'tcx>(
    body: &Body<'tcx>,
    inputs: usize,
    tcx: TyCtxt<'tcx>,
) -> IndexVec<Local, TypeInfo> {
    let mut param_tys = IndexVec::new();
    for (i, local) in body.local_decls.iter_enumerated() {
        if i.index() > inputs {
            break;
        }
        let ty = if let TyKind::RawPtr(ty, ..) = local.ty.kind() {
            TypeInfo::from_ty(ty, tcx)
        } else {
            TypeInfo::NonStruct
        };
        param_tys.push(ty);
    }
    param_tys
}

fn get_rpo_map(body: &Body<'_>) -> BTreeMap<BasicBlock, usize> {
    body.basic_blocks
        .reverse_postorder()
        .iter()
        .enumerate()
        .map(|(i, bb)| (*bb, i))
        .collect()
}

fn get_loop_blocks(
    body: &Body<'_>,
    rpo_map: &BTreeMap<BasicBlock, usize>,
) -> BTreeMap<BasicBlock, BTreeSet<BasicBlock>> {
    let dominators = body.basic_blocks.dominators();
    let loop_heads: BTreeSet<_> = body
        .basic_blocks
        .indices()
        .flat_map(|bb| {
            assert!(dominators.is_reachable(bb));
            let mut doms: Vec<_> =
                std::iter::successors(Some(bb), |&bb_| dominators.immediate_dominator(bb_))
                    .collect();
            let succs: BTreeSet<_> = body.basic_blocks.successors(bb).collect();
            doms.retain(|dom| succs.contains(dom));
            doms
        })
        .collect();
    let mut loop_heads: Vec<_> = loop_heads.into_iter().collect();
    loop_heads.sort_by_key(|bb| rpo_map[bb]);

    let succ_map: FxHashMap<_, FxHashSet<_>> = body
        .basic_blocks
        .indices()
        .map(|bb| (bb, body.basic_blocks.successors(bb).collect()))
        .collect();
    let mut inv_map = graph_util::inverse(&succ_map);
    loop_heads
        .into_iter()
        .map(|head| {
            let reachables = graph_util::reachable_vertices(&inv_map, head);
            for succs in inv_map.values_mut() {
                succs.remove(&head);
            }
            let loop_blocks = body
                .basic_blocks
                .indices()
                .filter(|bb| dominators.dominates(head, *bb) && reachables.contains(bb))
                .collect();
            (head, loop_blocks)
        })
        .collect()
}

fn compute_rpo_map(
    body: &Body<'_>,
    loop_blocks: &BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
) -> BTreeMap<BasicBlock, usize> {
    fn traverse(
        current: BasicBlock,
        visited: &mut BTreeSet<BasicBlock>,
        po: &mut Vec<BasicBlock>,
        body: &Body<'_>,
        loop_blocks: &BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
    ) {
        if visited.contains(&current) {
            return;
        }
        visited.insert(current);
        let loops: Vec<_> = loop_blocks
            .values()
            .filter(|blocks| blocks.contains(&current))
            .collect();
        let mut succs: Vec<_> = body.basic_blocks.successors(current).collect();
        succs.sort_by_key(|succ| loops.iter().filter(|blocks| blocks.contains(succ)).count());
        for succ in succs {
            traverse(succ, visited, po, body, loop_blocks);
        }
        po.push(current);
    }
    let mut visited = BTreeSet::new();
    let mut rpo = vec![];
    traverse(
        BasicBlock::from_usize(0),
        &mut visited,
        &mut rpo,
        body,
        loop_blocks,
    );
    rpo.reverse();
    rpo.into_iter().enumerate().map(|(i, bb)| (bb, i)).collect()
}

fn get_dead_locals<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> IndexVec<BasicBlock, DenseBitSet<Local>> {
    let mut borrowed_locals = rustc_mir_dataflow::impls::borrowed_locals(body);
    borrowed_locals.insert(Local::from_usize(0));
    let mut cursor = rustc_mir_dataflow::impls::MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    body.basic_blocks
        .indices()
        .map(|bb| {
            cursor.seek_to_block_start(bb);
            let live_locals = cursor.get();
            let mut borrowed_or_live_locals = borrowed_locals.clone();
            borrowed_or_live_locals.union(live_locals);
            let mut dead_locals = DenseBitSet::new_filled(body.local_decls.len());
            dead_locals.subtract(&borrowed_or_live_locals);
            dead_locals
        })
        .collect()
}

// MIR, HIR Visitors
struct CallVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    callees: FxHashSet<DefId>,
}

impl<'tcx> CallVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callees: FxHashSet::default(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for CallVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, _) = expr.kind
            && let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind
            && let Res::Def(DefKind::Fn, def_id) = path.res
        {
            self.callees.insert(def_id);
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

struct FnPtrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    callees: FxHashSet<HirId>,
    fn_ptrs: FxHashSet<DefId>,
}

impl<'tcx> FnPtrVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callees: FxHashSet::default(),
            fn_ptrs: FxHashSet::default(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for FnPtrVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call(callee, _) => {
                self.callees.insert(callee.hir_id);
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if !self.callees.contains(&expr.hir_id)
                    && let Res::Def(def_kind, def_id) = path.res
                    && def_kind.is_fn_like()
                {
                    self.fn_ptrs.insert(def_id);
                }
            }
            _ => {}
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

enum StatementCheck {
    None,
    UseExist,
    Overwritten,
}

struct LocalVisitor<'tcx> {
    _tcx: TyCtxt<'tcx>,
    local: Local,
    check_result: StatementCheck,
}

impl<'tcx> LocalVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, local: Local) -> Self {
        Self {
            _tcx: tcx,
            local,
            check_result: StatementCheck::None,
        }
    }

    fn clear(&mut self) {
        self.check_result = StatementCheck::None;
    }
}

impl<'tcx> MVisitor<'tcx> for LocalVisitor<'tcx> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if self.local == local {
            match context {
                PlaceContext::MutatingUse(MutatingUseContext::Store)
                | PlaceContext::MutatingUse(MutatingUseContext::Call)
                | PlaceContext::MutatingUse(MutatingUseContext::AsmOutput)
                | PlaceContext::MutatingUse(MutatingUseContext::Yield) => {
                    self.check_result = StatementCheck::Overwritten;
                }
                PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy)
                | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
                | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection)
                | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow)
                | PlaceContext::MutatingUse(MutatingUseContext::Borrow)
                | PlaceContext::MutatingUse(MutatingUseContext::RawBorrow) => {
                    self.check_result = StatementCheck::UseExist;
                }
                _ => {
                    self.check_result = StatementCheck::None;
                }
            }
        }
    }
}

struct GlobalVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    globals: FxHashSet<DefId>,
}

impl<'tcx> GlobalVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            globals: FxHashSet::default(),
        }
    }
}

impl<'tcx> MVisitor<'tcx> for GlobalVisitor<'tcx> {
    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _location: Location) {
        if let Const::Val(ConstValue::Scalar(Scalar::Ptr(ptr, _)), _) = constant.const_
            && let GlobalAlloc::Static(def_id) = self.tcx.global_alloc(ptr.provenance.alloc_id())
        {
            self.globals.insert(def_id);
        }
    }

    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        let StatementKind::Assign(box (_l, r)) = &stmt.kind else {
            return;
        };
        if let Rvalue::ThreadLocalRef(def_id) = r {
            self.globals.insert(*def_id);
        }
        self.super_statement(stmt, location);
    }
}

// For debugging
fn analysis_result_to_string(
    body: &Body<'_>,
    states: &BTreeMap<Location, BTreeMap<(MustPathSet, AbsNulls), AbsState>>,
    source_map: &SourceMap,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut res = String::new();
    for block in body.basic_blocks.indices() {
        let bbd = &body.basic_blocks[block];
        writeln!(&mut res, "block {block:?}")?;
        for (statement_index, stmt) in bbd.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if let Some(states) = states.get(&location) {
                for state in states.values() {
                    writeln!(&mut res, "{state:?}")?;
                }
            }
            writeln!(&mut res, "{stmt:?}")?;
            if let Ok(s) = source_map.span_to_snippet(stmt.source_info.span) {
                writeln!(&mut res, "{s}")?;
            }
        }
        if let Some(terminator) = bbd.terminator.as_ref() {
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            if let Some(states) = states.get(&location) {
                for state in states.values() {
                    writeln!(&mut res, "{state:?}")?;
                }
            }
            writeln!(&mut res, "{terminator:?}")?;
            if let Ok(s) = source_map.span_to_snippet(terminator.source_info.span) {
                writeln!(&mut res, "{s}")?;
            }
        }
    }
    Ok(res)
}
