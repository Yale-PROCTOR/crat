use etrace::some_or;
use rustc_ast::UnOp;
use rustc_data_structures::fx::FxHashSet;
use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, ItemKind, Node, PatKind, QPath,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_index::Idx;
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, Const, Operand, TerminatorKind},
    query::IntoQueryParam,
    ty::{self, TyCtxt},
};
use rustc_span::{Span, Symbol};
use typed_arena::Arena;
use utils::file::api_list;

use super::mir_loc::MirLoc;

pub(super) fn analyze<'a>(arena: &'a Arena<ExprLoc>, tcx: TyCtxt<'_>) -> AnalysisResult<'a> {
    let mut result = AnalysisResult::default();

    let mut visitor = HirVisitor::new(arena, tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    for def_id in &visitor.ctx.error_handling_fns {
        let body = tcx.optimized_mir(*def_id);

        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            let term = bbd.terminator();
            let TerminatorKind::Call { func, args, .. } = &term.kind else { continue };

            let handle_callee = some_or!(operand_to_def_id(func), continue);
            let indicator = some_or!(handling_api_indicator(handle_callee, tcx), continue);

            let place = args[0].node.place().unwrap();
            let hir_loc = MirLoc::Var(*def_id, place.local);

            let span = term.source_info.span;
            let func = *def_id;
            let loc = visitor.ctx.call_span_to_args[&span][0].as_ref().unwrap();

            let label = Label::new(func, bb, loc);
            let sink_result = analyze_sink(label, FxHashSet::default(), arena, &visitor.ctx, tcx);
            result.visit_nums.push(sink_result.visited_fns.len());

            if sink_result.sources.is_empty() {
                result.no_source_locs.push(hir_loc);
                continue;
            }

            let mut loc_result = LocAnalysisResult::default();
            loc_result.add_tracking_fn(label.func_loc, indicator);

            if sink_result.call_graph.is_empty() {
                result.loc_results.push((hir_loc, loc_result));
                continue;
            }

            for (caller, callees) in &sink_result.call_graph {
                for callee in callees {
                    loc_result.propagations.insert(ErrorPropagation {
                        caller: *caller,
                        callee: *callee,
                    });
                }
            }

            let mut call_graph = sink_result.call_graph;
            let mut nodes: FxHashSet<FuncLoc<'_>> = FxHashSet::default();
            for succs in call_graph.values() {
                nodes.extend(succs.iter().filter(|succ| !call_graph.contains_key(succ)));
            }
            for node in nodes {
                assert!(call_graph.insert(node, FxHashSet::default()).is_none());
            }
            let transitive_call_graph = utils::graph::transitive_closure(&call_graph);
            let inv_call_graph = utils::graph::inverse(&call_graph);
            let transitive_inv_call_graph = utils::graph::transitive_closure(&inv_call_graph);

            if inv_call_graph[&label.func_loc].is_empty() {
                let source_reachables: FxHashSet<_> = sink_result
                    .sources
                    .iter()
                    .flat_map(|source| &transitive_inv_call_graph[source])
                    .chain(&sink_result.sources)
                    .copied()
                    .collect();
                for l in &transitive_call_graph[&label.func_loc] {
                    if source_reachables.contains(l) {
                        loc_result.add_returning_fn(*l, indicator);
                    }
                }
            } else {
                let sink_reachables = &transitive_inv_call_graph[&label.func_loc];
                for source in sink_result.sources {
                    let source_reachables = &transitive_inv_call_graph[&source];
                    for caller in sink_reachables {
                        if *caller != source && !source_reachables.contains(caller) {
                            continue;
                        }
                        loc_result.add_tracking_fn(*caller, indicator);

                        for l in &transitive_call_graph[caller] {
                            if *l == source || source_reachables.contains(l) {
                                loc_result.add_returning_fn(*l, indicator);
                            }
                            if *l == label.func_loc || sink_reachables.contains(l) {
                                loc_result.add_taking_fn(*l, indicator);
                            }
                        }
                    }
                }
            }

            result.loc_results.push((hir_loc, loc_result));
        }
    }

    result.span_to_loc = visitor.ctx.span_to_loc;
    result
}

#[derive(Debug, Default)]
pub(super) struct AnalysisResult<'a> {
    pub(super) no_source_locs: Vec<MirLoc>,
    pub(super) span_to_loc: FxHashMap<Span, &'a ExprLoc>,
    pub(super) loc_results: Vec<(MirLoc, LocAnalysisResult<'a>)>,
    pub(super) visit_nums: Vec<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct ErrorPropagation<'a> {
    pub(super) caller: FuncLoc<'a>,
    pub(super) callee: FuncLoc<'a>,
}

impl<'a> ErrorPropagation<'a> {
    #[inline]
    pub(super) fn new(
        caller_func: LocalDefId,
        caller_loc: &'a ExprLoc,
        callee_func: LocalDefId,
        callee_loc: &'a ExprLoc,
    ) -> Self {
        Self {
            caller: FuncLoc::new(caller_func, caller_loc),
            callee: FuncLoc::new(callee_func, callee_loc),
        }
    }
}

#[derive(Debug, Default)]
pub(super) struct LocAnalysisResult<'a> {
    pub(super) tracking_fns: FxHashMap<LocalDefId, FxHashSet<(&'a ExprLoc, Indicator)>>,
    pub(super) returning_fns: FxHashMap<LocalDefId, FxHashSet<(&'a ExprLoc, Indicator)>>,
    pub(super) taking_fns: FxHashMap<LocalDefId, FxHashSet<(&'a ExprLoc, Indicator)>>,
    pub(super) propagations: FxHashSet<ErrorPropagation<'a>>,
}

impl<'a> LocAnalysisResult<'a> {
    #[inline]
    fn add_tracking_fn(&mut self, func_loc: FuncLoc<'a>, indicator: Indicator) {
        self.tracking_fns
            .entry(func_loc.func)
            .or_default()
            .insert((func_loc.loc, indicator));
    }

    #[inline]
    fn add_returning_fn(&mut self, func_loc: FuncLoc<'a>, indicator: Indicator) {
        self.returning_fns
            .entry(func_loc.func)
            .or_default()
            .insert((func_loc.loc, indicator));
        self.add_tracking_fn(func_loc, indicator);
    }

    #[inline]
    fn add_taking_fn(&mut self, func_loc: FuncLoc<'a>, indicator: Indicator) {
        self.taking_fns
            .entry(func_loc.func)
            .or_default()
            .insert((func_loc.loc, indicator));
        self.add_tracking_fn(func_loc, indicator);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(super) enum Indicator {
    Error,
    Eof,
}

impl Indicator {
    pub(super) const NUM: usize = 2;
}

impl Idx for Indicator {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx >= Self::NUM {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

impl std::fmt::Display for Indicator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Indicator::Error => write!(f, "error"),
            Indicator::Eof => write!(f, "eof"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Label<'a> {
    func_loc: FuncLoc<'a>,
    bb: BasicBlock,
}

impl<'a> Label<'a> {
    #[inline]
    fn new(func: LocalDefId, bb: BasicBlock, loc: &'a ExprLoc) -> Self {
        Self {
            func_loc: FuncLoc::new(func, loc),
            bb,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct FuncLoc<'a> {
    pub(super) func: LocalDefId,
    pub(super) loc: &'a ExprLoc,
}

impl<'a> FuncLoc<'a> {
    #[inline]
    fn new(func: LocalDefId, loc: &'a ExprLoc) -> Self {
        Self { func, loc }
    }
}

#[derive(Debug, Clone)]
struct SinkResult<'a> {
    sources: Vec<FuncLoc<'a>>,
    call_graph: FxHashMap<FuncLoc<'a>, FxHashSet<FuncLoc<'a>>>,
    visited_fns: FxHashSet<LocalDefId>,
}

fn analyze_sink<'a>(
    sink_label: Label<'a>,
    mut analyzed_labels: FxHashSet<Label<'a>>,
    arena: &'a Arena<ExprLoc>,
    ctx: &HirCtx<'a>,
    tcx: TyCtxt<'_>,
) -> SinkResult<'a> {
    analyzed_labels.insert(sink_label);
    let callers = ctx.callee_to_callers.get(&sink_label.func_loc.func);
    let used_as_fn_ptr = ctx.ptr_used_fns.contains(&sink_label.func_loc.func);

    let mut worklist = vec![sink_label];
    let mut visited = FxHashSet::default();
    let mut func_to_return_bb = FxHashMap::default();
    let mut sources = vec![];
    let mut call_graph: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    let mut fn_ptr_call = false;
    let mut visited_fns = FxHashSet::default();

    'l: while let Some(label) = worklist.pop() {
        if !visited.insert(label) {
            continue;
        }
        visited_fns.insert(label.func_loc.func);

        let body = tcx.optimized_mir(label.func_loc.func);
        let bbd = &body.basic_blocks[label.bb];
        let term = bbd.terminator();

        if let TerminatorKind::Call { func, .. } = &term.kind
            && let Some(args) = ctx.call_span_to_args.get(&term.source_info.span)
        {
            for (i, arg) in args.iter().enumerate() {
                let arg = some_or!(arg, continue);
                if !arg.is_prefix_of(label.func_loc.loc) {
                    continue;
                }

                if let Some(callee) = operand_to_def_id(func) {
                    if !api_list::is_def_id_api(callee, tcx) {
                        // intra call
                        let return_bb = *func_to_return_bb.entry(callee).or_insert_with(|| {
                            let body = tcx.optimized_mir(callee);
                            for (bb, bbd) in body.basic_blocks.iter_enumerated().rev() {
                                let term = bbd.terminator();
                                if matches!(term.kind, TerminatorKind::Return) {
                                    return bb;
                                }
                            }
                            panic!()
                        });
                        let node = tcx.hir_get_if_local(callee.to_def_id()).unwrap();
                        let Node::Item(item) = node else { panic!() };
                        let ItemKind::Fn { body, .. } = item.kind else { panic!() };
                        let body = tcx.hir_body(body);
                        let param = &body.params[i];
                        let PatKind::Binding(_, id, _, _) = param.pat.kind else { panic!() };
                        let base = ExprBase::Local(id);
                        let new_arg = arena.alloc(label.func_loc.loc.subst_prefix(base, arg));
                        let new_label = Label::new(callee, return_bb, new_arg);
                        call_graph
                            .entry(label.func_loc)
                            .or_default()
                            .insert(new_label.func_loc);
                        worklist.push(new_label);
                    } else if handling_api_indicator(callee, tcx).is_none() {
                        // api call
                        sources.push(label.func_loc);
                        continue 'l;
                    }
                } else {
                    fn_ptr_call = true;
                    sources.clear();
                    break 'l;
                }
            }
        }

        let predecessors = body.basic_blocks.predecessors();
        for pred in &predecessors[label.bb] {
            let label = Label { bb: *pred, ..label };
            worklist.push(label);
        }
    }

    if let ExprBase::Local(hir_id) = sink_label.func_loc.loc.base
        && let Some(param_idx) = ctx.param_indices.get(&hir_id)
        && let Some(callers) = callers
        && !fn_ptr_call
        && !used_as_fn_ptr
        && sources.is_empty()
    {
        let mut failed = false;

        'l: for caller in callers {
            let body = tcx.optimized_mir(*caller);

            for (bb, bbd) in body.basic_blocks.iter_enumerated() {
                let term = bbd.terminator();
                let TerminatorKind::Call { func, .. } = &term.kind else { continue };
                let callee = some_or!(operand_to_def_id(func), continue);
                if callee != sink_label.func_loc.func {
                    continue;
                }

                let args = &ctx.call_span_to_args[&term.source_info.span];
                let arg = args[*param_idx].as_ref().unwrap();
                let loc = sink_label.func_loc.loc.change_base(arg);
                let caller_label = Label::new(*caller, bb, arena.alloc(loc));
                call_graph
                    .entry(caller_label.func_loc)
                    .or_default()
                    .insert(sink_label.func_loc);

                if !analyzed_labels.contains(&caller_label) {
                    let res = analyze_sink(caller_label, analyzed_labels.clone(), arena, ctx, tcx);
                    visited_fns.extend(res.visited_fns);
                    if !res.sources.is_empty() {
                        sources.extend(res.sources);
                        for (caller, callees) in res.call_graph {
                            call_graph.entry(caller).or_default().extend(callees);
                        }
                        continue;
                    }
                }

                failed = true;
                break 'l;
            }
        }

        if failed {
            sources.clear();
        }
    }

    SinkResult {
        sources,
        call_graph,
        visited_fns,
    }
}

#[inline]
fn handling_api_indicator(
    def_id: impl IntoQueryParam<DefId>,
    tcx: TyCtxt<'_>,
) -> Option<Indicator> {
    let name = utils::ir::def_id_to_symbol(def_id, tcx).unwrap();
    let name = api_list::normalize_api_name(name.as_str());
    match name {
        "ferror" => Some(Indicator::Error),
        "feof" => Some(Indicator::Eof),
        _ => None,
    }
}

fn operand_to_def_id(op: &Operand<'_>) -> Option<LocalDefId> {
    let constant = op.constant()?;
    let Const::Val(_, ty) = constant.const_ else { unreachable!() };
    let ty::TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
    def_id.as_local()
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct ExprLoc {
    base: ExprBase,
    projections: Vec<ExprProj>,
}

impl std::fmt::Debug for ExprLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.base)?;
        for proj in &self.projections {
            write!(f, "{proj:?}")?;
        }
        Ok(())
    }
}

impl std::fmt::Display for ExprLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.base)?;
        for proj in &self.projections {
            write!(f, "_{proj}")?;
        }
        Ok(())
    }
}

impl ExprLoc {
    fn is_prefix_of(&self, other: &Self) -> bool {
        self.base == other.base
            && self.projections.len() <= other.projections.len()
            && self
                .projections
                .iter()
                .zip(&other.projections)
                .all(|(a, b)| a == b)
    }

    fn subst_prefix(&self, base: ExprBase, prefix: &Self) -> Self {
        assert!(prefix.is_prefix_of(self));
        Self {
            base,
            projections: self.projections[prefix.projections.len()..].to_vec(),
        }
    }

    fn change_base(&self, new: &Self) -> Self {
        let projections = new
            .projections
            .iter()
            .chain(&self.projections)
            .cloned()
            .collect();
        Self {
            base: new.base,
            projections,
        }
    }

    #[allow(unused)]
    #[inline]
    fn is_std(&self) -> bool {
        self.base.is_std()
    }

    #[allow(unused)]
    #[inline]
    fn is_global(&self) -> bool {
        self.base.is_global()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ExprBase {
    Stdin,
    Stdout,
    Stderr,
    Global(LocalDefId),
    Local(HirId),
}

impl std::fmt::Debug for ExprBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprBase::Stdin => write!(f, "stdin"),
            ExprBase::Stdout => write!(f, "stdout"),
            ExprBase::Stderr => write!(f, "stderr"),
            ExprBase::Global(def_id) => utils::ir::fmt_def_id(f, *def_id),
            ExprBase::Local(hir_id) => {
                utils::ir::fmt_def_id(f, hir_id.owner)?;
                write!(f, ":{:?}", hir_id.local_id)
            }
        }
    }
}

impl std::fmt::Display for ExprBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprBase::Stdin => write!(f, "stdin"),
            ExprBase::Stdout => write!(f, "stdout"),
            ExprBase::Stderr => write!(f, "stderr"),
            ExprBase::Global(def_id) => utils::ir::with_tcx(|tcx| {
                let name = utils::ir::def_id_to_symbol(*def_id, tcx).unwrap();
                write!(f, "{name}")
            }),
            ExprBase::Local(hir_id) => utils::ir::with_tcx(|tcx| {
                let node = tcx.hir_node(*hir_id);
                let Node::Pat(pat) = node else { panic!() };
                let PatKind::Binding(_, _, name, _) = pat.kind else { panic!() };
                write!(f, "{name}")
            }),
        }
    }
}

impl ExprBase {
    #[allow(unused)]
    #[inline]
    fn is_std(self) -> bool {
        matches!(self, ExprBase::Stdin | ExprBase::Stdout | ExprBase::Stderr)
    }

    #[allow(unused)]
    #[inline]
    fn is_global(self) -> bool {
        matches!(self, ExprBase::Global(_))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ExprProj {
    Field(Symbol),
    Index,
}

impl std::fmt::Debug for ExprProj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprProj::Field(name) => write!(f, ".{name}"),
            ExprProj::Index => write!(f, "[*]"),
        }
    }
}

impl std::fmt::Display for ExprProj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprProj::Field(name) => write!(f, "{name}"),
            ExprProj::Index => write!(f, "index"),
        }
    }
}

pub(super) fn expr_to_path(mut expr: &Expr<'_>, tcx: TyCtxt<'_>) -> Option<ExprLoc> {
    let mut projections = vec![];
    loop {
        match expr.kind {
            ExprKind::Unary(UnOp::Deref, e)
            | ExprKind::AddrOf(_, _, e)
            | ExprKind::Cast(e, _)
            | ExprKind::DropTemps(e) => expr = e,
            ExprKind::Field(e, f) => {
                projections.push(ExprProj::Field(f.name));
                expr = e;
            }
            ExprKind::Index(e, _, _) => {
                projections.push(ExprProj::Index);
                expr = e;
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                let base = match path.res {
                    Res::Def(DefKind::Static { .. }, def_id) => {
                        let def_id = def_id.as_local()?;
                        let name = utils::ir::def_id_to_symbol(def_id, tcx).unwrap();
                        match name.as_str() {
                            "stdin" => ExprBase::Stdin,
                            "stdout" => ExprBase::Stdout,
                            "stderr" => ExprBase::Stderr,
                            _ => ExprBase::Global(def_id),
                        }
                    }
                    Res::Local(hir_id) => ExprBase::Local(hir_id),
                    _ => return None,
                };
                projections.reverse();
                return Some(ExprLoc { base, projections });
            }
            _ => return None,
        }
    }
}

#[derive(Debug, Default)]
struct HirCtx<'a> {
    call_span_to_args: FxHashMap<Span, Vec<Option<&'a ExprLoc>>>,
    span_to_loc: FxHashMap<Span, &'a ExprLoc>,
    error_handling_fns: FxHashSet<LocalDefId>,
    callee_to_callers: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    ptr_used_fns: FxHashSet<LocalDefId>,
    param_indices: FxHashMap<HirId, usize>,
}

struct HirVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: HirCtx<'a>,
    arena: &'a Arena<ExprLoc>,
}

impl<'a, 'tcx> HirVisitor<'a, 'tcx> {
    fn new(arena: &'a Arena<ExprLoc>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            ctx: HirCtx::default(),
            arena,
        }
    }
}

impl<'tcx> Visitor<'tcx> for HirVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_body(&mut self, body: &rustc_hir::Body<'tcx>) {
        intravisit::walk_body(self, body);

        for (i, param) in body.params.iter().enumerate() {
            let PatKind::Binding(_, hir_id, _, _) = param.pat.kind else { continue };
            self.ctx.param_indices.insert(hir_id, i);
        }
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        intravisit::walk_expr(self, expr);

        match expr.kind {
            ExprKind::Call(path, args) => {
                let mut v = vec![];
                for arg in args {
                    let loc = expr_to_path(arg, self.tcx).map(|loc| &*self.arena.alloc(loc));
                    v.push(loc);
                    if let Some(loc) = loc {
                        self.ctx.span_to_loc.insert(arg.span, loc);
                    }
                }
                if !v.is_empty() {
                    self.ctx.call_span_to_args.insert(expr.span, v);
                }

                let ExprKind::Path(QPath::Resolved(_, path)) = path.kind else { return };
                let Res::Def(DefKind::Fn, def_id) = path.res else { return };
                let curr_fn = expr.hir_id.owner.def_id;
                if handling_api_indicator(def_id, self.tcx).is_some() {
                    self.ctx.error_handling_fns.insert(curr_fn);
                }
                let def_id = some_or!(def_id.as_local(), return);
                self.ctx
                    .callee_to_callers
                    .entry(def_id)
                    .or_default()
                    .insert(curr_fn);
            }
            ExprKind::Assign(lhs, _, _) => {
                let loc = expr_to_path(lhs, self.tcx).map(|loc| &*self.arena.alloc(loc));
                if let Some(loc) = loc {
                    self.ctx.span_to_loc.insert(lhs.span, loc);
                }
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                let Res::Def(DefKind::Fn, def_id) = path.res else { return };
                let def_id = some_or!(def_id.as_local(), return);
                let mut parents = self.tcx.hir_parent_iter(expr.hir_id);
                let (_, parent) = parents.next().unwrap();
                let Node::Expr(parent) = parent else { panic!() };
                if let ExprKind::Call(callee, _) = parent.kind
                    && callee.hir_id == expr.hir_id
                {
                    return;
                }
                self.ctx.ptr_used_fns.insert(def_id);
            }
            _ => {}
        }
    }
}
