use std::{cell::RefCell, collections::hash_map::Entry};

use etrace::some_or;
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, QPath, def::Res};
use rustc_index::{Idx, IndexVec, bit_set::ChunkedBitSet};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Const, ConstValue, Local, LocalDecl, Location, Operand,
        Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
        interpret::{GlobalAlloc, Scalar},
        visit::Visitor,
    },
    ty::{GenericArgKind, Ty, TyCtxt, TyKind},
};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    source_map::Spanned,
};
use serde::Deserialize;
use typed_arena::Arena;
use utils::{
    graph::{self, SccId},
    ty_shape::{self, TyShape, TyShapes},
};

use super::alloc_finder;

#[derive(Debug, Default, Deserialize)]
pub struct Config {
    #[serde(default)]
    pub use_optimized_mir: bool,
    pub c_exposed_fns: FxHashSet<String>,
}

pub fn run_analysis(config: &Config, tcx: TyCtxt<'_>) -> Solutions {
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx, config.use_optimized_mir);
    let pre = pre_analyze(config, &tss, tcx);
    analyze(config, &pre, &tss, tcx)
}

pub fn write_solutions<W: std::io::Write>(mut w: W, solutions: &Solutions) -> std::io::Result<()> {
    for (i, bitset) in solutions.iter_enumerated() {
        for loc in bitset.iter() {
            let mut loc = loc.index();
            while loc > 0 {
                let v = (loc & 127) as u8;
                w.write_all(&[v])?;
                loc >>= 7;
            }
            w.write_all(&[254])?;
        }
        if i + 1 < solutions.next_index() {
            w.write_all(&[255])?;
        }
    }
    Ok(())
}

pub fn serialize_solutions(solutions: &Solutions) -> Vec<u8> {
    let mut arr = vec![];
    write_solutions(&mut arr, solutions).unwrap();
    arr
}

pub fn deserialize_solutions(arr: &[u8]) -> Solutions {
    let size = arr.iter().filter(|n| **n == 255).count() + 1;
    let mut solutions: Solutions = IndexVec::from_raw(vec![ChunkedBitSet::new_empty(size)]);
    let mut s = &mut solutions[Loc::ZERO];
    let mut i = 0;
    let mut len = 0;
    for n in arr {
        match *n {
            255 => {
                solutions.push(ChunkedBitSet::new_empty(size));
                s = solutions.raw.last_mut().unwrap();
            }
            254 => {
                s.insert(Loc::from_usize(i));
                i = 0;
                len = 0;
            }
            n => {
                i |= (n as usize) << len;
                len += 7;
            }
        }
    }
    solutions
}

#[derive(Debug)]
pub struct BodyItem {
    local_def_id: LocalDefId,
    is_fn: bool,
}

#[derive(Debug)]
pub struct IndexInfo<'tcx> {
    pub ends: IndexVec<Loc, Loc>,
    tys: IndexVec<Loc, Ty<'tcx>>,
    owners: IndexVec<Loc, LocalDefId>,
}

impl<'tcx> IndexInfo<'tcx> {
    fn new() -> Self {
        IndexInfo {
            ends: IndexVec::new(),
            tys: IndexVec::new(),
            owners: IndexVec::new(),
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        assert!(self.ends.len() == self.tys.len());
        assert!(self.ends.len() == self.owners.len());
        self.ends.len()
    }

    pub fn next_index(&self) -> Loc {
        assert!(self.ends.len() == self.tys.len());
        assert!(self.ends.len() == self.owners.len());
        self.ends.next_index()
    }

    fn push(&mut self, end: Loc, ty: Ty<'tcx>, owner: LocalDefId) {
        self.ends.push(end);
        self.tys.push(ty);
        self.owners.push(owner);
    }

    pub fn get_end(&self, index: Loc) -> Loc {
        self.ends[index]
    }

    pub fn get_ty(&self, index: Loc) -> Ty<'tcx> {
        self.tys[index]
    }

    pub fn get_owner(&self, index: Loc) -> LocalDefId {
        self.owners[index]
    }

    fn modify_end(&mut self, index: Loc, new: Loc) {
        self.ends[index] = new;
    }

    fn modify_ty(&mut self, index: Loc, new: Ty<'tcx>) {
        self.tys[index] = new;
    }

    pub fn iter(&self) -> impl Iterator<Item = (Loc, Ty<'tcx>)> + '_ {
        self.ends.iter().copied().zip(self.tys.iter().copied())
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (Loc, (Loc, Ty<'tcx>))> + '_ {
        self.ends
            .iter_enumerated()
            .zip(self.tys.iter())
            .map(|((i, l), t)| (i, (*l, *t)))
    }
}

#[derive(Debug)]
pub struct PreAnalysisData<'tcx> {
    pub bodies: Vec<BodyItem>,
    pub alloc_fns: FxHashSet<LocalDefId>,

    pub call_graph: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    pub call_args: FxHashMap<LocalDefId, Vec<Vec<Option<Loc>>>>,
    pub indirect_calls: FxHashMap<LocalDefId, FxHashMap<BasicBlock, Loc>>,

    pub index_info: IndexInfo<'tcx>,
    pub globals: FxHashMap<LocalDefId, Loc>,
    pub non_fn_globals: FxHashSet<Loc>,
    pub inv_fns: FxHashMap<Loc, LocalDefId>,
    pub vars: FxHashMap<Var, Loc>,

    pub index_prefixes: FxHashMap<Loc, u8>,
    pub union_offsets: FxHashMap<Loc, Vec<usize>>,
    pub graph: LocGraph,
    pub var_nodes: FxHashMap<(LocalDefId, Local), LocNode>,

    pub exposed_fn_arg_vars: Vec<Var>,
}

pub type Solutions = IndexVec<Loc, ChunkedBitSet<Loc>>;

pub struct AnalysisResult {
    pub ends: IndexVec<Loc, Loc>,
    pub union_offsets: FxHashMap<Loc, Vec<usize>>,
    pub graph: LocGraph,
    pub var_nodes: FxHashMap<(LocalDefId, Local), LocNode>,

    pub solutions: Solutions,

    pub indirect_calls: FxHashMap<LocalDefId, FxHashMap<BasicBlock, Vec<LocalDefId>>>,
    pub call_graph_sccs: graph::Sccs<LocalDefId, false>,
    pub reachables: RefCell<FxHashMap<SccId, FxHashSet<SccId>>>,

    pub writes: FxHashMap<LocalDefId, FxHashMap<Location, ChunkedBitSet<Loc>>>,
    pub bitfield_writes: FxHashMap<LocalDefId, FxHashMap<Location, ChunkedBitSet<Loc>>>,
    pub fn_writes: FxHashMap<LocalDefId, ChunkedBitSet<Loc>>,
}

pub fn pre_analyze<'a, 'tcx>(
    config: &Config,
    tss: &'a TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> PreAnalysisData<'tcx> {
    let alloc_fns = alloc_finder::find_alloc_funcs(config, tcx);

    let mut bodies = vec![];
    let mut fn_def_ids = FxHashSet::default();
    let mut visitor = FnPtrVisitor::new(tcx);
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        match item.kind {
            ItemKind::Fn { ident, .. } if ident.name.as_str() != "main" => {
                fn_def_ids.insert(local_def_id);
                let body = if config.use_optimized_mir {
                    tcx.optimized_mir(def_id)
                } else {
                    &tcx.mir_drops_elaborated_and_const_checked(local_def_id)
                        .borrow()
                };
                visitor.visit_body(body);
                let body_item = BodyItem {
                    local_def_id,
                    is_fn: true,
                };
                bodies.push(body_item);
            }
            ItemKind::Static(_, _, _, _) => {
                let body = if config.use_optimized_mir {
                    tcx.mir_for_ctfe(def_id)
                } else {
                    &tcx.mir_drops_elaborated_and_const_checked(local_def_id)
                        .borrow()
                };
                visitor.visit_body(body);
                let body_item = BodyItem {
                    local_def_id,
                    is_fn: false,
                };
                bodies.push(body_item);
            }
            _ => {}
        }
    }
    let mut call_graph: FxHashMap<_, _> = fn_def_ids
        .iter()
        .map(|f| (*f, FxHashSet::default()))
        .collect();
    let fn_ptrs = visitor.fn_ptrs;

    let mut globals = FxHashMap::default();
    let mut non_fn_globals = FxHashSet::default();
    let mut inv_fns = FxHashMap::default();
    let mut vars = FxHashMap::default();
    let mut index_info = IndexInfo::new();
    let mut alloc_info = IndexInfo::new();
    let mut allocs = vec![];
    let mut graph = FxHashMap::default();
    let mut union_offsets = FxHashMap::default();
    let mut index_prefixes = FxHashMap::default();
    let mut exposed_fn_args = vec![];

    let mut indirect_calls: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
    let mut call_args: FxHashMap<_, Vec<Vec<_>>> = FxHashMap::default();
    let mut var_nodes = FxHashMap::default();
    for item in &bodies {
        let body = if !config.use_optimized_mir {
            // use MIR before optimization
            &tcx.mir_drops_elaborated_and_const_checked(item.local_def_id)
                .borrow()
        } else if item.is_fn {
            // if item is a function, use optimized MIR
            tcx.optimized_mir(item.local_def_id.to_def_id())
        } else {
            // if item is a static, use MIR for CTFE
            tcx.mir_for_ctfe(item.local_def_id.to_def_id())
        };
        let fn_ptr = fn_ptrs.contains(&item.local_def_id);
        let global_index = index_info.next_index();
        globals.insert(item.local_def_id, global_index);

        if item.is_fn {
            inv_fns.insert(global_index, item.local_def_id);
        }
        let exposed = item.is_fn
            && config
                .c_exposed_fns
                .contains(tcx.item_name(item.local_def_id.to_def_id()).as_str());
        let mut args = vec![];

        let mut local_decls = body.local_decls.iter_enumerated();
        let ret = local_decls.next().unwrap();
        let mut params = vec![];
        for _ in 0..body.arg_count {
            params.push(local_decls.next().unwrap());
        }
        let local_decls = params
            .into_iter()
            .chain(std::iter::once(ret))
            .chain(local_decls);

        for (local, local_decl) in local_decls {
            vars.insert(
                Var::Local(item.local_def_id, local),
                index_info.next_index(),
            );
            let ty = tss.tys[&local_decl.ty];
            let node = add_edges(
                ty,
                index_info.next_index(),
                &mut graph,
                &mut index_prefixes,
                &mut union_offsets,
            );
            var_nodes.insert((item.local_def_id, local), node);
            compute_ends(ty, &mut index_info, item.local_def_id);

            if fn_ptr && local.index() == 0 {
                index_info.modify_end(global_index, Loc::from_usize(index_info.len() - 1));
            }

            if let Some(ty) = ty_shape::unwrap_ptr(local_decl.ty) {
                let mut index_info = IndexInfo::new();
                let ty = tss.tys[&ty];
                compute_ends(ty, &mut index_info, item.local_def_id);
                for (i, (end, pty)) in index_info.iter_enumerated() {
                    if alloc_info.next_index() > i {
                        let prev_end = alloc_info.get_end(i);
                        if prev_end < end {
                            alloc_info.modify_end(i, end);
                            alloc_info.modify_ty(i, pty);
                        }
                    } else {
                        alloc_info.push(end, pty, item.local_def_id);
                    }
                }
            }

            if exposed
                && (1..=body.arg_count).contains(&local.index())
                && let ty = match local_decl.ty.kind() {
                    TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(ty),
                    TyKind::Adt(adt_def, gargs)
                        if tcx.item_name(adt_def.did()) == rustc_span::sym::Option =>
                    {
                        let GenericArgKind::Type(ty) = gargs[0].kind() else { panic!() };
                        if let TyKind::Ref(_, ty, _) = ty.kind() {
                            Some(ty)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
                && let Some(ty) = ty
            {
                args.push((local, ty));
            }
        }

        if !args.is_empty() {
            exposed_fn_args.push((item.local_def_id, args));
        }

        if !item.is_fn {
            non_fn_globals.extend(global_index..=(index_info.get_end(global_index)));
        }

        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &bbd.terminator().kind
            else {
                continue;
            };
            match func {
                Operand::Copy(func) | Operand::Move(func) => {
                    assert!(func.projection.is_empty());
                    let var = Var::Local(item.local_def_id, func.local);
                    let index = vars[&var];
                    indirect_calls
                        .entry(item.local_def_id)
                        .or_default()
                        .insert(bb, index);
                }
                _ => {
                    let def_id = some_or!(operand_to_fn(func), continue);
                    let local_def_id = some_or!(def_id.as_local(), continue);
                    let ty = destination.ty(&body.local_decls, tcx).ty;
                    if ty.is_raw_ptr()
                        && (is_c_fn(def_id, tcx) || alloc_fns.contains(&local_def_id))
                    {
                        allocs.push(Var::Alloc(item.local_def_id, bb));
                    }
                    if fn_def_ids.contains(&local_def_id) {
                        call_graph
                            .get_mut(&item.local_def_id)
                            .unwrap()
                            .insert(local_def_id);
                        let args = args
                            .iter()
                            .map(|a| {
                                a.node.place().map(|p| {
                                    let var = Var::Local(item.local_def_id, p.local);
                                    vars[&var]
                                })
                            })
                            .collect();
                        call_args.entry(local_def_id).or_default().push(args)
                    }
                }
            }
        }
    }

    for alloc in allocs {
        let len = index_info.next_index();
        vars.insert(alloc, len);
        for (end, ty) in alloc_info.iter() {
            let Var::Alloc(alloc_def_id, _) = alloc else { unreachable!() };

            index_info.push(len + end.index(), ty, alloc_def_id);
        }
    }

    let mut exposed_fn_arg_vars = vec![];
    for (def_id, args) in exposed_fn_args {
        for (local, ty) in args {
            let var = Var::Arg(def_id, local);
            exposed_fn_arg_vars.push(var);
            vars.insert(var, index_info.next_index());
            let ty = tss.tys[ty];
            compute_ends(ty, &mut index_info, def_id);
        }
    }

    PreAnalysisData {
        bodies,
        alloc_fns,
        call_graph,
        call_args,
        indirect_calls,
        index_info,
        globals,
        non_fn_globals,
        inv_fns,
        vars,
        index_prefixes,
        union_offsets,
        graph,
        var_nodes,
        exposed_fn_arg_vars,
    }
}

fn compute_ends<'tcx>(ty: &TyShape<'_, 'tcx>, ends: &mut IndexInfo<'tcx>, def_id: LocalDefId) {
    match ty {
        TyShape::Primitive(pty) => {
            ends.push(ends.next_index(), *pty, def_id);
        }
        TyShape::Array(t, _) => compute_ends(t, ends, def_id),
        TyShape::Struct(len, ts, _) => {
            let end = ends.next_index();
            for (_, t) in ts {
                compute_ends(t, ends, def_id);
            }
            ends.modify_end(end, end + (*len - 1));
        }
    }
}

pub fn analyze<'a, 'tcx>(
    config: &Config,
    pre: &PreAnalysisData<'tcx>,
    tss: &'a TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Solutions {
    let mut analyzer = Analyzer {
        tcx,
        tss,
        pre,
        graph: Graph::new(pre.index_info.len()),
    };
    for arg in &pre.exposed_fn_arg_vars {
        let arg_loc = pre.vars[arg];
        let Var::Arg(def_id, idx) = arg else { panic!() };
        let param = Var::Local(*def_id, *idx);
        let param_loc = pre.vars[&param];
        analyzer.graph.add_solution(param_loc, arg_loc);
    }
    for item in &pre.bodies {
        let body = if !config.use_optimized_mir {
            // use MIR before optimization
            &tcx.mir_drops_elaborated_and_const_checked(item.local_def_id)
                .borrow()
        } else if item.is_fn {
            // if item is a function, use optimized MIR
            tcx.optimized_mir(item.local_def_id.to_def_id())
        } else {
            // if item is a static, use MIR for CTFE
            tcx.mir_for_ctfe(item.local_def_id.to_def_id())
        };
        for (block, bbd) in body.basic_blocks.iter_enumerated() {
            for stmt in bbd.statements.iter() {
                let ctx = Context::new(&body.local_decls, item.local_def_id);
                analyzer.transfer_stmt(stmt, ctx);
            }
            let terminator = bbd.terminator();
            let ctx = Context::new(&body.local_decls, item.local_def_id);
            analyzer.transfer_term(terminator, ctx, block);
        }
    }
    analyzer.graph.solve(&pre.index_info.ends)
}

#[derive(Clone, Copy)]
struct Context<'a, 'tcx> {
    locals: &'a IndexVec<Local, LocalDecl<'tcx>>,
    owner: LocalDefId,
}

impl<'a, 'tcx> Context<'a, 'tcx> {
    #[inline]
    fn new(locals: &'a IndexVec<Local, LocalDecl<'tcx>>, owner: LocalDefId) -> Self {
        Self { locals, owner }
    }
}

struct Analyzer<'a, 'b, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pre: &'b PreAnalysisData<'tcx>,
    tss: &'a TyShapes<'a, 'tcx>,
    graph: Graph,
}

impl<'tcx> Analyzer<'_, '_, 'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>, ctx: Context<'_, 'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else {
            return;
        };
        let ty = l.ty(ctx.locals, self.tcx).ty;
        let l = self.prefixed_loc(*l, ctx);
        match r {
            Rvalue::Use(r) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::Repeat(r, _) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    let TyKind::Array(ty, _) = ty.kind() else { unreachable!() };
                    self.transfer_assign(l, r, *ty);
                }
            }
            Rvalue::Ref(_, _, r) => {
                let r = self.prefixed_loc(*r, ctx).with_ref(true);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::ThreadLocalRef(r) => {
                if let Some(r) = self.static_ref(*r) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::RawPtr(_, r) => {
                assert!(r.is_indirect_first_projection());
                let r = self.prefixed_loc(*r, ctx).with_deref(false);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::Len(_) => {}
            Rvalue::Cast(_, r, _) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::BinaryOp(op, box (r1, r2)) => {
                if !matches!(
                    op,
                    BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
                ) {
                    if let Some(r) = self.transfer_op(r1, ctx)
                        && !r.deref
                    {
                        self.transfer_assign(l, r, ty);
                    }
                    if let Some(r) = self.transfer_op(r2, ctx) {
                        self.transfer_assign(l, r, ty);
                    }
                }
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::UnaryOp(op, r) => {
                if matches!(op, UnOp::Neg)
                    && let Some(r) = self.transfer_op(r, ctx)
                {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::Discriminant(_) => {}
            Rvalue::Aggregate(box kind, fs) => match kind {
                AggregateKind::Array(ty) => {
                    for f in fs.iter() {
                        if let Some(r) = self.transfer_op(f, ctx) {
                            self.transfer_assign(l, r, *ty);
                        }
                    }
                }
                AggregateKind::Adt(_, v_idx, _, _, idx) => {
                    let TyShape::Struct(_, ts, _) = self.tss.tys[&ty] else { unreachable!() };
                    let TyKind::Adt(adt_def, generic_args) = ty.kind() else { unreachable!() };
                    let variant = adt_def.variant(*v_idx);
                    for ((i, d), f) in variant.fields.iter_enumerated().zip(fs) {
                        if let Some(r) = self.transfer_op(f, ctx) {
                            let i = if let Some(idx) = idx { *idx } else { i };
                            let proj = ts[i.index()].0;
                            let ty = d.ty(self.tcx, generic_args);
                            self.transfer_assign(l.add(proj), r, ty);
                        }
                    }
                }
                _ => unreachable!(),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                let r = self.prefixed_loc(*r, ctx);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::WrapUnsafeBinder(_, _) => unreachable!(),
        }
    }

    fn transfer_assign(&mut self, l: PrefixedLoc, r: PrefixedLoc, ty: Ty<'tcx>) {
        assert!(!l.r#ref);
        let len = self.tss.tys[&ty].len();
        for i in 0..len {
            let l = l.add(i);
            let r = r.add(i);
            match (l.deref, r.r#ref, r.deref) {
                (true, true, _) => unreachable!(),
                (true, false, true) => unreachable!(),
                (true, false, false) => self.graph.add_deref_eq(l.var.root, l.var.proj, r.index()), /* *l = r : *l >= r */
                (false, true, true) => self.graph.add_edge(l.index(), r.var.root, r.var.proj), /* l = &*r ? */
                (false, true, false) => self.graph.add_solution(l.index(), r.index()), /* l = &r : l >= { r } */
                (false, false, true) => self.graph.add_eq_deref(l.index(), r.var.root, r.var.proj), /* l = *r : l >= *r // edge from sol(r) to l */
                (false, false, false) => self.graph.add_edge(l.index(), r.index(), 0), /* l = r : l >= r */
            }
        }
    }

    fn transfer_op(&mut self, op: &Operand<'tcx>, ctx: Context<'_, 'tcx>) -> Option<PrefixedLoc> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Some(self.prefixed_loc(*place, ctx)),
            Operand::Constant(box constant) => match constant.const_ {
                Const::Ty(_, _) => unreachable!(),
                Const::Unevaluated(_, _) => None,
                Const::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(_) => None,
                        Scalar::Ptr(ptr, _) => {
                            match self.tcx.global_alloc(ptr.provenance.alloc_id()) {
                                GlobalAlloc::Static(def_id) => self.static_ref(def_id),
                                GlobalAlloc::Memory(_) => None,
                                _ => unreachable!(),
                            }
                        }
                    },
                    ConstValue::ZeroSized => match ty.kind() {
                        TyKind::FnDef(def_id, _) => {
                            let var = ProjectedLoc::new_root(
                                self.pre.globals.get(&def_id.as_local()?).copied()?,
                            );
                            Some(PrefixedLoc::new_ref(var))
                        }
                        TyKind::Array(_, _) => None,
                        TyKind::Tuple(_) => None,
                        _ => unreachable!("{:?}", ty),
                    },
                    ConstValue::Slice { .. } => None,
                    _ => unreachable!(),
                },
            },
        }
    }

    #[allow(clippy::assign_op_pattern)]
    fn transfer_term(
        &mut self,
        term: &Terminator<'tcx>,
        ctx: Context<'_, 'tcx>,
        block: BasicBlock,
    ) {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            return;
        };
        assert!(destination.projection.is_empty());

        let arg_locs: Vec<_> = args
            .iter()
            .map(|arg| self.transfer_op(&arg.node, ctx))
            .collect();
        let output = destination.ty(ctx.locals, self.tcx).ty;
        let dst = self.prefixed_loc(*destination, ctx);

        match func {
            Operand::Copy(func) | Operand::Move(func) => {
                assert!(func.projection.is_empty());
                let mut func = self.prefixed_loc(*func, ctx).with_deref(true);
                for (arg, arg_loc) in args.iter().zip(arg_locs) {
                    let ty = arg.node.ty(ctx.locals, self.tcx);
                    if let Some(arg) = arg_loc {
                        self.transfer_assign(func, arg, ty);
                    }
                    func = func.add(self.tss.tys[&ty].len());
                }
                self.transfer_assign(dst, func, output);
            }
            Operand::Constant(box constant) => {
                let Const::Val(value, ty) = constant.const_ else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                let name: Vec<_> = self
                    .tcx
                    .def_path(*def_id)
                    .data
                    .into_iter()
                    .map(|data| data.to_string())
                    .collect();
                let is_extern = name.iter().any(|s| s.starts_with("{extern#"));
                let seg = |i: usize| name.get(i).map(|s| s.as_str()).unwrap_or_default();
                let name = (seg(0), seg(1), seg(2), seg(3));
                if let Some(local_def_id) = def_id.as_local() {
                    if let Some(impl_def_id) = self.tcx.impl_of_method(*def_id) {
                        let ty = self.tcx.type_of(impl_def_id).skip_binder();
                        let TyKind::Adt(adt_def, _) = ty.kind() else { unreachable!() };
                        let adt_def_id = adt_def.did().as_local().unwrap();
                        let bitfield = &self.tss.bitfields[&adt_def_id];
                        let name = self.tcx.item_name(*def_id);
                        let name = name.as_str();
                        let name = name.strip_prefix("set_").unwrap_or(name);
                        assert!(bitfield.name_to_idx.contains_key(name));
                    } else if is_extern {
                        if output.is_raw_ptr() {
                            let var = Var::Alloc(ctx.owner, block);
                            let loc = ProjectedLoc::new_root(self.pre.vars[&var]);
                            self.transfer_assign(dst, PrefixedLoc::new_ref(loc), output);
                        }
                    } else if self.pre.alloc_fns.contains(&local_def_id) {
                        let var = Var::Alloc(ctx.owner, block);
                        let loc = ProjectedLoc::new_root(self.pre.vars[&var]);
                        self.transfer_assign(dst, PrefixedLoc::new_ref(loc), output);
                    } else {
                        let mut index = self.pre.globals[&local_def_id];
                        for (arg, arg_loc) in args.iter().zip(arg_locs) {
                            let ty = arg.node.ty(ctx.locals, self.tcx);
                            if let Some(arg) = arg_loc {
                                let loc = ProjectedLoc::new_root(index);
                                self.transfer_assign(PrefixedLoc::new(loc), arg, ty);
                            }
                            index = index + self.tss.tys[&ty].len();
                        }
                        let loc = ProjectedLoc::new_root(index);
                        self.transfer_assign(dst, PrefixedLoc::new(loc), output);
                    }
                } else {
                    match name {
                        ("option" | "result", _, "unwrap", _)
                        | ("slice" | "vec", _, "as_ptr" | "as_mut_ptr", _)
                        | ("ptr", _, _, "offset") => {
                            if let Some(arg) = &arg_locs[0] {
                                self.transfer_assign(dst, *arg, output);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn static_ref(&self, def_id: DefId) -> Option<PrefixedLoc> {
        let var = Var::Local(def_id.as_local()?, Local::new(0));
        let loc = ProjectedLoc::new_root(self.pre.vars.get(&var).copied()?);
        Some(PrefixedLoc::new_ref(loc))
    }

    fn prefixed_loc(&self, place: Place<'tcx>, ctx: Context<'_, 'tcx>) -> PrefixedLoc {
        let mut index = 0;
        let mut ty = ctx.locals[place.local].ty;
        let deref = place.is_indirect_first_projection();
        if deref {
            ty = ty_shape::unwrap_ptr(ty).unwrap();
        }
        let mut ty = self.tss.tys[&ty];
        for proj in place.projection {
            match proj {
                PlaceElem::Deref => {}
                PlaceElem::Index(_) => {
                    let TyShape::Array(t, _) = ty else { unreachable!() };
                    ty = t;
                }
                PlaceElem::Field(f, _) => {
                    let TyShape::Struct(_, fs, _) = ty else { unreachable!() };
                    let (i, nested_ty) = fs[f.index()];
                    index += i;
                    ty = nested_ty;
                }
                _ => unreachable!(),
            }
        }
        let var = Var::Local(ctx.owner, place.local);
        let loc = ProjectedLoc::new(self.pre.vars[&var], index);
        PrefixedLoc::new(loc).with_deref(place.is_indirect_first_projection())
    }
}

pub fn post_analyze<'a, 'tcx>(
    config: &Config,
    mut pre: PreAnalysisData<'tcx>,
    solutions: Solutions,
    tss: &'a TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> AnalysisResult {
    for (index, sols) in solutions.iter_enumerated() {
        let node = LocNode::new(0, index);
        let mut succs = vec![];
        for succ in sols.iter() {
            let max = pre.index_prefixes.get(&succ).cloned().unwrap_or(0);
            succs.extend((0..=max).map(|p| LocNode::new(p, succ)));
        }
        pre.graph.insert(node, LocEdges::Deref(succs));
    }
    let mut address_taken_indices = ChunkedBitSet::new_empty(pre.index_info.len());
    for indices in &solutions {
        address_taken_indices.union(indices);
    }
    for (i, _) in pre.index_info.ends.iter_enumerated() {
        if address_taken_indices.contains(i) {
            for j in (i + 1)..=pre.index_info.ends[i] {
                address_taken_indices.insert(j);
            }
        }
    }

    let analyzer = Analyzer {
        tcx,
        pre: &pre,
        tss,
        graph: Graph::new(pre.index_info.len()),
    };
    let mut writes: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
    let mut bitfield_writes: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
    for item in &pre.bodies {
        let writes = writes.entry(item.local_def_id).or_default();
        let bitfield_writes = bitfield_writes.entry(item.local_def_id).or_default();
        let body = if !config.use_optimized_mir {
            // use MIR before optimization
            &tcx.mir_drops_elaborated_and_const_checked(item.local_def_id)
                .borrow()
        } else if item.is_fn {
            // if item is a function, use optimized MIR
            tcx.optimized_mir(item.local_def_id.to_def_id())
        } else {
            // if item is a static, use MIR for CTFE
            tcx.mir_for_ctfe(item.local_def_id.to_def_id())
        };
        let ctx = Context::new(&body.local_decls, item.local_def_id);
        for (block, bbd) in body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in bbd.statements.iter().enumerate() {
                let StatementKind::Assign(box (l, _)) = stmt.kind else {
                    continue;
                };
                let location = Location {
                    block,
                    statement_index,
                };
                compute_writes(
                    l,
                    location,
                    &pre.index_info.ends,
                    &solutions,
                    ctx,
                    &analyzer,
                    writes,
                );
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &bbd.terminator().kind
            {
                let location = Location {
                    block,
                    statement_index: bbd.statements.len(),
                };
                compute_writes(
                    *destination,
                    location,
                    &pre.index_info.ends,
                    &solutions,
                    ctx,
                    &analyzer,
                    writes,
                );
                compute_bitfield_writes(
                    func,
                    args,
                    location,
                    tss,
                    tcx,
                    &pre.index_info.ends,
                    &solutions,
                    ctx,
                    &analyzer,
                    bitfield_writes,
                );
            }
        }
    }
    // only keep poinatble writes
    for writes in writes.values_mut() {
        for writes in writes.values_mut() {
            writes.intersect(&address_taken_indices);
        }
    }
    let fn_writes: FxHashMap<_, _> = writes
        .iter()
        .map(|(f, writes)| {
            let mut ws = ChunkedBitSet::new_empty(pre.index_info.len());
            for w in writes.values() {
                ws.union(w);
            }
            (*f, ws)
        })
        .collect();

    let indirect_calls: FxHashMap<_, FxHashMap<_, Vec<_>>> = pre
        .indirect_calls
        .into_iter()
        .map(|(def_id, calls)| {
            let calls = calls
                .into_iter()
                .map(|(bb, index)| {
                    let callees = solutions[index]
                        .iter()
                        .filter_map(|index| pre.inv_fns.get(&index).copied())
                        .collect();
                    (bb, callees)
                })
                .collect();
            (def_id, calls)
        })
        .collect();
    for (caller, calls) in &indirect_calls {
        let callees = pre.call_graph.get_mut(caller).unwrap();
        callees.extend(calls.values().flatten());
    }
    let call_graph_sccs: graph::Sccs<_, false> = graph::sccs_copied(&pre.call_graph);

    AnalysisResult {
        ends: pre.index_info.ends,
        union_offsets: pre.union_offsets,
        graph: pre.graph,
        var_nodes: pre.var_nodes,
        solutions,
        indirect_calls,
        call_graph_sccs,
        reachables: RefCell::new(FxHashMap::default()),
        writes,
        bitfield_writes,
        fn_writes,
    }
}

fn compute_writes<'tcx>(
    l: Place<'tcx>,
    location: Location,
    ends: &IndexVec<Loc, Loc>,
    solutions: &IndexVec<Loc, ChunkedBitSet<Loc>>,
    ctx: Context<'_, 'tcx>,
    analyzer: &Analyzer<'_, '_, 'tcx>,
    writes: &mut FxHashMap<Location, ChunkedBitSet<Loc>>,
) {
    let writes = writes
        .entry(location)
        .or_insert(ChunkedBitSet::new_empty(ends.len()));
    let ty = l.ty(ctx.locals, analyzer.tcx).ty;
    let len = analyzer.tss.tys[&ty].len();
    let l = analyzer.prefixed_loc(l, ctx);
    if l.deref {
        for loc in solutions[l.var.root].iter() {
            let loc = loc + l.var.proj;
            let end = *some_or!(ends.get(loc), continue);
            for i in 0..len {
                if loc + i > end {
                    break;
                }
                writes.insert(loc + i);
            }
        }
    } else {
        let loc = l.var.root + l.var.proj;
        for i in 0..len {
            writes.insert(loc + i);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn compute_bitfield_writes<'tcx>(
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    location: Location,
    tss: &TyShapes<'_, 'tcx>,
    tcx: TyCtxt<'tcx>,
    ends: &IndexVec<Loc, Loc>,
    solutions: &IndexVec<Loc, ChunkedBitSet<Loc>>,
    ctx: Context<'_, 'tcx>,
    analyzer: &Analyzer<'_, '_, 'tcx>,
    writes: &mut FxHashMap<Location, ChunkedBitSet<Loc>>,
) {
    if args.len() != 2 {
        return;
    }
    let Operand::Constant(box constant) = func else {
        return;
    };
    let Const::Val(_, ty) = constant.const_ else { unreachable!() };
    let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
    let local_def_id = some_or!(def_id.as_local(), return);
    let (local_def_id, method) = some_or!(receiver_and_method(local_def_id, tcx), return);
    let field = method.strip_prefix("set_").unwrap();
    let TyKind::Ref(_, ty, _) = args[0].node.ty(ctx.locals, tcx).kind() else { unreachable!() };
    let TyShape::Struct(_, fs, _) = tss.tys[ty] else { unreachable!() };
    let idx = tss.bitfields[&local_def_id].name_to_idx[field];
    let offset = fs[idx.as_usize()].0;
    let lhs = args[0].node.place().unwrap();
    assert!(lhs.projection.is_empty());
    let l = analyzer.prefixed_loc(lhs, ctx);
    let writes = writes
        .entry(location)
        .or_insert(ChunkedBitSet::new_empty(ends.len()));
    for loc in solutions[l.var.root].iter() {
        let loc = loc + offset;
        let end = ends[loc];
        if loc <= end {
            writes.insert(loc);
        }
    }
}

pub fn receiver_and_method(
    local_def_id: LocalDefId,
    tcx: TyCtxt<'_>,
) -> Option<(LocalDefId, String)> {
    let impl_def_id = tcx.impl_of_method(local_def_id.to_def_id())?;
    let impl_item = tcx.hir_expect_impl_item(local_def_id);
    let method = impl_item.ident.name.to_ident_string();
    let item = tcx.hir_expect_item(impl_def_id.expect_local());
    let ItemKind::Impl(imp) = item.kind else { unreachable!() };
    let rustc_hir::TyKind::Path(QPath::Resolved(_, path)) = imp.self_ty.kind else {
        unreachable!()
    };
    let Res::Def(_, struct_def_id) = path.res else { unreachable!() };
    let local_def_id = struct_def_id.expect_local();
    Some((local_def_id, method))
}

impl AnalysisResult {
    pub fn call_writes(&self, def_id: LocalDefId) -> ChunkedBitSet<Loc> {
        self.with_reachables(self.call_graph_sccs.indices[&def_id], |sccs| {
            let mut writes = ChunkedBitSet::new_empty(self.ends.len());
            for scc in sccs {
                for f in &self.call_graph_sccs.scc_elems[*scc] {
                    writes.union(&self.fn_writes[f]);
                }
            }
            writes
        })
    }

    #[inline]
    fn with_reachables<R, F: FnOnce(&FxHashSet<SccId>) -> R>(&self, scc: SccId, f: F) -> R {
        if let Some(rs) = self.reachables.borrow().get(&scc) {
            return f(rs);
        }
        let mut reachables = FxHashSet::default();
        self.reachables_from_scc(scc, &mut reachables);
        let r = f(&reachables);
        self.reachables.borrow_mut().insert(scc, reachables.clone());
        r
    }

    fn reachables_from_scc(&self, scc: SccId, reachables: &mut FxHashSet<SccId>) {
        if let Some(rs) = self.reachables.borrow().get(&scc) {
            reachables.extend(rs);
            return;
        }
        let mut this_reachables: FxHashSet<_> = [scc].into_iter().collect();
        for succ in self.call_graph_sccs.successors(scc) {
            self.reachables_from_scc(*succ, &mut this_reachables);
        }
        reachables.extend(this_reachables.iter());
        self.reachables.borrow_mut().insert(scc, this_reachables);
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "L{}"]
    pub struct Loc {}
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Var {
    Local(LocalDefId, Local),
    Alloc(LocalDefId, BasicBlock),
    Arg(LocalDefId, Local),
}

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Local(def_id, local) => write!(f, "{def_id:?}::{local:?}"),
            Var::Alloc(def_id, bb) => write!(f, "{def_id:?}::{bb:?}"),
            Var::Arg(def_id, i) => write!(f, "{def_id:?}::A{i:?}"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ProjectedLoc {
    root: Loc,
    proj: usize,
}

impl std::fmt::Debug for ProjectedLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.root.index())?;
        if self.proj != 0 {
            write!(f, "+{}", self.proj)?;
        }
        Ok(())
    }
}

impl ProjectedLoc {
    #[inline]
    fn new(root: Loc, proj: usize) -> Self {
        Self { root, proj }
    }

    #[inline]
    fn new_root(root: Loc) -> Self {
        Self { root, proj: 0 }
    }

    #[inline]
    fn add(self, proj: usize) -> Self {
        Self {
            proj: self.proj + proj,
            ..self
        }
    }

    #[inline]
    fn index(self) -> Loc {
        self.root + self.proj
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PrefixedLoc {
    deref: bool,
    r#ref: bool,
    var: ProjectedLoc,
}

impl PrefixedLoc {
    #[inline]
    fn new(var: ProjectedLoc) -> Self {
        Self {
            deref: false,
            r#ref: false,
            var,
        }
    }

    #[inline]
    fn new_ref(var: ProjectedLoc) -> Self {
        Self {
            deref: false,
            r#ref: true,
            var,
        }
    }

    #[inline]
    fn with_deref(self, deref: bool) -> Self {
        Self { deref, ..self }
    }

    #[inline]
    fn with_ref(self, r#ref: bool) -> Self {
        Self { r#ref, ..self }
    }

    #[inline]
    fn add(self, proj: usize) -> Self {
        Self {
            var: self.var.add(proj),
            ..self
        }
    }

    #[inline]
    fn index(self) -> Loc {
        self.var.index()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocProjection {
    Field(usize),
    Index,
    Deref,
}

fn add_edges(
    ty: &TyShape<'_, '_>,
    index: Loc, // global index
    graph: &mut LocGraph,
    index_prefixes: &mut FxHashMap<Loc, u8>,
    union_offsets: &mut FxHashMap<Loc, Vec<usize>>,
) -> LocNode {
    let node = match ty {
        TyShape::Primitive(_) => return LocNode::new(0, index),
        TyShape::Array(t, _) => {
            let succ = add_edges(t, index, graph, index_prefixes, union_offsets);
            let node = succ.parent();
            graph.insert(node, LocEdges::Index(succ));
            node
        }
        TyShape::Struct(len, ts, is_union) => {
            let succs: IndexVec<FieldIdx, _> = ts
                .iter()
                .map(|(offset, t)| {
                    add_edges(t, index + *offset, graph, index_prefixes, union_offsets)
                })
                .collect();
            let node = succs[FieldIdx::from_u32(0)].parent();
            graph.insert(node, LocEdges::Fields(succs));
            if *is_union {
                let mut offsets: Vec<usize> = ts.iter().map(|(offset, _)| *offset).collect();
                offsets.push(*len);
                union_offsets.insert(index, offsets);
            }
            node
        }
    };
    index_prefixes.insert(index, node.prefix);
    node
}

pub type LocGraph = FxHashMap<LocNode, LocEdges>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocNode {
    pub prefix: u8,
    pub index: Loc,
}

impl std::fmt::Debug for LocNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.index.index())?;
        if self.prefix != 0 {
            write!(f, ":{}", self.prefix)?;
        }
        Ok(())
    }
}

impl LocNode {
    fn new(prefix: u8, index: Loc) -> Self {
        Self { prefix, index }
    }

    fn parent(self) -> Self {
        Self {
            prefix: self.prefix + 1,
            index: self.index,
        }
    }
}

pub enum LocEdges {
    Fields(IndexVec<FieldIdx, LocNode>),
    Index(LocNode),
    Deref(Vec<LocNode>),
}

impl std::fmt::Debug for LocEdges {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocEdges::Fields(succs) => {
                write!(f, "[")?;
                for (i, succ) in succs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{i}: {succ:?}")?;
                }
                write!(f, "]")
            }
            LocEdges::Index(succ) => write!(f, "[_: {succ:?}]"),
            LocEdges::Deref(succs) => {
                write!(f, "[")?;
                for (i, field) in succs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "*: {field:?}")?;
                }
                write!(f, "]")
            }
        }
    }
}

type WeightedGraph = FxHashMap<Loc, FxHashMap<Loc, FxHashSet<usize>>>;

struct Graph {
    solutions: Solutions,
    zero_weight_edges: IndexVec<Loc, ChunkedBitSet<Loc>>,
    pos_weight_edges: WeightedGraph,
    deref_eqs: WeightedGraph,
    eq_derefs: WeightedGraph,
}

impl std::fmt::Debug for Graph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "solutions: ")?;
        for (i, sol) in self.solutions.iter().enumerate() {
            write!(f, "{}: {:?}, ", i, sol.iter().collect::<Vec<_>>())?;
        }
        write!(f, "\nzero_weight_edges: ")?;
        for (i, sol) in self.zero_weight_edges.iter().enumerate() {
            write!(f, "{}: {:?}, ", i, sol.iter().collect::<Vec<_>>())?;
        }
        write!(f, "\npos_weight_edges: {:?}", self.pos_weight_edges)?;
        write!(f, "\nderef_eqs: {:?}", self.deref_eqs)?;
        write!(f, "\neq_derefs: {:?}", self.eq_derefs)
    }
}

impl Graph {
    fn new(size: usize) -> Self {
        Self {
            solutions: IndexVec::from_raw(vec![ChunkedBitSet::new_empty(size); size]),
            zero_weight_edges: IndexVec::from_raw(vec![ChunkedBitSet::new_empty(size); size]),
            pos_weight_edges: FxHashMap::default(),
            deref_eqs: FxHashMap::default(),
            eq_derefs: FxHashMap::default(),
        }
    }

    fn add_solution(&mut self, v: Loc, sol: Loc) {
        self.solutions[v].insert(sol);
    }

    fn add_edge(&mut self, l: Loc, r: Loc, weight: usize) {
        if weight == 0 {
            self.zero_weight_edges[r].insert(l);
        } else {
            self.pos_weight_edges
                .entry(r)
                .or_default()
                .entry(l)
                .or_default()
                .insert(weight);
        }
    }

    fn add_deref_eq(&mut self, v: Loc, proj: usize, i: Loc) {
        self.deref_eqs
            .entry(v)
            .or_default()
            .entry(i)
            .or_default()
            .insert(proj);
    }

    fn add_eq_deref(&mut self, i: Loc, v: Loc, proj: usize) {
        self.eq_derefs
            .entry(v)
            .or_default()
            .entry(i)
            .or_default()
            .insert(proj);
    }

    fn solve(self, ends: &IndexVec<Loc, Loc>) -> Solutions {
        let Self {
            mut solutions,
            mut zero_weight_edges,
            mut pos_weight_edges,
            mut deref_eqs,
            mut eq_derefs,
        } = self;
        let len = solutions.len();

        let mut deltas = solutions.clone();
        let mut id_to_rep: IndexVec<Loc, Loc> = solutions.indices().collect();

        while deltas.iter().any(|s| !s.is_empty()) {
            let sccs: graph::Sccs<_, false> = graph::sccs_from_vec_bit_set(&zero_weight_edges);

            let mut scc_to_rep = IndexVec::new();
            let mut cycles = vec![];
            let mut new_id_to_rep = FxHashMap::default();
            for scc_id in sccs.scc_elems.indices() {
                let scc = &sccs.scc_elems[scc_id];
                let rep = *scc.iter().next().unwrap();
                scc_to_rep.push(rep);
                if scc.len() > 1 {
                    cycles.push((rep, scc));
                    for loc in scc {
                        if *loc != rep {
                            new_id_to_rep.insert(*loc, rep);
                        }
                    }
                }
            }

            if sccs.len() != len {
                // update id_to_rep
                for rep in &mut id_to_rep {
                    if let Some(new_rep) = new_id_to_rep.get(rep) {
                        *rep = *new_rep;
                    }
                }

                // update deltas
                for (rep, ids) in &cycles {
                    for id in *ids {
                        if rep != id {
                            let set =
                                std::mem::replace(&mut deltas[*id], ChunkedBitSet::new_empty(len));
                            deltas[*rep].union(&set);
                        }
                    }
                }

                // update solutions
                for (rep, ids) in &cycles {
                    let mut intersection = ChunkedBitSet::new_empty(len);
                    intersection.insert_all();
                    for id in *ids {
                        intersection.intersect(&solutions[*id]);
                        if rep != id {
                            let set = std::mem::replace(
                                &mut solutions[*id],
                                ChunkedBitSet::new_empty(len),
                            );
                            solutions[*rep].union(&set);
                        }
                    }
                    let mut union = solutions[*rep].clone();
                    union.subtract(&intersection);
                    deltas[*rep].union(&union);
                }

                // update zero_weight_edges
                zero_weight_edges = IndexVec::from_raw(vec![ChunkedBitSet::new_empty(len); len]);
                for (scc, rep) in scc_to_rep.iter_enumerated() {
                    let succs = &mut zero_weight_edges[*rep];
                    for succ in sccs.successors(scc) {
                        succs.insert(scc_to_rep[*succ]);
                    }
                }

                // update pos_weight_edges
                update_weighted_graph(&mut pos_weight_edges, &cycles);
                // update deref_eqs
                update_weighted_graph(&mut deref_eqs, &cycles);
                // update eq_derefs
                update_weighted_graph(&mut eq_derefs, &cycles);
            }

            for scc_id in sccs.post_order().rev() {
                let v = scc_to_rep[scc_id];
                if deltas[v].is_empty() {
                    continue;
                }
                let delta = std::mem::replace(&mut deltas[v], ChunkedBitSet::new_empty(len));

                propagate_deref(
                    v,
                    &deref_eqs,
                    &delta,
                    ends,
                    &id_to_rep,
                    &mut zero_weight_edges,
                    &mut solutions,
                    &mut deltas,
                    true,
                );
                propagate_deref(
                    v,
                    &eq_derefs,
                    &delta,
                    ends,
                    &id_to_rep,
                    &mut zero_weight_edges,
                    &mut solutions,
                    &mut deltas,
                    false,
                );

                for l in zero_weight_edges[v].iter() {
                    if l == v {
                        continue;
                    }
                    for f in delta.iter() {
                        if solutions[l].insert(f) {
                            deltas[l].insert(f);
                        }
                    }
                }

                if let Some(pos_weight_edges) = pos_weight_edges.get(&v) {
                    for (l, projs) in pos_weight_edges {
                        for proj in projs {
                            for i in delta.iter() {
                                let f = i + *proj;
                                if f > ends[i] {
                                    continue;
                                }
                                if !solutions[*l].insert(f) {
                                    continue;
                                }
                                deltas[*l].insert(f);
                            }
                        }
                    }
                }
            }
        }

        for (id, rep) in id_to_rep.iter_enumerated() {
            if id != *rep {
                solutions[id] = solutions[*rep].clone();
            }
        }

        solutions
    }
}

fn update_weighted_graph(graph: &mut WeightedGraph, cycles: &[(Loc, &FxHashSet<Loc>)]) {
    for (rep, ids) in cycles {
        let mut rep_edges = graph.remove(rep).unwrap_or_default();
        for id in *ids {
            if let Some(edges) = graph.remove(id) {
                for (l, weights) in edges {
                    match rep_edges.entry(l) {
                        Entry::Occupied(mut entry) => {
                            entry.get_mut().extend(weights);
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(weights);
                        }
                    }
                }
            }
        }
        if !rep_edges.is_empty() {
            graph.insert(*rep, rep_edges);
        }
    }
    for edges in graph.values_mut() {
        for (rep, ids) in cycles {
            let mut rep_weights = edges.remove(rep).unwrap_or_default();
            for id in *ids {
                if let Some(weights) = edges.remove(id) {
                    rep_weights.extend(weights);
                }
            }
            if !rep_weights.is_empty() {
                edges.insert(*rep, rep_weights);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
#[inline]
fn propagate_deref(
    v: Loc,
    derefs: &WeightedGraph,
    delta: &ChunkedBitSet<Loc>,
    ends: &IndexVec<Loc, Loc>,
    id_to_rep: &IndexVec<Loc, Loc>,
    zero_weight_edges: &mut IndexVec<Loc, ChunkedBitSet<Loc>>,
    solutions: &mut IndexVec<Loc, ChunkedBitSet<Loc>>,
    deltas: &mut IndexVec<Loc, ChunkedBitSet<Loc>>,
    deref_eq: bool,
) {
    let derefs = some_or!(derefs.get(&v), return);
    for (w, projs) in derefs {
        for proj in projs {
            for i in delta.iter() {
                let f = i + *proj;
                if f > ends[i] {
                    continue;
                }
                let f = id_to_rep[f];
                let (l, r) = if deref_eq { (f, *w) } else { (*w, f) };
                if !zero_weight_edges[r].insert(l) {
                    continue;
                }
                let mut diff = solutions[r].clone();
                diff.subtract(&solutions[l]);
                if !diff.is_empty() {
                    solutions[l].union(&diff);
                    deltas[l].union(&diff);
                }
            }
        }
    }
}

#[inline]
fn operand_to_fn(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let Const::Val(_, ty) = constant.const_ else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = ty.kind() else {
        return None;
    };
    Some(*def_id)
}

#[inline]
fn is_c_fn(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    for data in tcx.def_path(def_id).data {
        if data.to_string().starts_with("{extern#") {
            return true;
        }
    }
    false
}

struct FnPtrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_ptrs: FxHashSet<LocalDefId>,
}

impl<'tcx> FnPtrVisitor<'tcx> {
    #[inline]
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_ptrs: FxHashSet::default(),
        }
    }

    fn get_function(&self, operand: &Operand<'tcx>) -> Option<LocalDefId> {
        let constant = operand.constant()?;
        let Const::Val(_, ty) = constant.const_ else {
            return None;
        };
        let TyKind::FnDef(def_id, _) = ty.kind() else {
            return None;
        };
        let local_def_id = def_id.as_local()?;
        if self.tcx.impl_of_method(*def_id).is_none() && !is_c_fn(*def_id, self.tcx) {
            Some(local_def_id)
        } else {
            None
        }
    }

    fn operand(&mut self, operand: &Operand<'tcx>) {
        let local_def_id = some_or!(self.get_function(operand), return);
        self.fn_ptrs.insert(local_def_id);
    }
}

impl<'tcx> Visitor<'tcx> for FnPtrVisitor<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Use(v)
            | Rvalue::Repeat(v, _)
            | Rvalue::Cast(_, v, _)
            | Rvalue::UnaryOp(_, v) => self.operand(v),
            Rvalue::BinaryOp(_, box (v1, v2)) => {
                self.operand(v1);
                self.operand(v2);
            }
            Rvalue::Aggregate(_, fs) => {
                for f in fs {
                    self.operand(f);
                }
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }
}
