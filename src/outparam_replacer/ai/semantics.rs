use std::collections::{BTreeMap, BTreeSet};

use etrace::some_or;
use rustc_abi::{FieldIdx, Size, VariantIdx};
use rustc_const_eval::interpret::{AllocRange, GlobalAlloc, Scalar};
use rustc_hir as hir;
use rustc_middle::{
    mir::{
        AggregateKind, BinOp, CastKind, Const, ConstOperand, ConstValue, Local, Location, Operand,
        Place, PlaceElem, ProjectionElem, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, UnOp,
    },
    ty::{AdtKind, Ty, TyKind, adjustment::PointerCoercion},
};
use rustc_span::def_id::DefId;
use rustc_type_ir::{FloatTy, IntTy, UintTy};

use super::{analysis::FunctionSummary, domains::*};

pub struct TransferedTerminator {
    pub next_states: Vec<AbsState>,
    pub next_locations: Vec<Location>,
    pub writes: BTreeSet<AbsPath>,
    pub call_info: Vec<CallKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallKind {
    IntraEffect,
    IntraPure,
    Method,
    RustEffect(Option<Vec<AbsBase>>),
    RustPure,
    CEffect,
    CPure,
    TOP,
}

impl TransferedTerminator {
    #[inline]
    fn new(
        next_states: Vec<AbsState>,
        next_locations: Vec<Location>,
        writes: BTreeSet<AbsPath>,
        call_info: Vec<CallKind>,
    ) -> Self {
        Self {
            next_states,
            next_locations,
            writes,
            call_info,
        }
    }

    #[inline]
    fn empty() -> Self {
        Self::new(vec![], vec![], BTreeSet::new(), vec![])
    }

    #[inline]
    fn state_location(st: AbsState, loc: Location) -> Self {
        Self::new(vec![st], vec![loc], BTreeSet::new(), vec![])
    }

    #[inline]
    fn state_locations(st: AbsState, locs: Vec<Location>) -> Self {
        Self::new(vec![st], locs, BTreeSet::new(), vec![])
    }
}

#[allow(clippy::only_used_in_recursion)]
impl<'tcx> super::analysis::Analyzer<'_, 'tcx> {
    pub fn transfer_statement(
        &mut self,
        stmt: &Statement<'tcx>,
        state: &AbsState,
    ) -> (AbsState, BTreeSet<AbsPath>) {
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            let (new_v, reads, cmps) = self.transfer_rvalue(rvalue, state);
            let (mut new_state, writes) = self.assign(place, new_v, state);
            new_state.add_excludes(cmps.into_iter());
            new_state.add_reads(reads.into_iter());
            let (writes, nonnulls) = new_state.add_writes(writes.into_iter(), &self.ptr_params_inv);
            if !self.is_merged {
                new_state.add_nonnulls(nonnulls.into_iter());
            }
            (new_state, writes)
        } else {
            (state.clone(), BTreeSet::new())
        }
    }

    pub fn transfer_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        state: &AbsState,
        location: Location,
    ) -> TransferedTerminator {
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                TransferedTerminator::state_location(state.clone(), target.start_location())
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let (v, reads) = self.transfer_operand(discr, state);
                let mut new_state = state.clone();
                new_state.add_reads(reads.into_iter());
                let locations = if v.intv.is_bot() && v.uintv.is_bot() {
                    v.boolv
                        .gamma()
                        .into_iter()
                        .map(|b| targets.target_for_value(b as _).start_location())
                        .collect()
                } else if !v.intv.is_bot() && !v.intv.is_top() {
                    v.intv
                        .gamma()
                        .unwrap()
                        .iter()
                        .map(|b| targets.target_for_value(*b as _).start_location())
                        .collect()
                } else if !v.uintv.is_bot() && !v.uintv.is_top() {
                    v.uintv
                        .gamma()
                        .unwrap()
                        .iter()
                        .map(|u| targets.target_for_value(*u).start_location())
                        .collect()
                } else {
                    targets
                        .all_targets()
                        .iter()
                        .map(|target| target.start_location())
                        .collect()
                };
                TransferedTerminator::state_locations(new_state, locations)
            }
            TerminatorKind::UnwindResume => TransferedTerminator::empty(),
            TerminatorKind::UnwindTerminate(_) => TransferedTerminator::empty(),
            TerminatorKind::Return => TransferedTerminator::empty(),
            TerminatorKind::Unreachable => TransferedTerminator::empty(),
            TerminatorKind::Drop { target, .. } => {
                TransferedTerminator::state_location(state.clone(), target.start_location())
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let (func, mut reads) = self.transfer_operand(func, state);
                let (args, readss): (Vec<_>, Vec<_>) = args
                    .iter()
                    .map(|arg| self.transfer_operand(&arg.node, state))
                    .unzip();
                for reads2 in readss {
                    reads.extend(reads2);
                }

                let (new_states, writes, call_info) = if let Some(fns) = func.fnv.gamma() {
                    let mut new_states_map: BTreeMap<_, Vec<_>> = BTreeMap::new();
                    let mut ret_writes = BTreeSet::new();
                    let mut call_info = vec![];
                    for def_id in fns {
                        let (states, writes, call_kind) = self.transfer_call(
                            *def_id,
                            &args,
                            destination,
                            location,
                            state.clone(),
                            reads.clone(),
                        );
                        ret_writes.extend(writes);
                        call_info.push(call_kind);

                        for state in states {
                            let wn = (state.writes.clone(), state.nulls.clone());
                            new_states_map.entry(wn).or_default().push(state);
                        }
                    }
                    let new_states = new_states_map
                        .into_values()
                        .map(|states| states.into_iter().reduce(|a, b| a.join(&b)).unwrap())
                        .collect();
                    (new_states, ret_writes, call_info)
                } else {
                    let (mut new_state, writes) = self.assign(destination, AbsValue::top(), state);
                    let reads2 = args
                        .iter()
                        .flat_map(|arg| self.get_read_paths_of_ptr(&arg.ptrv, &[]));
                    reads.extend(reads2);
                    new_state.add_reads(reads.into_iter());
                    let (writes, nonnulls) =
                        new_state.add_writes(writes.into_iter(), &self.ptr_params_inv);
                    if !self.is_merged {
                        new_state.add_nonnulls(nonnulls.into_iter());
                    }
                    for arg in &args {
                        self.indirect_assign(&arg.ptrv, &AbsValue::top(), &[], &mut new_state);
                    }
                    (vec![new_state], writes, vec![])
                };
                let locations = if new_states.is_empty() {
                    vec![]
                } else {
                    target
                        .as_ref()
                        .map(|target| vec![target.start_location()])
                        .unwrap_or(vec![])
                };
                TransferedTerminator::new(new_states, locations, writes, call_info)
            }
            TerminatorKind::TailCall { .. } => todo!("{:?}", terminator.kind),
            TerminatorKind::Assert { cond, target, .. } => {
                let (_, reads) = self.transfer_operand(cond, state);
                let mut new_state = state.clone();
                new_state.add_reads(reads.into_iter());
                TransferedTerminator::state_location(new_state, target.start_location())
            }
            TerminatorKind::Yield { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::CoroutineDrop => unreachable!("{:?}", terminator.kind),
            TerminatorKind::FalseEdge { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::FalseUnwind { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::InlineAsm { targets, .. } => {
                let locations = targets
                    .iter()
                    .map(|target| target.start_location())
                    .collect();
                TransferedTerminator::state_locations(state.clone(), locations)
            }
        }
    }

    fn transfer_call(
        &mut self,
        callee: DefId,
        args: &[AbsValue],
        dst: &Place<'tcx>,
        location: Location,
        mut state: AbsState,
        mut reads: Vec<AbsPath>,
    ) -> (Vec<AbsState>, BTreeSet<AbsPath>, CallKind) {
        let mut offsets = vec![];
        let mut writes = vec![];
        let name = self.def_id_to_string(callee);
        let (vs, nulls, call_kind) = if callee.is_local() {
            if let Some(summary) = self.summaries.get(&callee) {
                return self
                    .transfer_intra_call(callee, summary, args, dst, state, location, reads);
            } else if name.contains("{extern#0}") {
                self.transfer_c_call(callee, args, &mut state, &mut reads)
            } else if name.contains("{impl#") {
                (
                    vec![self.transfer_method_call(callee, args, &mut reads)],
                    vec![],
                    CallKind::Method,
                )
            } else {
                (vec![AbsValue::top()], vec![], CallKind::TOP)
            }
        } else {
            self.transfer_rust_call(
                callee,
                args,
                &mut state,
                &mut offsets,
                &mut reads,
                &mut writes,
            )
        };
        let (mut new_states, writess): (Vec<_>, Vec<_>) = vs
            .into_iter()
            .map(|v| {
                let (mut new_state, writes_ret) = self.assign(dst, v, &state);
                new_state.add_excludes(offsets.iter().cloned());
                new_state.add_reads(reads.iter().cloned());
                let (writes, nonnulls) = new_state.add_writes(
                    writes.iter().cloned().chain(writes_ret),
                    &self.ptr_params_inv,
                );
                if !self.is_merged {
                    new_state.add_nonnulls(nonnulls.into_iter());
                }
                (new_state, writes)
            })
            .unzip();

        if !nulls.is_empty() {
            assert!(new_states.len() == nulls.len());
            for (state, (i, arg, n)) in new_states.iter_mut().zip(nulls) {
                match n {
                    AbsNull::Top => unreachable!(),
                    AbsNull::Null | AbsNull::Nonnull => {
                        let path = AbsPath::new(i, vec![]);
                        state.add_null(path, arg, n);
                    }
                }
            }
        }

        let writes = writess.into_iter().flatten().collect();
        (new_states, writes, call_kind)
    }

    #[allow(clippy::too_many_arguments)]
    fn transfer_intra_call(
        &mut self,
        callee: DefId,
        summary: &FunctionSummary,
        args: &[AbsValue],
        dst: &Place<'tcx>,
        state: AbsState,
        location: Location,
        mut reads: Vec<AbsPath>,
    ) -> (Vec<AbsState>, BTreeSet<AbsPath>, CallKind) {
        let call_kind = if summary.has_side_effects {
            CallKind::IntraEffect
        } else {
            CallKind::IntraPure
        };
        if summary.return_states.is_empty() {
            return (vec![], BTreeSet::new(), call_kind);
        }

        let mut ptr_maps = BTreeMap::new();
        for (param, arg) in summary.init_state.local.iter().skip(1).zip(args.iter()) {
            if let Some(idx) = param.ptrv.get_arg() {
                ptr_maps.insert(idx, arg.ptrv.clone());
            }
        }

        let sig = self.tcx.fn_sig(callee).skip_binder();
        let inputs = sig.inputs().skip_binder();
        for arg in args.iter().skip(inputs.len()) {
            let reads2 = self.get_read_paths_of_ptr(&arg.ptrv, &[]);
            reads.extend(reads2);
        }

        let mut states = vec![];
        let mut ret_writes = BTreeSet::new();
        for return_state in summary.return_states.values() {
            let mut state = state.clone();
            let ret_v = return_state.local.get(Local::ZERO);
            for (p, a) in &ptr_maps {
                let v = return_state.args.get(*p).subst(&ptr_maps);
                self.indirect_assign(a, &v, &[], &mut state);
            }
            let ret_v = ret_v.subst(&ptr_maps);
            let (mut state, writes) = self.assign(dst, ret_v, &state);
            let callee_null_excludes: Vec<_> = return_state
                .null_excludes
                .iter()
                .flat_map(|exclude| self.get_caller_path(exclude, args))
                .collect();
            let callee_excludes: Vec<_> = return_state
                .excludes
                .iter()
                .flat_map(|exclude| self.get_caller_path(exclude, args))
                .collect();
            let callee_reads: Vec<_> = return_state
                .reads
                .iter()
                .flat_map(|read| self.get_caller_path(read, args))
                .collect();
            let mut callee_writes = vec![];
            let mut callee_nonnulls = BTreeSet::new();
            for write in return_state.writes.iter() {
                let idx = write.base.index() - 1;
                let AbsPtr::Set(ptrs) = &args[idx].ptrv else {
                    continue;
                };
                if ptrs.len() != 1 {
                    continue;
                }
                let ptr = ptrs.first().unwrap();
                let (mut path, array_access) =
                    some_or!(AbsPath::from_place(ptr, &self.ptr_params), continue);
                if array_access {
                    continue;
                }
                if return_state.nonnulls.contains(write.base) {
                    callee_nonnulls.insert(path.base);
                }

                path.projections.extend(write.projections.clone());
                callee_writes.push(path.clone());
                self.call_args
                    .entry(location)
                    .or_default()
                    .insert(path.base.index() - 1, idx);
            }
            state.add_excludes(callee_excludes.into_iter());
            state.add_null_excludes(callee_null_excludes.into_iter());
            state.add_reads(reads.clone().into_iter());
            state.add_reads(callee_reads.into_iter());

            let (callee_writes, callee_nonnull_cands) =
                state.add_writes(callee_writes.into_iter(), &self.ptr_params_inv);
            let (writes, nonnulls) = state.add_writes(writes.into_iter(), &self.ptr_params_inv);

            if !self.is_merged {
                state.add_nonnulls(nonnulls.into_iter());
                state.add_nonnulls(callee_nonnull_cands.intersection(&callee_nonnulls).cloned());
            }

            ret_writes.extend(callee_writes.into_iter().chain(writes));
            states.push(state)
        }
        (states, ret_writes, call_kind)
    }

    fn transfer_method_call(
        &self,
        callee: DefId,
        args: &[AbsValue],
        reads: &mut Vec<AbsPath>,
    ) -> AbsValue {
        let node = self.tcx.hir_get_if_local(callee).unwrap();
        if let hir::Node::ImplItem(item) = node {
            let span_str = self.span_to_string(item.span);
            assert_eq!(span_str, "BitfieldStruct", "{callee:?} {span_str}");
            let reads2 = self.get_read_paths_of_ptr(&args[0].ptrv, &[]);
            reads.extend(reads2);
            if let hir::ImplItemKind::Fn(sig, _) = &item.kind {
                match &sig.decl.output {
                    hir::FnRetTy::Return(ty) => {
                        if let hir::TyKind::Path(hir::QPath::Resolved(_, path)) = &ty.kind
                            && let hir::def::Res::Def(_, def_id) = path.res {
                                let ty = self.def_id_to_string(def_id);
                                let ty = ty.split("::").last().unwrap();
                                let v = match ty {
                                    "c_int" => AbsValue::top_int(),
                                    "c_uint" => AbsValue::top_uint(),
                                    _ => AbsValue::top(),
                                };
                                return v;
                            }
                    }
                    hir::FnRetTy::DefaultReturn(_) => {
                        let name = item.ident.name.to_ident_string();
                        assert!(name.starts_with("set_"), "{callee:?}");
                        return AbsValue::bot();
                    }
                }
            }
        }
        unreachable!("{:?}", callee)
    }

    fn transfer_c_call(
        &mut self,
        callee: DefId,
        args: &[AbsValue],
        state: &mut AbsState,
        reads: &mut Vec<AbsPath>,
    ) -> (Vec<AbsValue>, Vec<(Local, ArgIdx, AbsNull)>, CallKind) {
        let name = self.def_id_to_string(callee);
        let mut segs: Vec<_> = name.split("::").collect();
        let segs0 = segs.pop().unwrap_or_default();

        let call_kind = match segs0 {
            "__ctype_toupper_loc"
            | "towlower"
            | "towupper"
            | "gettimeofday"
            | "strlen"
            | "strspn"
            | "strerror"
            | "__errno_location" => CallKind::CPure,
            _ => CallKind::CEffect,
        };

        let sig = self.tcx.fn_sig(callee).skip_binder();
        let inputs = sig.inputs().skip_binder();
        let output = sig.output().skip_binder();

        let ptr_args: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter_map(|(i, ty)| {
                if let TyKind::RawPtr(ty, _) = ty.kind() {
                    if let TyKind::Adt(adt, _) = ty.kind()
                        && self.def_id_to_string(adt.did()).ends_with("::_IO_FILE") {
                            return None;
                        }
                    return Some(i);
                }
                None
            })
            .collect();
        for arg in ptr_args.iter() {
            let reads2 = self.get_read_paths_of_ptr(&args[*arg].ptrv, &[]);
            reads.extend(reads2);
        }

        for arg in args.iter().skip(inputs.len()) {
            let reads2 = self.get_read_paths_of_ptr(&arg.ptrv, &[]);
            reads.extend(reads2);
        }

        let reads2 = args.iter().flat_map(|arg| {
            let (v, _) = self.read_ptr(&arg.ptrv, &[], state);
            self.get_read_paths_of_ptr(&v.ptrv, &[])
        });
        reads.extend(reads2);

        for arg in ptr_args {
            self.indirect_assign(&args[arg].ptrv, &AbsValue::top(), &[], state);
        }

        let v = if output.is_primitive() || output.is_unit() || output.is_never() {
            self.top_value_of_ty(&output)
        } else if output.is_raw_ptr() {
            AbsValue::heap_or_null()
        } else {
            AbsValue::top()
        };

        (vec![v], vec![], call_kind)
    }

    fn transfer_rust_call(
        &self,
        callee: DefId,
        args: &[AbsValue],
        state: &mut AbsState,
        offsets: &mut Vec<AbsPath>,
        reads: &mut Vec<AbsPath>,
        writes: &mut Vec<AbsPath>,
    ) -> (Vec<AbsValue>, Vec<(Local, ArgIdx, AbsNull)>, CallKind) {
        let name = self.def_id_to_string(callee);
        let mut call_kind = CallKind::RustPure;
        let mut segs: Vec<_> = name.split("::").collect();
        let segs0 = segs.pop().unwrap_or_default();
        let segs1 = segs.pop().unwrap_or_default();
        let segs2 = segs.pop().unwrap_or_default();
        let segs3 = segs.pop().unwrap_or_default();
        let v = match (segs3, segs2, segs1, segs0) {
            ("", "slice", _, "as_mut_ptr" | "as_ptr") => {
                let ptr = if let Some(ptrs) = args[0].ptrv.gamma() {
                    AbsPtr::alphas(
                        ptrs.iter()
                            .cloned()
                            .map(|mut ptr| {
                                let zero = AbsUint::alpha(0);
                                ptr.projections.push(AbsProjElem::Index(zero));
                                ptr
                            })
                            .collect(),
                    )
                } else {
                    AbsPtr::top()
                };
                AbsValue::ptr(ptr)
            }
            ("ptr", "mut_ptr" | "const_ptr", _, "offset") => {
                let offsets2 = self.get_read_paths_of_ptr(&args[0].ptrv, &[]);
                offsets.extend(offsets2);
                let ptr = if let Some(ptrs) = args[0].ptrv.gamma() {
                    AbsPtr::alphas(
                        ptrs.iter()
                            .cloned()
                            .map(|mut ptr| {
                                let last = ptr.projections.last_mut();
                                if let Some(AbsProjElem::Index(i)) = last {
                                    *i = i.to_i64().add(&args[1].intv).to_u64();
                                }
                                ptr
                            })
                            .collect(),
                    )
                } else {
                    AbsPtr::top()
                };
                AbsValue::ptr(ptr)
            }
            ("ptr", "mut_ptr" | "const_ptr", _, "is_null") => {
                if let Some(ptrs) = args[0].ptrv.gamma() {
                    let t = ptrs.iter().any(|p| p.is_null());
                    let f = ptrs.iter().any(|p| !p.is_null());
                    let args: BTreeSet<_> = ptrs
                        .iter()
                        .filter_map(|p| {
                            if !p.projections.is_empty() {
                                return None;
                            }
                            let (path, _) = AbsPath::from_place(p, &self.ptr_params)?;
                            Some(path.base)
                        })
                        .collect();
                    if args.len() == 1 && !t {
                        let i = *args.first().unwrap();
                        let arg = *self.ptr_params_inv.get(&i).unwrap();
                        match state.nulls.get(arg) {
                            AbsNull::Null => AbsValue::bool_true(),
                            AbsNull::Nonnull => AbsValue::bool_false(),
                            AbsNull::Top => {
                                return (
                                    vec![AbsValue::bool_true(), AbsValue::bool_false()],
                                    vec![(i, arg, AbsNull::null()), (i, arg, AbsNull::nonnull())],
                                    call_kind,
                                );
                            }
                        }
                    } else {
                        match (t, f) {
                            (true, true) => AbsValue::top_bool(),
                            (true, false) => AbsValue::bool_true(),
                            (false, true) => AbsValue::bool_false(),
                            (false, false) => AbsValue::bot(),
                        }
                    }
                } else {
                    AbsValue::top_bool()
                }
            }
            ("ptr", "mut_ptr" | "const_ptr", _, "offset_from") => AbsValue::top_int(),
            ("", "", "ptr", "write_volatile") => {
                self.indirect_assign(&args[0].ptrv, &args[1], &[], state);
                let writes2 = self.get_write_paths_of_ptr(&args[0].ptrv, &[]);
                writes.extend(writes2);
                let bases = self
                    .get_write_bases_of_ptr(&args[0].ptrv)
                    .unwrap_or_default();
                call_kind = CallKind::RustEffect(Some(bases));
                AbsValue::top()
            }
            ("", "", "ptr", "read_volatile")
            | ("", "clone", "Clone", "clone")
            | ("", "", "ptr", "read") => {
                let (v, reads2) = self.read_ptr(&args[0].ptrv, &[], state);
                reads.extend(reads2);
                v
            }
            ("", "option", _, "is_some") => {
                let (v, reads2) = self.read_ptr(&args[0].ptrv, &[], state);
                reads.extend(reads2);
                match v.optionv {
                    AbsOption::Top => AbsValue::top_bool(),
                    AbsOption::Some(_) => AbsValue::bool_true(),
                    AbsOption::None => AbsValue::bool_false(),
                    AbsOption::Bot => AbsValue::bot(),
                }
            }
            ("", "option", _, "is_none") => {
                let (v, reads2) = self.read_ptr(&args[0].ptrv, &[], state);
                reads.extend(reads2);
                match v.optionv {
                    AbsOption::Top => AbsValue::top_bool(),
                    AbsOption::Some(_) => AbsValue::bool_false(),
                    AbsOption::None => AbsValue::bool_true(),
                    AbsOption::Bot => AbsValue::bot(),
                }
            }
            ("", "option", _, "unwrap") => match &args[0].optionv {
                AbsOption::Top => AbsValue::top(),
                AbsOption::Some(v) => v.clone(),
                _ => AbsValue::bot(),
            },
            ("", "cast", "ToPrimitive", "to_u64")
            | ("", "num", _, "count_ones" | "trailing_zeros" | "leading_zeros")
            | ("", "", "mem", "size_of" | "align_of") => AbsValue::top_uint(),
            ("", "", "panicking", "panic" | "begin_panic" | "panic_explicit") => {
                call_kind = CallKind::RustEffect(None);
                AbsValue::bot()
            }
            ("", "vec", _, "leak")
            | ("ops", "deref", "Deref", "deref")
            | ("ops", "deref", "DerefMut", "deref_mut") => AbsValue::top_ptr(),
            ("", "num", _, "overflowing_add") => {
                AbsValue::alpha_list(vec![args[0].add(&args[1]), AbsValue::top_bool()])
            }
            ("", "num", _, "overflowing_sub") => {
                AbsValue::alpha_list(vec![args[0].sub(&args[1]), AbsValue::top_bool()])
            }
            ("", "num", _, "overflowing_mul") => {
                AbsValue::alpha_list(vec![args[0].mul(&args[1]), AbsValue::top_bool()])
            }
            ("", "num", _, "overflowing_div") => {
                AbsValue::alpha_list(vec![args[0].div(&args[1]), AbsValue::top_bool()])
            }
            ("", "num", _, "overflowing_rem") => {
                AbsValue::alpha_list(vec![args[0].rem(&args[1]), AbsValue::top_bool()])
            }
            ("", "num", _, "overflowing_neg") => {
                AbsValue::alpha_list(vec![args[0].neg(), AbsValue::top_bool()])
            }
            ("", "num", _, "wrapping_add") => args[0].add(&args[1]),
            ("", "num", _, "wrapping_sub") => args[0].sub(&args[1]),
            ("", "num", _, "wrapping_mul") => args[0].mul(&args[1]),
            ("", "num", _, "wrapping_div") => args[0].div(&args[1]),
            ("", "num", _, "wrapping_rem") => args[0].rem(&args[1]),
            ("", "num", _, "wrapping_neg") => args[0].neg(),
            (_, "f64", _, m) if m.starts_with("is_") => AbsValue::top_bool(),
            ("", "", "AsmCastTrait", "cast_out") => AbsValue::bot(),
            ("", "unix", _, "memcpy") => {
                let reads2 = self.get_read_paths_of_ptr(&args[1].ptrv, &[]);
                reads.extend(reads2);
                let writes2 = self.get_write_paths_of_ptr(&args[0].ptrv, &[]);
                writes.extend(writes2);
                let bases = self
                    .get_write_bases_of_ptr(&args[0].ptrv)
                    .unwrap_or_default();
                call_kind = CallKind::RustEffect(Some(bases));
                args[0].clone()
            }
            ("", "vec", _, "as_mut_ptr") => AbsValue::top_ptr(),
            ("ffi", "va_list", _, "arg" | "as_va_list")
            | ("", "", "AsmCastTrait", "cast_in")
            | ("", "f128_t", _, "new")
            | ("", "convert", "From", "from")
            | ("", "convert", "TryInto", "try_into")
            | ("", "convert", "Into", "into")
            | ("", "", "vec", "from_elem")
            | ("", "result", _, "unwrap")
            | ("", "num", _, "swap_bytes")
            | (
                "ops",
                "arith",
                "Add" | "BitAnd" | "BitOr" | "BitXor" | "Div" | "Mul" | "Neg" | "Not" | "Rem"
                | "Shl" | "Shr" | "Sub",
                _,
            ) => AbsValue::top(),
            (
                "ops",
                "arith",
                "AddAssign" | "BitAndAssign" | "BitOrAssign" | "BitXorAssign" | "DivAssign"
                | "MulAssign" | "RemAssign" | "ShlAssign" | "ShrAssign" | "SubAssign",
                _,
            )
            | ("", "cast", "ToPrimitive", "to_i64") => {
                let reads0 = self.get_read_paths_of_ptr(&args[0].ptrv, &[]);
                reads.extend(reads0);
                AbsValue::top()
            }
            ("", "cmp", "PartialOrd", "lt" | "le" | "gt" | "ge")
            | ("", "cmp", "PartialEq", "eq" | "ne") => {
                let reads0 = self.get_read_paths_of_ptr(&args[0].ptrv, &[]);
                let reads1 = self.get_read_paths_of_ptr(&args[1].ptrv, &[]);
                reads.extend(reads0);
                reads.extend(reads1);
                AbsValue::top_bool()
            }
            _ => todo!("{}", name),
        };
        (vec![v], vec![], call_kind)
    }

    fn transfer_rvalue(
        &self,
        rvalue: &Rvalue<'tcx>,
        state: &AbsState,
    ) -> (AbsValue, Vec<AbsPath>, Vec<AbsPath>) {
        match rvalue {
            Rvalue::Use(operand) => {
                let (v, reads) = self.transfer_operand(operand, state);
                (v, reads, vec![])
            }
            Rvalue::Repeat(operand, len) => {
                let (v, reads) = self.transfer_operand(operand, state);
                let len = len.try_to_target_usize(self.tcx).unwrap();
                (AbsValue::alpha_list(vec![v; len as usize]), reads, vec![])
            }
            Rvalue::Ref(_, _, place) => {
                let v = if place.is_indirect_first_projection() {
                    let projection = self.abstract_projection(&place.projection[1..], state);
                    let ptr = state.local.get(place.local);
                    if let AbsPtr::Set(ptrs) = &ptr.ptrv {
                        AbsValue::ptr(AbsPtr::Set(
                            ptrs.iter()
                                .map(|ptr| {
                                    let mut ptr_projection = ptr.projections.clone();
                                    ptr_projection.extend(projection.clone());
                                    AbsPlace {
                                        base: ptr.base,
                                        projections: ptr_projection,
                                    }
                                })
                                .collect(),
                        ))
                    } else {
                        AbsValue::top_ptr()
                    }
                } else {
                    let place = self.abstract_place(place, state);
                    AbsValue::alpha_ptr(place)
                };
                (v, vec![], vec![])
            }
            Rvalue::ThreadLocalRef(_) => (AbsValue::top_ptr(), vec![], vec![]),
            Rvalue::RawPtr(_, place) => {
                assert_eq!(place.projection.len(), 1);
                assert!(place.is_indirect_first_projection());
                let v = state.local.get(place.local);
                (v.clone(), vec![], vec![])
            }
            Rvalue::Len(_) => unreachable!("{:?}", rvalue),
            Rvalue::Cast(kind, operand, ty) => {
                let (v, reads) = self.transfer_operand(operand, state);
                let v = match kind {
                    CastKind::PointerExposeProvenance => self.top_value_of_ty(ty),
                    CastKind::PointerWithExposedProvenance => {
                        let zero: BTreeSet<u128> = [0].into_iter().collect();
                        if v.uintv.gamma().map(|s| s == &zero).unwrap_or(false) {
                            AbsValue::null()
                        } else {
                            AbsValue::top_ptr()
                        }
                    }
                    CastKind::PointerCoercion(coercion, _) => match coercion {
                        PointerCoercion::ReifyFnPointer => v,
                        PointerCoercion::UnsafeFnPointer => unreachable!("{:?}", rvalue),
                        PointerCoercion::ClosureFnPointer(_) => unreachable!("{:?}", rvalue),
                        PointerCoercion::MutToConstPointer => v,
                        PointerCoercion::ArrayToPointer => {
                            if let Some(ptrs) = v.ptrv.gamma() {
                                AbsValue::ptr(AbsPtr::Set(
                                    ptrs.iter()
                                        .cloned()
                                        .map(|mut ptr| {
                                            let zero = AbsUint::alpha(0);
                                            ptr.projections.push(AbsProjElem::Index(zero));
                                            ptr
                                        })
                                        .collect(),
                                ))
                            } else {
                                AbsValue::top_ptr()
                            }
                        }
                        PointerCoercion::Unsize => v,
                        PointerCoercion::DynStar => unreachable!("{:?}", rvalue),
                    },
                    CastKind::IntToInt | CastKind::FloatToInt => match ty.kind() {
                        TyKind::Int(int_ty) => match int_ty {
                            IntTy::Isize => v.to_i64(),
                            IntTy::I8 => v.to_i8(),
                            IntTy::I16 => v.to_i16(),
                            IntTy::I32 => v.to_i32(),
                            IntTy::I64 => v.to_i64(),
                            IntTy::I128 => v.to_i128(),
                        },
                        TyKind::Uint(uint_ty) => match uint_ty {
                            UintTy::Usize => v.to_u64(),
                            UintTy::U8 => v.to_u8(),
                            UintTy::U16 => v.to_u16(),
                            UintTy::U32 => v.to_u32(),
                            UintTy::U64 => v.to_u64(),
                            UintTy::U128 => v.to_u128(),
                        },
                        _ => unreachable!("{:?}", rvalue),
                    },
                    CastKind::FloatToFloat | CastKind::IntToFloat => {
                        if let TyKind::Float(float_ty) = ty.kind() {
                            match float_ty {
                                FloatTy::F16 => todo!("{:?}", rvalue),
                                FloatTy::F32 => v.to_f32(),
                                FloatTy::F64 => v.to_f64(),
                                FloatTy::F128 => todo!("{:?}", rvalue),
                            }
                        } else {
                            unreachable!("{:?}", rvalue)
                        }
                    }
                    CastKind::PtrToPtr => {
                        let void = if let TyKind::RawPtr(ty, _) = ty.kind() {
                            ty.is_c_void(self.tcx)
                        } else {
                            false
                        };
                        if void { v } else { AbsValue::heap().join(&v) }
                    }
                    CastKind::FnPtrToPtr => v,
                    CastKind::Transmute => v,
                };
                (v, reads, vec![])
            }
            Rvalue::BinaryOp(binop, box (l, r)) => {
                let (l, mut reads_l) = self.transfer_operand(l, state);
                let (r, reads_r) = self.transfer_operand(r, state);
                let v = match binop {
                    BinOp::Add => l.add(&r),
                    BinOp::AddUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::AddWithOverflow => unreachable!("{:?}", rvalue),
                    BinOp::Sub => l.sub(&r),
                    BinOp::SubUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::SubWithOverflow => unreachable!("{:?}", rvalue),
                    BinOp::Mul => l.mul(&r),
                    BinOp::MulUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::MulWithOverflow => unreachable!("{:?}", rvalue),
                    BinOp::Div => l.div(&r),
                    BinOp::Rem => l.rem(&r),
                    BinOp::BitXor => l.bit_xor(&r),
                    BinOp::BitAnd => l.bit_and(&r),
                    BinOp::BitOr => l.bit_or(&r),
                    BinOp::Shl => l.shl(&r),
                    BinOp::ShlUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Shr => l.shr(&r),
                    BinOp::ShrUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Eq => l.eq(&r),
                    BinOp::Lt => l.lt(&r),
                    BinOp::Le => l.le(&r),
                    BinOp::Ne => l.ne(&r),
                    BinOp::Ge => l.ge(&r),
                    BinOp::Gt => l.gt(&r),
                    BinOp::Cmp => todo!("{:?}", rvalue),
                    BinOp::Offset => todo!("{:?}", rvalue),
                };
                let mut cmps = vec![];
                if matches!(
                    binop,
                    BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
                ) && !l.ptrv.is_bot()
                    && !r.ptrv.is_bot()
                    && !l.ptrv.is_null()
                    && !r.ptrv.is_null()
                {
                    cmps.extend(self.get_read_paths_of_ptr(&l.ptrv, &[]));
                    cmps.extend(self.get_read_paths_of_ptr(&r.ptrv, &[]));
                }
                reads_l.extend(reads_r);
                (v, reads_l, cmps)
            }
            Rvalue::NullaryOp(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::UnaryOp(unary, operand) => {
                let (v, reads) = self.transfer_operand(operand, state);
                let v = match unary {
                    UnOp::Not => v.not(),
                    UnOp::Neg => v.neg(),
                    UnOp::PtrMetadata => todo!("{:?}", rvalue),
                };
                (v, reads, vec![])
            }
            Rvalue::Discriminant(_) => todo!("{:?}", rvalue),
            Rvalue::Aggregate(box kind, fields) => match kind {
                AggregateKind::Array(_) => {
                    let (vs, readss): (Vec<_>, Vec<_>) = fields
                        .iter()
                        .map(|operand| self.transfer_operand(operand, state))
                        .unzip();
                    let v = AbsValue::alpha_list(vs.into_iter().collect());
                    let reads = readss.into_iter().flatten().collect();
                    (v, reads, vec![])
                }
                AggregateKind::Tuple => unreachable!("{:?}", rvalue),
                AggregateKind::Adt(def_id, _, _, _, _) => {
                    let adt_def = self.tcx.adt_def(def_id);
                    match adt_def.adt_kind() {
                        AdtKind::Struct => {
                            let (vs, readss): (Vec<_>, Vec<_>) = fields
                                .iter()
                                .map(|operand| self.transfer_operand(operand, state))
                                .unzip();
                            let v = AbsValue::alpha_list(vs.into_iter().collect());
                            let reads = readss.into_iter().flatten().collect();
                            (v, reads, vec![])
                        }
                        AdtKind::Union => {
                            assert_eq!(fields.len(), 1);
                            let operand = &fields[FieldIdx::from_usize(0)];
                            let (v, reads) = self.transfer_operand(operand, state);
                            let variant = adt_def.variant(VariantIdx::from_usize(0));
                            let v = AbsValue::alpha_list(
                                variant.fields.iter().map(|_| v.clone()).collect(),
                            );
                            (v, reads, vec![])
                        }
                        AdtKind::Enum => {
                            assert_eq!(
                                format!("{adt_def:?}"),
                                "std::option::Option",
                                "{:?}",
                                rvalue
                            );
                            if let Some(field) = fields.get(FieldIdx::from_usize(0)) {
                                let (v, reads) = self.transfer_operand(field, state);
                                if v.is_bot() {
                                    (AbsValue::bot(), reads, vec![])
                                } else {
                                    (AbsValue::some(v), reads, vec![])
                                }
                            } else {
                                (AbsValue::none(), vec![], vec![])
                            }
                        }
                    }
                }
                AggregateKind::Closure(_, _) => unreachable!("{:?}", rvalue),
                AggregateKind::Coroutine(_, _) => unreachable!("{:?}", rvalue),
                AggregateKind::CoroutineClosure(_, _) => unreachable!("{:?}", rvalue),
                AggregateKind::RawPtr(_, _) => todo!("{:?}", rvalue),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::CopyForDeref(place) => {
                let (v, reads) = self.transfer_place(place, state);
                (v, reads, vec![])
            }
            Rvalue::WrapUnsafeBinder(_, _) => unreachable!("{:?}", rvalue),
        }
    }

    fn transfer_operand(
        &self,
        operand: &Operand<'tcx>,
        state: &AbsState,
    ) -> (AbsValue, Vec<AbsPath>) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.transfer_place(place, state),
            Operand::Constant(box constant) => (self.transfer_constant(constant), vec![]),
        }
    }

    fn transfer_place(&self, place: &Place<'tcx>, state: &AbsState) -> (AbsValue, Vec<AbsPath>) {
        if place.is_indirect_first_projection() {
            let projection = self.abstract_projection(&place.projection[1..], state);
            let ptr = state.local.get(place.local);
            self.read_ptr(&ptr.ptrv, &projection, state)
        } else {
            let v = state.local.get(place.local);
            let projection = self.abstract_projection(place.projection, state);
            (self.get_value(v, &projection), vec![])
        }
    }

    fn transfer_constant(&self, constant: &ConstOperand<'tcx>) -> AbsValue {
        match constant.const_ {
            Const::Ty(ty, constant) => {
                let v = constant.to_value();
                let v = self.tcx.valtree_to_const_val(v);
                self.transfer_const_value(&v, &ty)
            }
            Const::Unevaluated(constant, ty) => {
                if ty.is_ref() {
                    AbsValue::top()
                } else if let Ok(v) = self.tcx.const_eval_poly(constant.def) {
                    self.transfer_const_value(&v, &ty)
                } else {
                    self.top_value_of_ty(&ty)
                }
            }
            Const::Val(v, ty) => self.transfer_const_value(&v, &ty),
        }
    }

    fn transfer_const_value(&self, v: &ConstValue<'tcx>, ty: &Ty<'tcx>) -> AbsValue {
        match v {
            ConstValue::Scalar(s) => match s {
                Scalar::Int(i) => match ty.kind() {
                    TyKind::Int(int_ty) => {
                        let v = match int_ty {
                            IntTy::Isize => i.to_i64() as _,
                            IntTy::I8 => i.to_i8() as _,
                            IntTy::I16 => i.to_i16() as _,
                            IntTy::I32 => i.to_i32() as _,
                            IntTy::I64 => i.to_i64() as _,
                            IntTy::I128 => i.to_i128(),
                        };
                        AbsValue::alpha_int(v)
                    }
                    TyKind::Uint(uint_ty) => {
                        let v = match uint_ty {
                            UintTy::Usize => i.to_u64() as _,
                            UintTy::U8 => i.to_u8() as _,
                            UintTy::U16 => i.to_u16() as _,
                            UintTy::U32 => i.to_u32() as _,
                            UintTy::U64 => i.to_u64() as _,
                            UintTy::U128 => i.to_u128(),
                        };
                        AbsValue::alpha_uint(v)
                    }
                    TyKind::Float(float_ty) => {
                        let v = match float_ty {
                            FloatTy::F16 => todo!("{:?}", float_ty),
                            FloatTy::F32 => f32::from_bits(i.to_u32()) as _,
                            FloatTy::F64 => f64::from_bits(i.to_u64()),
                            FloatTy::F128 => todo!("{:?}", float_ty),
                        };
                        AbsValue::alpha_float(v)
                    }
                    TyKind::Bool => AbsValue::alpha_bool(i.try_to_bool().unwrap()),
                    TyKind::Char => AbsValue::alpha_uint(i.to_u32() as _),
                    _ => unreachable!("{:?}", ty),
                },
                Scalar::Ptr(ptr, _) => {
                    let alloc = self.tcx.global_alloc(ptr.provenance.alloc_id());
                    match alloc {
                        GlobalAlloc::Function { .. } => unreachable!("{:?}", alloc),
                        GlobalAlloc::VTable(_, _) => unreachable!("{:?}", alloc),
                        GlobalAlloc::Static(_) | GlobalAlloc::Memory(_) => AbsValue::heap(),
                    }
                }
            },
            ConstValue::ZeroSized => {
                if let TyKind::FnDef(def_id, _) = ty.kind() {
                    AbsValue::alpha_fn(*def_id)
                } else {
                    unreachable!("{:?}", v)
                }
            }
            ConstValue::Slice { data, meta } => {
                let size = Size::from_bytes(*meta);
                let range = AllocRange {
                    start: Size::ZERO,
                    size,
                };
                let arr = data
                    .inner()
                    .get_bytes_strip_provenance(&self.tcx, range)
                    .unwrap();
                let msg = String::from_utf8(arr.to_vec()).unwrap();
                if msg == "explicit panic" || msg == "internal error: entered unreachable code" {
                    AbsValue::top()
                } else {
                    unreachable!("{:?}", msg)
                }
            }
            ConstValue::Indirect { .. } => AbsValue::top(),
        }
    }

    pub fn top_value_of_ty(&self, ty: &Ty<'tcx>) -> AbsValue {
        match ty.kind() {
            TyKind::Bool => AbsValue::top_bool(),
            TyKind::Char => unreachable!("{:?}", ty),
            TyKind::Int(_) => AbsValue::top_int(),
            TyKind::Uint(_) => AbsValue::top_uint(),
            TyKind::Float(_) => AbsValue::top_float(),
            TyKind::Adt(adt, arg) => match adt.adt_kind() {
                AdtKind::Struct | AdtKind::Union => {
                    let variant = adt.variant(VariantIdx::from_usize(0));
                    AbsValue::alpha_list(
                        variant
                            .fields
                            .iter()
                            .map(|field| {
                                let ty = field.ty(self.tcx, arg);
                                self.top_value_of_ty(&ty)
                            })
                            .collect(),
                    )
                }
                AdtKind::Enum => {
                    let ty = format!("{adt:?}");
                    match ty.as_str() {
                        "std::option::Option" => AbsValue::top_option(),
                        "libc::c_void" => AbsValue::top(),
                        _ => unreachable!("{:?}", ty),
                    }
                }
            },
            TyKind::Foreign(_) => AbsValue::top(),
            TyKind::Str => unreachable!("{:?}", ty),
            TyKind::Array(ty, len) => {
                let len = len.try_to_target_usize(self.tcx).unwrap();
                if len <= 100 {
                    AbsValue::alpha_list((0..len).map(|_| self.top_value_of_ty(ty)).collect())
                } else {
                    AbsValue::top_list()
                }
            }
            TyKind::Pat(_, _) => unreachable!("{:?}", ty),
            TyKind::Slice(_) => unreachable!("{:?}", ty),
            TyKind::RawPtr(_, _) | TyKind::Ref(_, _, _) => AbsValue::heap_or_null(),
            TyKind::FnDef(_, _) => unreachable!("{:?}", ty),
            TyKind::FnPtr(_, _) => todo!("{:?}", ty),
            TyKind::UnsafeBinder(_) => unreachable!("{:?}", ty),
            TyKind::Dynamic(_, _, _) => unreachable!("{:?}", ty),
            TyKind::Closure(_, _) => unreachable!("{:?}", ty),
            TyKind::CoroutineClosure(_, _) => unreachable!("{:?}", ty),
            TyKind::Coroutine(_, _) => unreachable!("{:?}", ty),
            TyKind::CoroutineWitness(_, _) => unreachable!("{:?}", ty),
            TyKind::Never => AbsValue::bot(),
            TyKind::Tuple(tys) => {
                AbsValue::alpha_list(tys.iter().map(|ty| self.top_value_of_ty(&ty)).collect())
            }
            TyKind::Alias(_, _) => unreachable!("{:?}", ty),
            TyKind::Param(_) => unreachable!("{:?}", ty),
            TyKind::Bound(_, _) => unreachable!("{:?}", ty),
            TyKind::Placeholder(_) => unreachable!("{:?}", ty),
            TyKind::Infer(_) => unreachable!("{:?}", ty),
            TyKind::Error(_) => unreachable!("{:?}", ty),
        }
    }

    fn abstract_place(&self, place: &Place<'tcx>, state: &AbsState) -> AbsPlace {
        let base = AbsBase::Local(place.local);
        let projection = self.abstract_projection(place.projection, state);
        AbsPlace {
            base,
            projections: projection,
        }
    }

    fn abstract_projection(
        &self,
        projection: &[PlaceElem<'tcx>],
        state: &AbsState,
    ) -> Vec<AbsProjElem> {
        projection
            .iter()
            .map(|e| self.abstract_elem(e, state))
            .collect()
    }

    fn abstract_elem(&self, elem: &PlaceElem<'tcx>, state: &AbsState) -> AbsProjElem {
        match elem {
            ProjectionElem::Deref => todo!("{:?}", elem),
            ProjectionElem::Field(field, _) => AbsProjElem::Field(*field),
            ProjectionElem::Index(idx) => AbsProjElem::Index(state.local.get(*idx).uintv.clone()),
            ProjectionElem::ConstantIndex { .. } => unreachable!("{:?}", elem),
            ProjectionElem::Subslice { .. } => unreachable!("{:?}", elem),
            ProjectionElem::Downcast(_, _) => unreachable!("{:?}", elem),
            ProjectionElem::OpaqueCast(_) => unreachable!("{:?}", elem),
            ProjectionElem::UnwrapUnsafeBinder(_) => unreachable!("{:?}", elem),
            ProjectionElem::Subtype(_) => unreachable!("{:?}", elem),
        }
    }

    fn assign(
        &mut self,
        place: &Place<'tcx>,
        new_v: AbsValue,
        state: &AbsState,
    ) -> (AbsState, Vec<AbsPath>) {
        let mut new_state = state.clone();
        let writes = if place.is_indirect_first_projection() {
            let projection = self.abstract_projection(&place.projection[1..], state);
            let ptr = state.local.get(place.local);
            self.indirect_assigns.insert(place.local);
            self.indirect_assign(&ptr.ptrv, &new_v, &projection, &mut new_state);
            self.get_write_paths_of_ptr(&ptr.ptrv, &projection)
        } else {
            let old_v = new_state.local.get_mut(place.local);
            let projection = self.abstract_projection(place.projection, state);
            self.update_value(new_v, old_v, false, &projection);
            vec![]
        };
        (new_state, writes)
    }

    fn indirect_assign(
        &self,
        ptr: &AbsPtr,
        new_v: &AbsValue,
        projection: &[AbsProjElem],
        state: &mut AbsState,
    ) {
        if let AbsPtr::Set(ptrs) = ptr {
            if ptrs
                .iter()
                .any(|ptr| matches!(ptr.base, AbsBase::Arg(_) | AbsBase::Heap))
            {
                let reads = self.get_read_paths_of_ptr(&new_v.ptrv, &[]);
                state.add_excludes(reads.into_iter());
            }
            let weak = ptrs.len() > 1;
            for ptr in ptrs {
                let old_v = some_or!(state.get_mut(ptr.base), continue);
                let mut ptr_projection = ptr.projections.clone();
                ptr_projection.extend(projection.to_owned());
                self.update_value(new_v.clone(), old_v, weak, &ptr_projection);
            }
        }
    }

    fn get_write_paths_of_ptr(&self, ptr: &AbsPtr, projection: &[AbsProjElem]) -> Vec<AbsPath> {
        if let AbsPtr::Set(ptrs) = ptr
            && ptrs.len() == 1 {
                let mut ptr = ptrs.first().unwrap().clone();
                ptr.projections.extend(projection.to_owned());
                if let Some((path, false)) = AbsPath::from_place(&ptr, &self.ptr_params) {
                    return self.expands_path(&path);
                }
            }
        vec![]
    }

    fn get_write_bases_of_ptr(&self, ptr: &AbsPtr) -> Option<Vec<AbsBase>> {
        if let AbsPtr::Set(ptrs) = ptr
            && ptrs.len() == 1 {
                let ptr = ptrs.first().unwrap().clone();
                return Some(vec![ptr.base]);
            }
        None
    }

    fn update_value(
        &self,
        new_v: AbsValue,
        old_v: &mut AbsValue,
        weak: bool,
        projection: &[AbsProjElem],
    ) {
        if let Some(first) = projection.first() {
            match first {
                AbsProjElem::Field(field) => {
                    if let Some(old_v) = AbsValue::make_mut(old_v).listv.get_mut(field.index()) {
                        self.update_value(new_v, old_v, weak, &projection[1..]);
                    }
                }
                AbsProjElem::Index(idx) => {
                    if let AbsList::List(l) = &mut AbsValue::make_mut(old_v).listv {
                        let (indices, new_weak): (Box<dyn Iterator<Item = usize>>, _) =
                            if let Some(indices) = idx.gamma() {
                                (Box::new(indices.iter().map(|i| *i as _)), indices.len() > 1)
                            } else {
                                (Box::new(0..l.len()), l.len() > 1)
                            };
                        let weak = weak || new_weak;
                        for idx in indices {
                            if let Some(old_v) = l.get_mut(idx) {
                                self.update_value(new_v.clone(), old_v, weak, &projection[1..]);
                            }
                        }
                    }
                }
            }
        } else if weak {
            *old_v = new_v.join(old_v);
        } else {
            *old_v = new_v;
        }
    }

    fn read_ptr(
        &self,
        ptr: &AbsPtr,
        projection: &[AbsProjElem],
        state: &AbsState,
    ) -> (AbsValue, Vec<AbsPath>) {
        let v = if let Some(ptrs) = ptr.gamma() {
            ptrs.iter()
                .filter_map(|ptr| {
                    let v = state.get(ptr.base)?;
                    let mut ptr_projection = ptr.projections.clone();
                    ptr_projection.extend(projection.to_owned());
                    Some(self.get_value(v, &ptr_projection))
                })
                .reduce(|v1, v2| v1.join(&v2))
                .unwrap_or(AbsValue::bot())
        } else {
            AbsValue::top()
        };
        (v, self.get_read_paths_of_ptr(ptr, projection))
    }

    pub fn get_read_paths_of_ptr(&self, ptr: &AbsPtr, projection: &[AbsProjElem]) -> Vec<AbsPath> {
        if let AbsPtr::Set(ptrs) = ptr {
            ptrs.iter()
                .cloned()
                .filter_map(|mut ptr| {
                    ptr.projections.extend(projection.to_owned());
                    AbsPath::from_place(&ptr, &self.ptr_params).map(|(path, _)| path)
                })
                .flat_map(|path| self.expands_path(&path))
                .collect()
        } else {
            vec![]
        }
    }

    fn get_value(&self, v: &AbsValue, projection: &[AbsProjElem]) -> AbsValue {
        let first = some_or!(projection.first(), return v.clone());
        match first {
            AbsProjElem::Field(field) => match &v.listv {
                AbsList::Top => AbsValue::top(),
                AbsList::List(l) => {
                    if let Some(v) = l.get(field.index()) {
                        self.get_value(v, &projection[1..])
                    } else {
                        AbsValue::bot()
                    }
                }
                AbsList::Bot => AbsValue::bot(),
            },
            AbsProjElem::Index(idx) => match &v.listv {
                AbsList::Top => {
                    if idx.is_bot() {
                        AbsValue::bot()
                    } else {
                        AbsValue::top()
                    }
                }
                AbsList::List(l) => {
                    let indices: Box<dyn Iterator<Item = usize>> =
                        if let Some(indices) = idx.gamma() {
                            Box::new(indices.iter().map(|i| *i as _))
                        } else {
                            Box::new(0..l.len())
                        };
                    indices
                        .filter_map(|index| {
                            l.get(index).map(|v| self.get_value(v, &projection[1..]))
                        })
                        .reduce(|v1, v2| v1.join(&v2))
                        .unwrap_or(AbsValue::bot())
                }
                AbsList::Bot => AbsValue::bot(),
            },
        }
    }

    fn get_caller_path(&self, callee_path: &AbsPath, args: &[AbsValue]) -> Vec<AbsPath> {
        let ptrs = if let AbsPtr::Set(ptrs) = &args[callee_path.base.index() - 1].ptrv {
            ptrs
        } else {
            return vec![];
        };
        ptrs.iter()
            .filter_map(|ptr| {
                let (mut path, _) = AbsPath::from_place(ptr, &self.ptr_params)?;
                path.projections.extend(callee_path.projections.clone());
                Some(path)
            })
            .collect::<Vec<_>>()
    }
}
