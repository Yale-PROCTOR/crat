use points_to::andersen;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_middle::{
    mir::{
        AggregateKind, BinOp, CastKind, Const, ConstValue, Location, Operand, Place, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind, UnOp,
        interpret::{GlobalAlloc, Scalar},
    },
    ty::{IntTy, Ty, TyKind, UintTy, adjustment::PointerCoercion},
};
use rustc_span::{def_id::LocalDefId, source_map::Spanned};
use utils::ty_shape::TyShape;

use super::{analysis::Analyzer, domains::*};

impl<'tcx> Analyzer<'tcx, '_, '_> {
    pub fn transfer_stmt(&self, stmt: &Statement<'tcx>, stmt_loc: Location, state: &mut AbsMem) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        if l.projection.is_empty() {
            state.gm().invalidate_symbolic(l.local);
        }
        let lty = Place::ty(l, &self.body.local_decls, self.tcx).ty;
        let (l, l_deref) = self.acc_path(*l, state);
        if let Some(writes) = self.get_assign_writes(stmt_loc) {
            let strong_update = state.g().strong_update_loc(l.clone(), l_deref);
            state.gm().invalidate(
                self.ctx.local_def_id,
                strong_update.as_ref(),
                !l_deref,
                self.ctx.may_points_to,
                writes,
            );
        }
        match r {
            Rvalue::Use(r) => {
                let r = self.transfer_op(r, state);
                state
                    .gm()
                    .assign_with_ty(&l, l_deref, &r, self.ctx.tss.tys[&lty]);
            }
            Rvalue::Cast(kind, r, ty) => match kind {
                CastKind::IntToInt => {
                    let rty = r.ty(&self.body.local_decls, self.tcx);
                    let r = self.transfer_op(r, state);
                    if let OpVal::Int(v) = r {
                        let v = match ty.kind() {
                            TyKind::Int(int_ty) => match int_ty {
                                IntTy::Isize => to_isize(v, rty),
                                IntTy::I8 => to_i8(v, rty),
                                IntTy::I16 => to_i16(v, rty),
                                IntTy::I32 => to_i32(v, rty),
                                IntTy::I64 => to_i64(v, rty),
                                IntTy::I128 => to_i128(v, rty),
                            },
                            TyKind::Uint(uint_ty) => match uint_ty {
                                UintTy::Usize => to_usize(v, rty),
                                UintTy::U8 => to_u8(v, rty),
                                UintTy::U16 => to_u16(v, rty),
                                UintTy::U32 => to_u32(v, rty),
                                UintTy::U64 => to_u64(v, rty),
                                UintTy::U128 => to_u128(v, rty),
                            },
                            _ => unreachable!(),
                        };
                        state.gm().assign(&l, l_deref, &OpVal::Int(v));
                    } else {
                        state.gm().assign(&l, l_deref, &r);
                    }
                }
                CastKind::PointerCoercion(coercion, _) => match coercion {
                    PointerCoercion::ReifyFnPointer
                    | PointerCoercion::UnsafeFnPointer
                    | PointerCoercion::ClosureFnPointer(_)
                    | PointerCoercion::ArrayToPointer => {
                        state.gm().assign_with_ty(
                            &l,
                            l_deref,
                            &OpVal::Other,
                            self.ctx.tss.tys[&lty],
                        );
                    }
                    PointerCoercion::MutToConstPointer
                    | PointerCoercion::Unsize
                    | PointerCoercion::DynStar => {
                        let r = self.transfer_op(r, state);
                        state
                            .gm()
                            .assign_with_ty(&l, l_deref, &r, self.ctx.tss.tys[&lty]);
                    }
                },
                _ => {
                    state
                        .gm()
                        .assign_with_ty(&l, l_deref, &OpVal::Other, self.ctx.tss.tys[&lty]);
                }
            },
            Rvalue::Repeat(r, len) => {
                let r = self.transfer_op(r, state);
                let len = len.try_to_target_usize(self.tcx).unwrap();
                let TyKind::Array(ty, _) = lty.kind() else { unreachable!() };
                for i in 0..len.min(10) {
                    let l = l.extended(&[AccElem::num_index(i as _)]);
                    state
                        .gm()
                        .assign_with_ty(&l, l_deref, &r, self.ctx.tss.tys[ty]);
                }
            }
            Rvalue::Ref(_, _, r) => {
                assert!(!l_deref);
                let (r, r_deref) = self.acc_path(*r, state);
                state.gm().x_eq_ref_y(&l, &r, r_deref);
            }
            Rvalue::ThreadLocalRef(_) => {
                state.gm().assign(&l, l_deref, &OpVal::Other);
            }
            Rvalue::RawPtr(_, r) => {
                assert_eq!(r.projection.len(), 1);
                let (path, is_deref) = self.acc_path(*r, state);
                assert!(is_deref);
                let v = OpVal::Place(path, false);
                state.gm().assign(&l, l_deref, &v);
            }
            Rvalue::Len(_) => unreachable!(),
            Rvalue::BinaryOp(op, box (r1, r2)) => {
                let ty = r1.ty(&self.body.local_decls, self.tcx);
                let r1 = self.transfer_op(r1, state);
                let r2 = self.transfer_op(r2, state);
                if let (OpVal::Int(v1), OpVal::Int(v2)) = (r1, r2) {
                    let v = match op {
                        BinOp::Add => v1 + v2,
                        BinOp::Sub => v1 - v2,
                        BinOp::Mul => v1 * v2,
                        BinOp::Div => div(v1, v2, ty),
                        BinOp::Rem => rem(v1, v2, ty),
                        BinOp::BitXor => v1 ^ v2,
                        BinOp::BitAnd => v1 & v2,
                        BinOp::BitOr => v1 | v2,
                        BinOp::Shl => shl(v1, v2, ty),
                        BinOp::Shr => shr(v1, v2, ty),
                        BinOp::Eq => (v1 == v2) as i128,
                        BinOp::Lt => lt(v1, v2, ty),
                        BinOp::Le => le(v1, v2, ty),
                        BinOp::Ne => (v1 != v2) as i128,
                        BinOp::Ge => ge(v1, v2, ty),
                        BinOp::Gt => gt(v1, v2, ty),
                        _ => unreachable!(),
                    };
                    state.gm().assign(&l, l_deref, &OpVal::Int(v));
                } else {
                    state.gm().assign(&l, l_deref, &OpVal::Other);
                }
            }
            Rvalue::UnaryOp(op, r) => {
                let ty = r.ty(&self.body.local_decls, self.tcx);
                let r = self.transfer_op(r, state);
                if let OpVal::Int(v) = r {
                    let v = match op {
                        UnOp::Not => Some(!v),
                        UnOp::Neg => Some(neg(v, ty)),
                        UnOp::PtrMetadata => None,
                    };
                    match v {
                        Some(v) => state.gm().assign(&l, l_deref, &OpVal::Int(v)),
                        None => state.gm().assign(&l, l_deref, &OpVal::Other),
                    }
                } else {
                    state.gm().assign(&l, l_deref, &OpVal::Other);
                }
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::Discriminant(_) => {
                state.gm().assign(&l, l_deref, &OpVal::Other);
            }
            Rvalue::Aggregate(box kind, rs) => {
                let idx = if let AggregateKind::Adt(_, _, _, _, idx) = kind {
                    idx.as_ref()
                } else {
                    None
                };
                if let Some(field) = idx {
                    assert_eq!(rs.len(), 1);
                    let op = &rs[FieldIdx::from_usize(0)];
                    let v = self.transfer_op(op, state);
                    let l = l.extended(&[AccElem::Field(*field, true)]);
                    let TyKind::Adt(adt_def, gargs) = lty.kind() else { unreachable!() };
                    let variant = adt_def.variant(VariantIdx::from_u32(0));
                    let ty = variant.fields[*field].ty(self.tcx, gargs);
                    state
                        .gm()
                        .assign_with_ty(&l, l_deref, &v, self.ctx.tss.tys[&ty]);
                } else {
                    let tys = match self.ctx.tss.tys[&lty] {
                        TyShape::Array(t, len) => vec![t; *len],
                        TyShape::Struct(_, tys, _) => tys.iter().map(|(_, t)| t).collect(),
                        TyShape::Primitive(_) => unreachable!(),
                    };
                    for ((field, op), ty) in rs.iter_enumerated().zip(&tys) {
                        let v = self.transfer_op(op, state);
                        let l = l.extended(&[AccElem::Field(field, false)]);
                        state.gm().assign_with_ty(&l, l_deref, &v, ty);
                    }
                    for (field, ty) in tys.iter().enumerate().skip(rs.len()) {
                        let v = OpVal::Int(0);
                        let field = FieldIdx::from_usize(field);
                        let l = l.extended(&[AccElem::Field(field, false)]);
                        state.gm().assign_with_ty(&l, l_deref, &v, ty);
                    }
                }
            }
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                let (path, is_deref) = self.acc_path(*r, state);
                let v = OpVal::Place(path, is_deref);
                state.gm().assign(&l, l_deref, &v);
            }
            Rvalue::WrapUnsafeBinder(_, _) => unreachable!(),
        }
    }

    fn transfer_op(&self, op: &Operand<'tcx>, state: &AbsMem) -> OpVal {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let (path, is_deref) = self.acc_path(*place, state);
                if let Some(i) = state.g().get_x_as_int(&path, is_deref) {
                    OpVal::Int(i)
                } else {
                    OpVal::Place(path, is_deref)
                }
            }
            Operand::Constant(box constant) => match constant.const_ {
                Const::Ty(ty, constant) => {
                    let value = constant.to_value();
                    let cv = self.tcx.valtree_to_const_val(value);
                    self.transfer_const_value(cv, ty)
                }
                Const::Unevaluated(constant, ty) => {
                    if ty.is_integral() || ty.is_char() {
                        if let Ok(v) = self.tcx.const_eval_poly(constant.def) {
                            self.transfer_const_value(v, ty)
                        } else {
                            OpVal::Other
                        }
                    } else {
                        OpVal::Other
                    }
                }
                Const::Val(value, ty) => self.transfer_const_value(value, ty),
            },
        }
    }

    fn transfer_const_value(&self, value: ConstValue<'_>, ty: Ty<'_>) -> OpVal {
        match value {
            ConstValue::Scalar(scalar) => match scalar {
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
                        OpVal::Int(v)
                    }
                    TyKind::Uint(uint_ty) => {
                        let v = match uint_ty {
                            UintTy::Usize => i.to_u64() as _,
                            UintTy::U8 => i.to_u8() as _,
                            UintTy::U16 => i.to_u16() as _,
                            UintTy::U32 => i.to_u32() as _,
                            UintTy::U64 => i.to_u64() as _,
                            UintTy::U128 => i.to_u128() as _,
                        };
                        OpVal::Int(v)
                    }
                    TyKind::Char => OpVal::Int(i.to_u32() as _),
                    _ => OpVal::Other,
                },
                Scalar::Ptr(ptr, _) => match self.tcx.global_alloc(ptr.provenance.alloc_id()) {
                    GlobalAlloc::Static(def_id) => {
                        if let Some(def_id) = def_id.as_local() {
                            OpVal::Static(def_id)
                        } else {
                            OpVal::Other
                        }
                    }
                    GlobalAlloc::Memory(_) => OpVal::Other,
                    _ => unreachable!(),
                },
            },
            ConstValue::ZeroSized => OpVal::Other,
            ConstValue::Slice { .. } => unreachable!(),
            ConstValue::Indirect { .. } => unreachable!(),
        }
    }

    pub fn transfer_term(
        &self,
        term: &Terminator<'tcx>,
        dv: Option<&DiscrVal>,
        term_loc: Location,
        state: &AbsMem,
    ) -> Vec<(Location, AbsMem)> {
        match &term.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. } => {
                let location = Location {
                    block: *target,
                    statement_index: 0,
                };
                vec![(location, state.clone())]
            }
            TerminatorKind::InlineAsm { targets, .. } => targets
                .iter()
                .map(|target| {
                    let location = Location {
                        block: *target,
                        statement_index: 0,
                    };
                    (location, state.clone())
                })
                .collect(),
            TerminatorKind::Return | TerminatorKind::Call { target: None, .. } => vec![],
            TerminatorKind::SwitchInt {
                discr: discr_op,
                targets,
            } => match self.transfer_op(discr_op, state) {
                OpVal::Place(discr, is_deref) => match dv {
                    Some(dv) => {
                        assert_eq!(targets.all_targets().len(), 2);
                        let tb = targets.target_for_value(1);
                        let fb = targets.target_for_value(0);
                        assert_ne!(tb, fb);
                        let tl = Location {
                            block: tb,
                            statement_index: 0,
                        };
                        let fl = Location {
                            block: fb,
                            statement_index: 0,
                        };
                        let g = state.g();
                        let v_local = g
                            .get_local_as_int(dv.lhs)
                            .map(|n| (n, dv.rhs))
                            .or_else(|| g.get_local_as_int(dv.rhs).map(|n| (n, dv.lhs)));
                        let mut ts = state.clone();
                        let mut fs = state.clone();
                        if let Some((v, local)) = v_local {
                            let (g, gn) = if dv.equal {
                                (ts.gm(), fs.gm())
                            } else {
                                (fs.gm(), ts.gm())
                            };
                            g.filter_x_int(&AccPath::new(local, vec![]), false, v);
                            gn.filter_x_not_ints(
                                &AccPath::new(local, vec![]),
                                false,
                                std::iter::once(v),
                            );
                        }
                        vec![(tl, ts), (fl, fs)]
                    }
                    None => {
                        let is_bool = discr_op.ty(&self.body.local_decls, self.tcx).is_bool();
                        targets
                            .iter()
                            .map(|(v, target)| {
                                let location = Location {
                                    block: target,
                                    statement_index: 0,
                                };
                                if is_bool {
                                    assert_eq!(v, 0);
                                }
                                let mut state = state.clone();
                                state.gm().filter_x_int(&discr, is_deref, v as i128);
                                (location, state)
                            })
                            .chain(std::iter::once({
                                let location = Location {
                                    block: targets.otherwise(),
                                    statement_index: 0,
                                };
                                let mut state = state.clone();
                                if is_bool {
                                    state.gm().filter_x_int(&discr, is_deref, 1);
                                } else {
                                    state.gm().filter_x_not_ints(
                                        &discr,
                                        is_deref,
                                        targets.iter().map(|(v, _)| v as i128),
                                    )
                                }
                                (location, state)
                            }))
                            .collect()
                    }
                },
                OpVal::Static(_) => unreachable!(),
                OpVal::Int(i) => {
                    let target_opt = targets.iter().find(|(v, _)| i as u128 == *v);
                    let target = if let Some((_, target)) = target_opt {
                        target
                    } else {
                        targets.otherwise()
                    };
                    let location = Location {
                        block: target,
                        statement_index: 0,
                    };
                    vec![(location, state.clone())]
                }
                OpVal::Other => targets
                    .all_targets()
                    .iter()
                    .map(|target| {
                        let location = Location {
                            block: *target,
                            statement_index: 0,
                        };
                        (location, state.clone())
                    })
                    .collect(),
            },
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } => {
                assert!(destination.projection.is_empty());
                let mut state = state.clone();
                state.gm().invalidate_symbolic(destination.local);
                let location = Location {
                    block: *target,
                    statement_index: 0,
                };
                let (l, l_deref) = self.acc_path(*destination, &state);
                if let Some(writes) = self.get_assign_writes(term_loc) {
                    let strong_update = state.g().strong_update_loc(l.clone(), l_deref);
                    state.gm().invalidate(
                        self.ctx.local_def_id,
                        strong_update.as_ref(),
                        !l_deref,
                        self.ctx.may_points_to,
                        writes,
                    );
                }
                let need_update = match func {
                    Operand::Copy(func) | Operand::Move(func) => {
                        assert!(func.projection.is_empty());
                        let callees = self.resolve_indirect_call(term_loc);
                        self.transfer_intra_call(callees, &mut state);
                        true
                    }
                    Operand::Constant(box constant) => {
                        let Const::Val(value, ty) = constant.const_ else { unreachable!() };
                        assert!(matches!(value, ConstValue::ZeroSized));
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        let namev: Vec<_> = self
                            .tcx
                            .def_path(*def_id)
                            .data
                            .into_iter()
                            .map(|data| data.to_string())
                            .collect();
                        let is_extern = namev.iter().any(|s| s.starts_with("{extern#"));
                        let seg = |i: usize| namev.get(i).map(|s| s.as_str()).unwrap_or_default();
                        let name = (seg(0), seg(1), seg(2), seg(3));
                        let sig = self.tcx.fn_sig(def_id).skip_binder();
                        let inputs = sig.inputs().skip_binder();
                        if let Some(local_def_id) = def_id.as_local() {
                            if self.tcx.impl_of_method(*def_id).is_some() {
                                self.transfer_method_call(
                                    local_def_id,
                                    args,
                                    &l,
                                    term_loc,
                                    &mut state,
                                );
                                false
                            } else if is_extern {
                                self.transfer_c_call(
                                    namev.last().unwrap(),
                                    inputs,
                                    args,
                                    &mut state,
                                );
                                true
                            } else {
                                self.transfer_intra_call(&[local_def_id], &mut state);
                                true
                            }
                        } else {
                            self.transfer_rust_call(name, args, destination, &mut state);
                            false
                        }
                    }
                };
                if need_update {
                    let ty = Place::ty(destination, &self.body.local_decls, self.tcx).ty;
                    state
                        .gm()
                        .assign_with_ty(&l, l_deref, &OpVal::Other, self.ctx.tss.tys[&ty]);
                }
                vec![(location, state)]
            }
            _ => unreachable!(),
        }
    }

    fn transfer_intra_call(&self, callees: &[LocalDefId], state: &mut AbsMem) {
        if let Some(writes) = self.get_call_writes(callees) {
            state.gm().invalidate(
                self.ctx.local_def_id,
                None,
                false,
                self.ctx.may_points_to,
                &writes,
            );
        }
    }

    fn transfer_method_call(
        &self,
        f: LocalDefId,
        args: &[Spanned<Operand<'tcx>>],
        dst: &AccPath,
        loc: Location,
        state: &mut AbsMem,
    ) {
        let l = args[0].node.place().unwrap();
        let (mut l, l_deref) = self.acc_path(l, state);
        assert!(!l_deref);

        if let Some(writes) = self.get_bitfield_writes(loc) {
            let strong_update = state.g().strong_update_loc(l.clone(), true);
            state.gm().invalidate(
                self.ctx.local_def_id,
                strong_update.as_ref(),
                false,
                self.ctx.may_points_to,
                writes,
            );
        }

        let (ty, method) = andersen::receiver_and_method(f, self.tcx).unwrap();
        match args.len() {
            1 => {
                let offset = self.ctx.tss.bitfields[&ty].name_to_idx[&method];
                let mut r = l;
                r.extend_projection(&[AccElem::Field(offset, false)]);
                let r = OpVal::Place(r, true);
                state.gm().assign(dst, false, &r);
            }
            2 => {
                let field = method.strip_prefix("set_").unwrap();
                let offset = self.ctx.tss.bitfields[&ty].name_to_idx[field];
                l.extend_projection(&[AccElem::Field(offset, false)]);
                let r = self.transfer_op(&args[1].node, state);
                state.gm().assign(&l, true, &r);
            }
            _ => unreachable!(),
        }
    }

    fn transfer_c_call(
        &self,
        name: &str,
        inputs: &[Ty<'_>],
        args: &[Spanned<Operand<'tcx>>],
        state: &mut AbsMem,
    ) {
        if name == "realloc" || name == "free" {
            return;
        }
        let args = inputs.iter().zip(args).filter_map(|(ty, arg)| {
            if ty.is_mutable_ptr()
                && let Some(arg) = arg.node.place()
            {
                assert!(arg.projection.is_empty());
                return Some(arg.local);
            }
            None
        });
        if let Some(writes) = self.get_arg_writes(args) {
            state.gm().invalidate(
                self.ctx.local_def_id,
                None,
                false,
                self.ctx.may_points_to,
                &writes,
            );
        }
    }

    fn transfer_rust_call(
        &self,
        name: (&str, &str, &str, &str),
        args: &[Spanned<Operand<'tcx>>],
        dst: &Place<'tcx>,
        state: &mut AbsMem,
    ) {
        let (d, d_deref) = self.acc_path(*dst, state);
        assert!(!d_deref);
        match name {
            ("slice", _, "as_ptr" | "as_mut_ptr", _) => {
                let ptr = args[0].node.place().unwrap();
                let (mut ptr, ptr_deref) = self.acc_path(ptr, state);
                assert!(!ptr_deref);
                ptr.projection.push(AccElem::num_index(0));
                state.gm().x_eq_ref_y(&d, &ptr, true);
            }
            ("ptr", _, _, "offset") => {
                let ptr = args[0].node.place().unwrap();
                let (ptr, ptr_deref) = self.acc_path(ptr, state);
                assert!(!ptr_deref);
                let idx = self.transfer_op(&args[1].node, state);
                state.gm().x_eq_offset(&d, &ptr, idx);
            }
            _ => {}
        }
    }

    fn acc_path(&self, place: Place<'tcx>, state: &AbsMem) -> (AccPath, bool) {
        AccPath::from_place(place, state, &self.body.local_decls, self.tcx)
    }
}

macro_rules! create_div_fn {
    ($name:ident, $op:tt) => {
        fn $name(n: i128, m: i128, ty: Ty<'_>) -> i128 {
            match ty.kind() {
                TyKind::Int(int_ty) => {
                    match int_ty {
                        IntTy::Isize => (n as isize $op m as isize) as i128,
                        IntTy::I8 => (n as i8 $op m as i8) as i128,
                        IntTy::I16 => (n as i16 $op m as i16) as i128,
                        IntTy::I32 => (n as i32 $op m as i32) as i128,
                        IntTy::I64 => (n as i64 $op m as i64) as i128,
                        IntTy::I128 => (n as i128 $op m as i128) as i128,
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        UintTy::Usize => (n as usize $op m as usize) as i128,
                        UintTy::U8 => (n as u8 $op m as u8) as i128,
                        UintTy::U16 => (n as u16 $op m as u16) as i128,
                        UintTy::U32 => (n as u32 $op m as u32) as i128,
                        UintTy::U64 => (n as u64 $op m as u64) as i128,
                        UintTy::U128 => (n as u128 $op m as u128) as i128,
                    }
                }
                _ => panic!(),
            }
        }
    }
}

create_div_fn!(div, /);
create_div_fn!(rem, %);

macro_rules! create_shift_fn {
    ($name:ident, $op:tt) => {
        fn $name(n: i128, m: i128, ty: Ty<'_>) -> i128 {
            match ty.kind() {
                TyKind::Int(int_ty) => {
                    match int_ty {
                        IntTy::Isize => ((n as isize) $op m) as i128,
                        IntTy::I8 => ((n as i8) $op m) as i128,
                        IntTy::I16 => ((n as i16) $op m) as i128,
                        IntTy::I32 => ((n as i32) $op m) as i128,
                        IntTy::I64 => ((n as i64) $op m) as i128,
                        IntTy::I128 => ((n as i128) $op m) as i128,
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        UintTy::Usize => ((n as usize) $op m) as i128,
                        UintTy::U8 => ((n as u8) $op m) as i128,
                        UintTy::U16 => ((n as u16) $op m) as i128,
                        UintTy::U32 => ((n as u32) $op m) as i128,
                        UintTy::U64 => ((n as u64) $op m) as i128,
                        UintTy::U128 => ((n as u128) $op m) as i128,
                    }
                }
                _ => panic!(),
            }
        }
    }
}

create_shift_fn!(shl, <<);
create_shift_fn!(shr, >>);

macro_rules! create_cmp_fn {
    ($name:ident, $op:tt) => {
        fn $name(n: i128, m: i128, ty: Ty<'_>) -> i128 {
            match ty.kind() {
                TyKind::Int(int_ty) => {
                    match int_ty {
                        IntTy::Isize => ((n as isize) $op m as isize) as i128,
                        IntTy::I8 => ((n as i8) $op m as i8) as i128,
                        IntTy::I16 => ((n as i16) $op m as i16) as i128,
                        IntTy::I32 => ((n as i32) $op m as i32) as i128,
                        IntTy::I64 => ((n as i64) $op m as i64) as i128,
                        IntTy::I128 => ((n as i128) $op m as i128) as i128,
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        UintTy::Usize => ((n as usize) $op m as usize) as i128,
                        UintTy::U8 => ((n as u8) $op m as u8) as i128,
                        UintTy::U16 => ((n as u16) $op m as u16) as i128,
                        UintTy::U32 => ((n as u32) $op m as u32) as i128,
                        UintTy::U64 => ((n as u64) $op m as u64) as i128,
                        UintTy::U128 => ((n as u128) $op (m as u128)) as i128,
                    }
                }
                TyKind::Bool => ((n != 0) $op (m != 0)) as i128,
                _ => panic!(),
            }
        }
    }
}

create_cmp_fn!(lt, <);
create_cmp_fn!(le, <=);
create_cmp_fn!(ge, >=);
create_cmp_fn!(gt, >);

macro_rules! create_cast_fn {
    ($name:ident, $typ:ty) => {
        fn $name(n: i128, ty: Ty<'_>) -> i128 {
            #[allow(trivial_numeric_casts)]
            match ty.kind() {
                TyKind::Int(int_ty) => match int_ty {
                    IntTy::Isize => (n as isize) as $typ as i128,
                    IntTy::I8 => (n as i8) as $typ as i128,
                    IntTy::I16 => (n as i16) as $typ as i128,
                    IntTy::I32 => (n as i32) as $typ as i128,
                    IntTy::I64 => (n as i64) as $typ as i128,
                    IntTy::I128 => (n as i128) as $typ as i128,
                },
                TyKind::Uint(uint_ty) => match uint_ty {
                    UintTy::Usize => (n as usize) as $typ as i128,
                    UintTy::U8 => (n as u8) as $typ as i128,
                    UintTy::U16 => (n as u16) as $typ as i128,
                    UintTy::U32 => (n as u32) as $typ as i128,
                    UintTy::U64 => (n as u64) as $typ as i128,
                    UintTy::U128 => (n as u128) as $typ as i128,
                },
                TyKind::Bool => (n != 0) as $typ as i128,
                TyKind::Char => (n as u32) as $typ as i128,
                _ => panic!(),
            }
        }
    };
}

create_cast_fn!(to_i8, i8);
create_cast_fn!(to_i16, i16);
create_cast_fn!(to_i32, i32);
create_cast_fn!(to_i64, i64);
create_cast_fn!(to_i128, i128);
create_cast_fn!(to_isize, isize);
create_cast_fn!(to_u8, u8);
create_cast_fn!(to_u16, u16);
create_cast_fn!(to_u32, u32);
create_cast_fn!(to_u64, u64);
create_cast_fn!(to_u128, u128);
create_cast_fn!(to_usize, usize);

fn neg(n: i128, ty: Ty<'_>) -> i128 {
    match ty.kind() {
        TyKind::Int(int_ty) => match int_ty {
            IntTy::Isize => -(n as isize) as i128,
            IntTy::I8 => -(n as i8) as i128,
            IntTy::I16 => -(n as i16) as i128,
            IntTy::I32 => -(n as i32) as i128,
            IntTy::I64 => -(n as i64) as i128,
            IntTy::I128 => -n,
        },
        _ => panic!(),
    }
}
