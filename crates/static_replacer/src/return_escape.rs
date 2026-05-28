use rustc_hash::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        Const, ConstOperand, ConstValue, Operand, Place, RETURN_PLACE, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
        interpret::{GlobalAlloc, Scalar},
    },
    ty::{TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

type StaticSources = Vec<FxHashSet<LocalDefId>>;

pub(crate) fn statics_returned_by_non_raw_address(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    let mut result = FxHashSet::default();

    for def_id in tcx.hir_body_owners() {
        if !matches!(tcx.def_kind(def_id), DefKind::Fn) {
            continue;
        }

        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        if body.local_decls[RETURN_PLACE].ty.is_raw_ptr() {
            continue;
        }

        let mut state = vec![FxHashSet::default(); body.local_decls.len()];
        loop {
            let mut changed = false;
            for block in body.basic_blocks.iter() {
                for stmt in &block.statements {
                    changed |= transfer_stmt(stmt, &mut state, tcx);
                }
                changed |= transfer_terminator(block.terminator(), &mut state, tcx);
            }
            if !changed {
                break;
            }
        }

        result.extend(state[RETURN_PLACE.index()].iter().copied());
    }

    result
}

fn transfer_stmt(stmt: &Statement<'_>, state: &mut StaticSources, tcx: TyCtxt<'_>) -> bool {
    let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
        return false;
    };
    let Some(dst) = place.as_local() else {
        return false;
    };
    let src = rvalue_sources(rvalue, state, tcx);
    union_into(&mut state[dst.index()], src)
}

fn transfer_terminator(
    terminator: &Terminator<'_>,
    state: &mut StaticSources,
    tcx: TyCtxt<'_>,
) -> bool {
    let TerminatorKind::Call {
        func,
        args,
        destination,
        ..
    } = &terminator.kind
    else {
        return false;
    };
    if !is_transparent_call(func, tcx) {
        return false;
    }
    let Some(dst) = destination.as_local() else {
        return false;
    };
    let Some(arg) = args.first() else {
        return false;
    };
    let src = operand_sources(&arg.node, state, tcx);
    union_into(&mut state[dst.index()], src)
}

fn rvalue_sources(
    rvalue: &Rvalue<'_>,
    state: &StaticSources,
    tcx: TyCtxt<'_>,
) -> FxHashSet<LocalDefId> {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_sources(operand, state, tcx),
        Rvalue::CopyForDeref(place) => place_sources(*place, state),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => reborrow_sources(*place, state),
        Rvalue::ThreadLocalRef(def_id) => def_id.as_local().into_iter().collect(),
        Rvalue::Aggregate(_, operands) => {
            let mut sources = FxHashSet::default();
            for operand in operands {
                union_into(&mut sources, operand_sources(operand, state, tcx));
            }
            sources
        }
        _ => FxHashSet::default(),
    }
}

fn operand_sources(
    operand: &Operand<'_>,
    state: &StaticSources,
    tcx: TyCtxt<'_>,
) -> FxHashSet<LocalDefId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_sources(*place, state),
        Operand::Constant(box constant) => constant_static(constant, tcx)
            .into_iter()
            .collect::<FxHashSet<_>>(),
    }
}

fn place_sources(place: Place<'_>, state: &StaticSources) -> FxHashSet<LocalDefId> {
    if place.is_indirect_first_projection() {
        FxHashSet::default()
    } else {
        state[place.local.index()].clone()
    }
}

fn reborrow_sources(place: Place<'_>, state: &StaticSources) -> FxHashSet<LocalDefId> {
    // Static addresses can lower to a constant pointer local followed by `&*p`.
    // Preserve that source without treating ordinary deref copies as transparent.
    state[place.local.index()].clone()
}

fn constant_static(constant: &ConstOperand<'_>, tcx: TyCtxt<'_>) -> Option<LocalDefId> {
    if let Const::Val(ConstValue::Scalar(Scalar::Ptr(ptr, _)), _) = constant.const_
        && let GlobalAlloc::Static(def_id) = tcx.global_alloc(ptr.provenance.alloc_id())
    {
        def_id.as_local()
    } else {
        None
    }
}

fn is_transparent_call(func: &Operand<'_>, tcx: TyCtxt<'_>) -> bool {
    let Operand::Constant(box constant) = func else {
        return false;
    };
    let Const::Val(ConstValue::ZeroSized, ty) = constant.const_ else {
        return false;
    };
    let TyKind::FnDef(def_id, _) = ty.kind() else {
        return false;
    };
    let name: Vec<_> = tcx
        .def_path(*def_id)
        .data
        .into_iter()
        .map(|data| data.to_string())
        .collect();
    let seg = |i: usize| name.get(i).map(|s| s.as_str()).unwrap_or_default();
    matches!(
        (seg(0), seg(1), seg(2), seg(3)),
        ("option" | "result", _, "unwrap" | "expect", _)
    )
}

fn union_into(dst: &mut FxHashSet<LocalDefId>, src: FxHashSet<LocalDefId>) -> bool {
    let mut changed = false;
    for def_id in src {
        changed |= dst.insert(def_id);
    }
    changed
}
