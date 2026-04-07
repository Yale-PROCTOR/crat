use std::ops::Range;

use either::Either::Left;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        Body, ClearCrossCrate, Local, LocalInfo, Location, Operand, Place, RETURN_PLACE, Rvalue,
        StatementKind, TerminatorKind, VarDebugInfoContents,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::TyKind,
};

use super::{Ownership, whole_program::WholeProgramResults};
use crate::{
    analyses::ownership::{
        discretization::{self, Discretization},
        ssa::{AnalysisResults, FnResults},
        vec_vec::VecVec,
    },
    utils::rustc::RustProgram,
};

rustc_index::newtype_index! {
    #[debug_format = "{}"]
    pub struct Var {}
}

pub type SolidifiedOwnershipSchemes = TypeQualifiers<Ownership>;

pub struct TypeQualifiers<Qualifier> {
    struct_fields: discretization::StructFields<Var>,
    fn_locals: discretization::FnLocals<Var>,
    model: IndexVec<Var, Qualifier>,
}

impl<Qualifier> TypeQualifiers<Qualifier> {
    pub fn new(
        struct_fields: discretization::StructFields<Var>,
        fn_locals: discretization::FnLocals<Var>,
        model: IndexVec<Var, Qualifier>,
    ) -> Self {
        Self {
            struct_fields,
            fn_locals,
            model,
        }
    }

    pub fn fn_results<'me>(&'me self, r#fn: &DefId) -> FnResult<'me, Qualifier> {
        let locals = &self.fn_locals.0.contents[self.fn_locals.0.did_idx[r#fn]];
        FnResult {
            locals,
            model: &self.model,
        }
    }

    #[cfg(test)]
    pub fn struct_results(&self, r#struct: &DefId) -> impl Iterator<Item = &[Qualifier]> {
        self.struct_fields
            .fields(r#struct)
            .map(|Range { start, end }| &self.model.raw[start.index()..end.index()])
    }

    pub fn struct_field_result(&self, r#struct: &DefId, f: usize) -> &[Qualifier] {
        let Range { start, end } = self.struct_fields.field(r#struct, f);
        &self.model.raw[start.index()..end.index()]
    }

    #[cfg(test)]
    pub fn fn_sig(
        &self,
        r#fn: &DefId,
        tcx: rustc_middle::ty::TyCtxt,
    ) -> impl Iterator<Item = &[Qualifier]> {
        let fn_result = self.fn_results(r#fn);
        let body = &tcx
            .mir_drops_elaborated_and_const_checked(r#fn.expect_local())
            .borrow();
        fn_result.results().take(body.arg_count + 1)
    }

    pub fn place_result<'tcx>(&self, body: &Body<'tcx>, place: &Place<'tcx>) -> &[Qualifier] {
        let mut ptr_kinds = self
            .fn_results(&body.source.def_id())
            .local_result(place.local);
        let mut ptr_kinds_index = 0;
        let mut ty = body.local_decls[place.local].ty;
        for proj in place.projection {
            match proj {
                rustc_middle::mir::ProjectionElem::Deref => {
                    ptr_kinds_index += 1;
                    ty = ty.builtin_deref(true).unwrap();
                }
                rustc_middle::mir::ProjectionElem::Field(f, field_ty) => {
                    assert_eq!(ptr_kinds_index, ptr_kinds.len());
                    let adt_def = ty.ty_adt_def().unwrap();
                    ptr_kinds = self.struct_field_result(&adt_def.did(), f.index());
                    ptr_kinds_index = 0;
                    ty = field_ty;
                }
                rustc_middle::mir::ProjectionElem::Index(_) => {
                    ty = ty.builtin_index().unwrap();
                }
                _ => unreachable!(),
            }
        }

        &ptr_kinds[ptr_kinds_index..]
    }
}

#[derive(Clone, Copy)]
pub struct FnResult<'me, Domain> {
    locals: &'me [Var],
    model: &'me IndexVec<Var, Domain>,
}

impl<'me, Domain> FnResult<'me, Domain> {
    #[cfg(test)]
    pub fn results(self) -> impl Iterator<Item = &'me [Domain]> {
        self.locals
            .array_windows()
            .map(|&[start, end]| &self.model.raw[start.index()..end.index()])
    }

    pub fn local_result(self, local: Local) -> &'me [Domain] {
        let (start, end) = (self.locals[local.index()], self.locals[local.index() + 1]);
        &self.model.raw[start.index()..end.index()]
    }
}

impl<'tcx> WholeProgramResults<'tcx> {
    pub fn solidify(&self, program: &RustProgram<'tcx>) -> SolidifiedOwnershipSchemes {
        let structs = program
            .structs
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();

        let mut model = IndexVec::new();
        let mut next: Var = model.next_index();
        let mut did_idx = FxHashMap::default();
        did_idx.reserve(structs.len());
        let mut vars = VecVec::with_capacity(structs.len(), structs.len() * 4);

        for (idx, r#struct) in structs.iter().enumerate() {
            did_idx.insert(*r#struct, idx);

            let fields_ownership = self.fields(r#struct);
            for ownership in fields_ownership {
                model.extend(ownership.iter().copied());
                vars.push_inner(next);
                next += ownership.len();
                assert_eq!(model.next_index(), next);
            }
            vars.push_inner(next);
            vars.push();
        }
        let vars = vars.done();
        let struct_fields = discretization::StructFields(Discretization {
            did_idx,
            contents: vars,
        });

        let mut did_idx = FxHashMap::default();
        did_idx.reserve(fns.len());
        let mut vars = VecVec::with_capacity(fns.len(), fns.len() * 15);
        for (idx, r#fn) in fns.iter().enumerate() {
            did_idx.insert(*r#fn, idx);

            let body = &*program
                .tcx
                .mir_drops_elaborated_and_const_checked(r#fn.expect_local())
                .borrow();

            let mut locals = Vec::with_capacity(body.local_decls.len());
            for local_decl in body.local_decls.iter() {
                fn mir_ty_ptr_count(mut ty: rustc_middle::ty::Ty<'_>) -> usize {
                    let mut cnt = 0;
                    loop {
                        if let Some(inner) = ty.builtin_index() {
                            ty = inner;
                            continue;
                        }
                        if let Some(inner_mut) = ty.builtin_deref(true) {
                            ty = inner_mut;
                            cnt += 1;
                            continue;
                        }
                        break;
                    }
                    cnt
                }
                let ptr_depth = mir_ty_ptr_count(local_decl.ty);
                locals.push(smallvec::smallvec![Ownership::Transient; ptr_depth]);
            }

            for (param, ownership) in self.fn_sig(*r#fn).zip(&mut locals) {
                if matches!(param, Some(param) if param.is_output()) && !ownership.is_empty() {
                    ownership[0] = Ownership::Owning
                }
            }

            let ownership_scheme = self.fn_results(*r#fn).unwrap();

            let mut proxy_temporaries = FxHashSet::default();
            for bb_data in body.basic_blocks.iter() {
                let Some(terminator) = &bb_data.terminator else {
                    continue;
                };
                if let TerminatorKind::Call { args, .. } = &terminator.kind {
                    proxy_temporaries.extend(
                        args.iter()
                            .filter_map(|arg| arg.node.place().and_then(|arg| arg.as_local())),
                    )
                }
            }
            for (local, local_decl) in body.local_decls.iter_enumerated() {
                if matches!(
                    local_decl.local_info.as_ref(),
                    ClearCrossCrate::Set(local_info)
                        if matches!(local_info.as_ref(), LocalInfo::DerefTemp)
                ) {
                    proxy_temporaries.insert(local);
                }
            }

            for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                for statement_index in
                    0usize..(bb_data.statements.len() + bb_data.terminator.is_some() as usize)
                {
                    let location = Location {
                        block: bb,
                        statement_index,
                    };

                    let location_results = ownership_scheme.location_results(location);
                    for (local, consume) in location_results {
                        let solidified_ownership: &mut smallvec::SmallVec<[Ownership; 3]> =
                            &mut locals[local.index()];
                        for (solidified_ownership, r#use, def) in
                            itertools::izip!(solidified_ownership, consume.r#use, consume.def)
                        {
                            if r#use.is_owning() || def.is_owning() {
                                *solidified_ownership = Ownership::Owning;
                            }
                        }
                    }

                    let Left(stmt) = body.stmt_at(location) else { continue };
                    let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else { continue };
                    if matches!(place.as_local(), Some(local) if proxy_temporaries.contains(&local))
                    {
                        let mut by_ref = false;
                        let rplace = match rvalue {
                            Rvalue::RawPtr(_, rplace) | Rvalue::Ref(_, _, rplace) => {
                                by_ref = true;
                                rplace
                            }
                            Rvalue::Cast(_, Operand::Copy(rplace) | Operand::Move(rplace), _) => {
                                rplace
                            }
                            Rvalue::Use(Operand::Copy(rplace) | Operand::Move(rplace)) => rplace,
                            Rvalue::CopyForDeref(rplace) => rplace,
                            _ => continue,
                        };

                        let mut ownership: &[Ownership] = &locals[rplace.local.index()][..];
                        if ownership.is_empty() {
                            continue;
                        }
                        let mut index = 0;
                        let mut ty = body.local_decls[rplace.local].ty;

                        for proj in rplace.projection {
                            match proj {
                                rustc_middle::mir::ProjectionElem::Deref => {
                                    index += 1;
                                    ty = ty.builtin_deref(true).unwrap();
                                }
                                rustc_middle::mir::ProjectionElem::Field(f, field_ty) => {
                                    assert_eq!(index, ownership.len());
                                    let Some(adt_def) = ty.ty_adt_def() else {
                                        continue;
                                    };
                                    if adt_def.is_union() {
                                        ownership = &[];
                                        continue;
                                    }
                                    let Range { start, end } =
                                        struct_fields.field(&adt_def.did(), f.index());
                                    ownership = &model.raw[start.index()..end.index()];
                                    index = 0;
                                    ty = field_ty;
                                }
                                rustc_middle::mir::ProjectionElem::Index(_) => {
                                    ty = ty.builtin_index().unwrap();
                                }
                                _ => unreachable!(),
                            }
                        }

                        let ownership =
                            smallvec::SmallVec::<[_; 2]>::from_slice(&ownership[index..]);

                        let proxy_temporary = if by_ref {
                            &mut locals[place.local.index()][1..]
                        } else {
                            &mut locals[place.local.index()]
                        };

                        for (proxy, ownership) in proxy_temporary.iter_mut().zip(ownership) {
                            *proxy = ownership
                        }
                    }
                }
            }

            // Fallback: if a user-visible raw-pointer local is derived from allocator
            // results and the allocation root is either freed or returned, treat it as owning.
            apply_allocator_owner_fallback(body, program.tcx, &mut locals);

            for local in locals {
                vars.push_inner(next);
                next += local.len();
                model.extend(local.into_iter());
                assert_eq!(model.next_index(), next);
            }
            vars.push_inner(next);
            vars.push();
        }
        let vars = vars.done();
        let fn_locals = discretization::FnLocals(Discretization {
            did_idx,
            contents: vars,
        });

        let solidified = TypeQualifiers::new(struct_fields, fn_locals, model);

        sanity_check(self, &solidified, program, &fns);

        solidified
    }
}

fn rhs_local_from_rvalue<'tcx>(rvalue: &Rvalue<'tcx>) -> Option<Local> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::WrapUnsafeBinder(Operand::Copy(place) | Operand::Move(place), _) => {
            place.as_local()
        }
        Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => place.as_local(),
        Rvalue::CopyForDeref(place) => place.as_local(),
        _ => None,
    }
}

fn allocator_kind<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> Option<AllocatorCallKind> {
    let func = func.constant()?;
    let TyKind::FnDef(def_id, _) = func.ty().kind() else {
        return None;
    };
    let symbol = tcx.item_name(*def_id);
    match symbol.as_str() {
        "malloc" | "calloc" | "realloc" | "strdup" => Some(AllocatorCallKind::Alloc),
        "free" => Some(AllocatorCallKind::Free),
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AllocatorCallKind {
    Alloc,
    Free,
}

fn apply_allocator_owner_fallback<'tcx>(
    body: &Body<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    locals: &mut [smallvec::SmallVec<[Ownership; 3]>],
) {
    let mut user_visible_locals: FxHashSet<Local> = FxHashSet::default();
    user_visible_locals.extend(body.var_debug_info.iter().filter_map(|info| {
        let VarDebugInfoContents::Place(place) = &info.value else {
            return None;
        };
        place.as_local()
    }));

    let mut origins = IndexVec::from_elem_n(FxHashSet::<Local>::default(), body.local_decls.len());

    // Grow allocator-root provenance through local copy/cast chains.
    let mut changed = true;
    while changed {
        changed = false;

        for bb_data in body.basic_blocks.iter() {
            for statement in &bb_data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let Some(lhs_local) = lhs.as_local() else {
                    continue;
                };

                let Some(rhs_local) = rhs_local_from_rvalue(rvalue) else {
                    continue;
                };

                let rhs_roots = origins[rhs_local].clone();
                if !rhs_roots.is_empty() {
                    let before = origins[lhs_local].len();
                    origins[lhs_local].extend(rhs_roots);
                    if origins[lhs_local].len() != before {
                        changed = true;
                    }
                }
            }

            let Some(terminator) = &bb_data.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func, destination, ..
            } = &terminator.kind
            else {
                continue;
            };
            if !matches!(allocator_kind(tcx, func), Some(AllocatorCallKind::Alloc)) {
                continue;
            }
            let Some(dest_local) = destination.as_local() else {
                continue;
            };
            if origins[dest_local].insert(dest_local) {
                changed = true;
            }
        }
    }

    // Track locals that can receive pointer values with no allocator-root provenance.
    // If such flow reaches a local, do not promote it via fallback.
    let mut has_non_root_flow = IndexVec::from_elem_n(false, body.local_decls.len());
    let mut direct_internal_alloc_flow = IndexVec::from_elem_n(false, body.local_decls.len());
    let mut changed = true;
    while changed {
        changed = false;
        for bb_data in body.basic_blocks.iter() {
            for statement in &bb_data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let Some(lhs_local) = lhs.as_local() else {
                    continue;
                };
                if !body.local_decls[lhs_local].ty.is_raw_ptr() {
                    continue;
                }

                let Some(rhs_local) = rhs_local_from_rvalue(rvalue) else {
                    continue;
                };

                let rhs_is_external_provenance = rhs_local.index() <= body.arg_count
                    || user_visible_locals.contains(&rhs_local)
                    || matches!(
                        body.local_decls[rhs_local].local_info.as_ref(),
                        ClearCrossCrate::Set(local_info)
                            if matches!(local_info.as_ref(), LocalInfo::User(_))
                    );

                let rhs_non_root = has_non_root_flow[rhs_local]
                    || (origins[rhs_local].is_empty() && rhs_is_external_provenance);
                if rhs_non_root && !has_non_root_flow[lhs_local] {
                    has_non_root_flow[lhs_local] = true;
                    changed = true;
                }

                let rhs_is_internal_alloc_chain = !origins[rhs_local].is_empty()
                    && !user_visible_locals.contains(&rhs_local)
                    && !matches!(
                        body.local_decls[rhs_local].local_info.as_ref(),
                        ClearCrossCrate::Set(local_info)
                            if matches!(local_info.as_ref(), LocalInfo::User(_))
                    );
                if rhs_is_internal_alloc_chain && !direct_internal_alloc_flow[lhs_local] {
                    direct_internal_alloc_flow[lhs_local] = true;
                    changed = true;
                }
            }
        }
    }

    let mut promoted_roots: FxHashSet<Local> = FxHashSet::default();

    for bb_data in body.basic_blocks.iter() {
        let Some(terminator) = &bb_data.terminator else {
            continue;
        };

        match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => {
                let is_allocator_free =
                    matches!(allocator_kind(tcx, func), Some(AllocatorCallKind::Free));

                let is_sink_like_wrapper = if let Some(func_const) = func.constant() {
                    if let TyKind::FnDef(def_id, _) = func_const.ty().kind() {
                        let symbol = tcx.item_name(*def_id);
                        let name = symbol.as_str();
                        name.contains("free")
                            || name.contains("destroy")
                            || name.contains("cleanup")
                            || name.contains("dealloc")
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !(is_allocator_free || is_sink_like_wrapper) {
                    continue;
                }

                if let Some(arg_local) = args
                    .first()
                    .and_then(|arg| arg.node.place())
                    .and_then(|place| place.as_local())
                {
                    promoted_roots.extend(origins[arg_local].iter().copied());
                }
            }
            TerminatorKind::Return => {
                promoted_roots.extend(origins[RETURN_PLACE].iter().copied());
            }
            _ => {}
        }
    }

    if promoted_roots.is_empty() && !direct_internal_alloc_flow.iter().any(|&flag| flag) {
        return;
    }

    for (local, local_decl) in body.local_decls.iter_enumerated() {
        if !local_decl.ty.is_raw_ptr() {
            continue;
        }
        if !user_visible_locals.contains(&local)
            && !matches!(
                local_decl.local_info.as_ref(),
                ClearCrossCrate::Set(local_info) if matches!(local_info.as_ref(), LocalInfo::User(_))
            )
        {
            continue;
        }
        if locals[local.index()].is_empty() {
            continue;
        }
        if has_non_root_flow[local] {
            continue;
        }
        if direct_internal_alloc_flow[local]
            || origins[local]
                .iter()
                .any(|root| promoted_roots.contains(root))
        {
            locals[local.index()][0] = Ownership::Owning;
        }
    }
}

fn sanity_check<'tcx>(
    ownership_schemes: &WholeProgramResults<'tcx>,
    solidifed_ownership_schemes: &SolidifiedOwnershipSchemes,
    program: &RustProgram<'tcx>,
    fns: &[DefId],
) {
    for r#fn in fns {
        let body = &*program
            .tcx
            .mir_drops_elaborated_and_const_checked(r#fn.expect_local())
            .borrow();

        let ownership_schemes = ownership_schemes.fn_results(*r#fn).unwrap();

        let mut sanity_checker = SanityCheck {
            ownership_schemes: &ownership_schemes,
            solidifed: solidifed_ownership_schemes,
            body,
            err_locations: Vec::new(),
        };

        sanity_checker.visit_body(body);

        let err_locations = sanity_checker.err_locations;

        for location in err_locations {
            let stmt = body.stmt_at(location);
            let span = match stmt {
                either::Either::Left(stmt) => stmt.source_info.span,
                either::Either::Right(term) => term.source_info.span,
            };

            if let Ok(source_text) = program.tcx.sess.source_map().span_to_snippet(span) {
                tracing::error!("semantics changed: {source_text} @ {:?}", span)
            } else {
                tracing::error!("semantics changed @ {:?}", span)
            }
        }
    }
}

/// This does not work for more than two dereferences
struct SanityCheck<'me, 'tcx> {
    ownership_schemes: &'me <WholeProgramResults<'tcx> as AnalysisResults<'me>>::FnResults,
    solidifed: &'me SolidifiedOwnershipSchemes,
    body: &'me Body<'tcx>,
    err_locations: Vec<Location>,
}

impl<'me, 'tcx> Visitor<'tcx> for SanityCheck<'me, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::CopyForDeref(place) = rvalue
            && matches!(self
                .solidifed
                .place_result(self.body, &Place::from(place.local))
                .chunks(2)
                .next(),
                Some(&[ownership1, ownership2]) if ownership1.is_owning() && ownership2.is_owning())
            && let Some(flowing) = self.ownership_schemes.local_result(place.local, location)
            && flowing.r#use.len() >= 2
            && !(flowing.r#use[1].is_owning() && flowing.def[1].is_owning())
        {
            self.err_locations.push(location);
        }
        if let Rvalue::CopyForDeref(..) = rvalue {
        } else {
            self.super_rvalue(rvalue, location)
        }
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if matches!(self
            .solidifed
            .place_result(self.body, &Place::from(local))
            .first()
            .copied(), Some(ownership) if ownership.is_owning())
            && matches!(
                context,
                PlaceContext::MutatingUse(MutatingUseContext::Projection)
                    | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection)
            )
            && let Some(flowing) = self.ownership_schemes.local_result(local, location)
            && (flowing.is_use() && !flowing.r#use[0].is_owning()
                || !(flowing.is_use()
                    || flowing.r#use[0].is_owning() && flowing.def[0].is_owning()))
        {
            self.err_locations.push(location);
        }
    }
}
