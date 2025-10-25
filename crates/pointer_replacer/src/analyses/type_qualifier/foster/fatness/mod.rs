use std::ops::Range;

use rustc_middle::mir::{
    HasLocalDecls, Location, Operand, Place, ProjectionElem, Rvalue, Terminator, visit::Visitor,
};
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        lattice::{HasBottom, HasTop, Lattice},
        mir::{self, CallKind, TerminatorExt},
        type_qualifier::foster::{
            BooleanLattice, InferCtxt, StructFields, TypeQualifiers, Var,
            constraint_system::{BooleanSystem, ConstraintSystem},
            fatness::{libc::libc_call, library::library_call},
        },
    },
    utils::rustc::RustProgram,
};

mod libc;
mod library;

#[allow(unused)]
pub fn fatness_analysis(rust_program: &RustProgram) -> FatnessResult {
    let mut result = FatnessResult::new_empty(rust_program);
    let mut database = BooleanSystem::new(&result.model);
    for r#fn in &rust_program.functions {
        let body = &*rust_program
            .tcx
            .mir_drops_elaborated_and_const_checked(r#fn.expect_local())
            .borrow();
        let locals = {
            let idx = result.fn_locals.0.did_idx[&body.source.def_id()];
            &result.fn_locals.0.contents[idx]
        };
        let ctxt = InferCtxt {
            local_decls: body,
            locals,
            fn_locals: &result.fn_locals,
            struct_fields: &result.struct_fields,
            tcx: rust_program.tcx,
        };

        let mut analysis = FatnessAnalysis {
            ctxt,
            database: &mut database,
        };

        analysis.visit_body(body);
    }
    database.greatest_model(&mut result.model);
    result
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// [`Fatness::Arr`] ⊑ [`Fatness::Ptr`]
pub enum Fatness {
    Arr,
    Ptr,
}

impl Fatness {
    #[inline]
    pub fn is_arr(&self) -> bool {
        *self == Fatness::Arr
    }

    #[inline]
    pub fn is_ptr(&self) -> bool {
        *self == Fatness::Ptr
    }
}

impl std::fmt::Display for Fatness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Fatness::Arr => write!(f, "&[]"),
            Fatness::Ptr => write!(f, "&"),
        }
    }
}

pub type FatnessResult = TypeQualifiers<Fatness>;

impl From<Fatness> for bool {
    fn from(fatness: Fatness) -> Self {
        fatness == Fatness::Ptr
    }
}

impl From<bool> for Fatness {
    fn from(b: bool) -> Self {
        if b { Fatness::Ptr } else { Fatness::Arr }
    }
}

impl HasBottom for Fatness {
    const BOTTOM: Self = Self::Arr;
}

impl HasTop for Fatness {
    const TOP: Self = Self::Ptr;
}

impl Lattice for Fatness {
    fn join(&mut self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Arr, Self::Ptr) => {
                *self = Self::Ptr;
                return true;
            }
            _ => {}
        }
        false
    }

    fn meet(&mut self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Ptr, Self::Arr) => {
                *self = Self::Arr;
                return true;
            }
            _ => {}
        }
        true
    }
}

impl BooleanLattice for Fatness {}

pub struct FatnessAnalysis<'infer, 'tcx, D> {
    ctxt: InferCtxt<'infer, 'tcx, D>,
    database: &'infer mut BooleanSystem<Fatness>,
}

impl<'infer, 'tcx, D: HasLocalDecls<'tcx>> Visitor<'tcx> for FatnessAnalysis<'infer, 'tcx, D> {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, _location: Location) {
        let lhs = place;
        let rhs = rvalue;

        let local_decls = &*self.ctxt.local_decls;
        let locals = &*self.ctxt.locals;
        let struct_fields = &*self.ctxt.struct_fields;

        let database = &mut *self.database;

        match rhs {
            Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs)) | Rvalue::CopyForDeref(rhs) => {
                let lhs = place_vars(lhs, local_decls, locals, struct_fields);
                let rhs = place_vars(rhs, local_decls, locals, struct_fields);

                // type safety
                assert_eq!(
                    lhs.end.index() - lhs.start.index(),
                    rhs.end.index() - rhs.start.index()
                );

                let mut lhs_rhs = lhs.zip(rhs);
                if let Some((lhs, rhs)) = lhs_rhs.next() {
                    database.guard(lhs, rhs);

                    // let lhs_ownership = self.solidified.place_result(self.body, place);
                    // if matches!(lhs_ownership.first().copied(), Some(ownership) if ownership.is_owning())
                    // {
                    //     database.guard(rhs, lhs);
                    // }
                }
                for (lhs, rhs) in lhs_rhs {
                    database.guard(lhs, rhs);
                    database.guard(rhs, lhs)
                }
            }
            Rvalue::Cast(_, Operand::Copy(rhs) | Operand::Move(rhs), _) => {
                // for cast, we process the head ptr only
                let lhs = place_vars(lhs, local_decls, locals, struct_fields);
                let rhs = place_vars(rhs, local_decls, locals, struct_fields);

                let mut lhs_rhs = lhs.zip(rhs);
                if let Some((lhs, rhs)) = lhs_rhs.next() {
                    database.guard(lhs, rhs);

                    // let lhs_ownership = self.solidified.place_result(self.body, place);
                    // if matches!(lhs_ownership.first().copied(), Some(ownership) if ownership.is_owning())
                    // {
                    //     database.guard(rhs, lhs);
                    // }
                }
            }
            Rvalue::Ref(_, _, rhs) | Rvalue::RawPtr(_, rhs) => {
                let lhs = place_vars(lhs, local_decls, locals, struct_fields);
                let rhs = place_vars(rhs, local_decls, locals, struct_fields);
                for (lhs, rhs) in lhs.skip(1).zip(rhs) {
                    database.guard(lhs, rhs);
                    database.guard(rhs, lhs);
                }
            }
            _ => {
                // no need. [`place_vars`] is a pure function
                // let _ = place_vars(lhs, local_decls, locals, struct_fields);
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _location: Location) {
        let InferCtxt {
            local_decls,
            locals,
            fn_locals,
            struct_fields,
            tcx,
        } = self.ctxt;
        let database = &mut *self.database;

        if let Some(mir::MirFunctionCall {
            func,
            args,
            ref destination,
        }) = terminator.as_call(tcx)
        {
            match func {
                CallKind::FreeStanding(callee) => {
                    let callee_body = &*tcx
                        .mir_drops_elaborated_and_const_checked(callee.expect_local())
                        .borrow();
                    let mut callee_vars = fn_locals
                        .0
                        .contents_iter(&callee)
                        .take(callee_body.arg_count + 1);

                    let dest = place_vars(destination, local_decls, locals, struct_fields);
                    let ret = callee_vars.next().unwrap();

                    let mut dest_ret = dest.zip(ret);

                    if let Some((dest, ret)) = dest_ret.next() {
                        database.guard(dest, ret)
                    }
                    for (dest, ret) in dest_ret {
                        database.guard(ret, dest);
                        database.guard(dest, ret);
                    }

                    for (arg, param_vars) in args.iter().zip(callee_vars) {
                        let Some(arg) = arg.node.place() else {
                            continue;
                        };
                        let arg_vars = place_vars(&arg, local_decls, locals, struct_fields);

                        let mut param_arg = param_vars.zip(arg_vars);
                        if let Some((param, arg)) = param_arg.next() {
                            database.guard(param, arg);
                        }
                        for (param, arg) in param_arg {
                            database.guard(arg, param);
                            database.guard(param, arg);
                        }
                    }
                }
                CallKind::LibC(ident) => {
                    libc_call(
                        destination,
                        args,
                        ident,
                        local_decls,
                        locals,
                        struct_fields,
                        database,
                    );
                }
                CallKind::RustLib(callee) => {
                    library_call(
                        destination,
                        args,
                        callee,
                        local_decls,
                        locals,
                        struct_fields,
                        database,
                        tcx,
                    );
                }
                CallKind::Impl(_) => todo!(),
                CallKind::Closure => todo!(),
                CallKind::Dynamic => todo!(),
            }
        }
    }
}

fn place_vars<'tcx>(
    place: &Place<'tcx>,
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
) -> Range<Var> {
    let mut place_vars = Range {
        start: locals[place.local.index()],
        end: locals[place.local.index() + 1],
    };
    let mut base_ty = local_decls.local_decls()[place.local].ty;

    for projection_elem in place.projection {
        match projection_elem {
            ProjectionElem::Deref => {
                place_vars.start = place_vars.start + 1;
                base_ty = base_ty.builtin_deref(true).unwrap();
            }
            ProjectionElem::Field(field, ty) => {
                assert!(place_vars.is_empty());

                match base_ty.kind() {
                    TyKind::Adt(adt_def, _) => {
                        // FIXME correctness?
                        if adt_def.is_union() {
                            return place_vars;
                        }
                        let field_vars = struct_fields
                            .fields(&adt_def.did())
                            .nth(field.index())
                            .unwrap();

                        place_vars = field_vars;

                        base_ty = ty;
                    }
                    TyKind::Tuple(..) => return place_vars,
                    _ => unreachable!(),
                }
            }
            ProjectionElem::Index(_) => {
                base_ty = base_ty.builtin_index().unwrap();
            }
            ProjectionElem::ConstantIndex { .. } => unreachable!("unexpected constant index"),
            ProjectionElem::Subslice { .. } => unreachable!("unexpected subslicing"),
            ProjectionElem::OpaqueCast(_) => unreachable!("unexpected opaque cast"),
            ProjectionElem::Downcast(..) => {
                // happens when asserting nonnullness of fn ptrs
                assert!(place_vars.is_empty());
                return place_vars;
            }
            ProjectionElem::UnwrapUnsafeBinder(_) => unreachable!("unexpected UnwrapUnsafeBinder"),
            ProjectionElem::Subtype(_) => unreachable!("unexpected Subtype"),
        }
    }

    place_vars
}
