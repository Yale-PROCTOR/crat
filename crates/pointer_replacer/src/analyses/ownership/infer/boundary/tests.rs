use rustc_index::bit_set::MixedBitSet;

use crate::analyses::ownership::{
    AnalysisKind, CrateCtxt,
    ptr::Measurable,
    ssa::{
        constraint::{Database, Gen, GlobalAssumptions, SolverDatabase, Z3Database},
        consume::Consume,
    },
    whole_program::{OwnershipSolver, WholeProgramAnalysis},
};

#[test]
fn generic_calls_match_pointer_bearing_arguments_and_returns() {
    for source in [
        r#"
pub struct Node { pub data: *mut i32 }
pub fn process<T>(value: &mut T) {}
pub unsafe fn caller(node: &mut Node) { process(node); *node.data = 1; }
"#,
        r#"
pub struct Node { pub data: *mut i32 }
pub fn identity<T>(value: T) -> T { value }
pub fn caller(node: Node) -> Node { identity(node) }
"#,
        r#"
pub struct Node { pub data: *mut i32 }
pub fn identity<T>(value: *mut T) -> *mut T { value }
pub fn caller(node: *mut Node) -> *mut Node { identity(node) }
"#,
        r#"
pub struct Node { pub data: *mut i32 }
pub fn identity<T>(value: T) -> T { value }
pub fn caller(node: &mut Node) -> &mut Node { identity(node) }
"#,
        r#"
pub struct Node { pub data: *mut i32 }
pub fn fill<T>(destination: &mut T, value: T) { *destination = value; }
pub fn caller(destination: &mut Node, value: Node) { fill(destination, value); }
"#,
        r#"
pub struct First { pub data: *mut i32 }
pub struct Second { pub data: *mut *mut i32, pub other: *mut i32 }
pub fn process<T>(value: &mut T) {}
pub fn forward<T>(value: &mut T, again: bool) {
    if again { forward(value, false); } else { process(value); }
}

pub fn caller(first: &mut First, second: &mut Second) {
    forward(first, true);
    forward(second, true);
}
"#,
    ] {
        utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::rewriter::collect_input(tcx);
            for mark_output in [false, true] {
                let output = program
                    .functions
                    .iter()
                    .map(|&function| {
                        let body = tcx
                            .mir_drops_elaborated_and_const_checked(function)
                            .borrow();
                        let mut outputs = MixedBitSet::new_empty(body.local_decls.len());
                        if mark_output
                            && matches!(
                                tcx.item_name(function.to_def_id()).as_str(),
                                "process" | "fill" | "forward"
                            )
                        {
                            for arg in body.args_iter() {
                                if body.local_decls[arg].ty.builtin_deref(true).is_some() {
                                    outputs.insert(arg);
                                }
                            }
                        }
                        (function, outputs)
                    })
                    .collect();
                let ownership = WholeProgramAnalysis::analyze(CrateCtxt::new(&program), &output)
                    .expect("generic-call ownership inference");
                for &function in &program.functions {
                    assert!(
                        ownership.precision(&function.to_def_id()) > 0,
                        "{} lost ownership precision with mark_output={mark_output}: {source}",
                        tcx.def_path_str(function)
                    );
                }
            }
        })
        .unwrap();
    }
}

#[test]
fn generic_call_slots_preserve_the_prefix_and_constrain_hidden_pointers() {
    utils::compilation::run_compiler_on_str(
        r#"
pub struct Node { pub data: *mut i32, pub next: *mut Node }
pub fn value<T>(input: T) {}
pub fn pointer<T>(input: *mut T) {}
pub fn nested<T>(input: *mut *mut T) {}
pub fn reference<T>(input: &mut T) {}
pub fn array<T>(input: [T; 2]) {}
"#,
        |tcx| {
            let program = crate::rewriter::collect_input(tcx);
            let mut context = CrateCtxt::new(&program);
            context.struct_ctxt.increase_precision(tcx);
            context.struct_ctxt.increase_precision(tcx);
            let node = tcx.type_of(program.structs[0]).instantiate_identity();
            let substitutions = tcx.mk_args(&[node.into()]);

            for &function in &program.functions {
                let ty = tcx
                    .fn_sig(function)
                    .instantiate_identity()
                    .skip_binder()
                    .inputs()[0];
                let instantiated_ty = tcx
                    .fn_sig(function)
                    .instantiate(tcx, substitutions)
                    .skip_binder()
                    .inputs()[0];
                let mut database = Z3Database::new();
                let mut generator = Gen::new();
                let params = database.new_vars(&mut generator, context.struct_ctxt.measure(ty, 0));
                let count = context.struct_ctxt.measure(instantiated_ty, 0);
                let args = Consume {
                    r#use: database.new_vars(&mut generator, count),
                    def: database.new_vars(&mut generator, count),
                };
                let mut matched = Vec::new();
                super::match_call(
                    ty,
                    instantiated_ty,
                    params.clone(),
                    args.clone().transpose(),
                    &context.struct_ctxt,
                    &mut database,
                    |param, arg, database| {
                        matched.push((param, arg.r#use, arg.def));
                        database.push_equal_impl(param, arg.def);
                        database.push_equal_impl(arg.r#use, arg.def);
                    },
                );
                let expected = params
                    .clone()
                    .zip(args.r#use.clone().zip(args.def.clone()))
                    .map(|(param, (r#use, def))| (param, r#use, def))
                    .collect::<Vec<_>>();
                assert_eq!(matched, expected);
                assert_eq!(database.solver.check(), z3::SatResult::Sat);

                let param_count = params.clone().count();
                for var in args.r#use.clone().take(param_count) {
                    database.solver.push();
                    database.push_assume_impl(var, true);
                    assert_eq!(database.solver.check(), z3::SatResult::Sat);
                    database.solver.pop(1);
                }
                let hidden = args
                    .r#use
                    .skip(param_count)
                    .chain(args.def.skip(param_count))
                    .collect::<Vec<_>>();
                assert!(!hidden.is_empty());
                for var in hidden {
                    database.solver.push();
                    database.push_assume_impl(var, true);
                    assert_eq!(database.solver.check(), z3::SatResult::Unsat);
                    database.solver.pop(1);
                }
            }
        },
    )
    .unwrap();
}

#[test]
fn instantiated_generic_fields_keep_their_declared_ownership_slots() {
    use rustc_abi::FieldIdx;
    use rustc_middle::mir::ProjectionElem;

    use crate::analyses::ownership::infer::InferCtxt;

    utils::compilation::run_compiler_on_str(
        r#"
pub struct Node { pub pointer: *mut i32, pub next: *mut Node }
pub struct Holder<'a, T> { pub generic: &'a mut T, pub deep: *mut *mut i32 }
pub unsafe fn inspect(value: Holder<'_, Node>) -> *mut i32 {
    let generic = value.generic;
    let pointer = generic.pointer;
    let deep = value.deep;
    if pointer.is_null() { *deep } else { pointer }
}
"#,
        |tcx| {
            let program = crate::rewriter::collect_input(tcx);
            let function = program.functions[0];
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let holder = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
            let rustc_middle::ty::TyKind::Adt(adt, args) = holder.kind() else { unreachable!() };
            let fields = &adt.non_enum_variant().fields;
            let generic_ty = fields[FieldIdx::from_usize(0)].ty(tcx, args);
            let deep_ty = fields[FieldIdx::from_usize(1)].ty(tcx, args);
            let node_pointer = body.return_ty();

            for precision in [2, 3] {
                let mut context = CrateCtxt::new(&program);
                while context.struct_ctxt.max_ptr_chased() < precision {
                    context.struct_ctxt.increase_precision(tcx);
                }
                let mut database = SolverDatabase::new(OwnershipSolver::Z3);
                let mut generator = Gen::new();
                let globals = GlobalAssumptions::new(&context, &mut generator, &mut database);
                let inter_context = Default::default();
                let mut inference = InferCtxt::<WholeProgramAnalysis> {
                    tcx,
                    inter_ctxt: &inter_context,
                    database: &mut database,
                    var_gen: &mut generator,
                    struct_ctxt: context.struct_ctxt.with_max_precision(precision),
                    fn_body_sig: Default::default(),
                    deref_copy: None,
                    call_args: Vec::new(),
                    global_assumptions: &globals,
                };
                let vars = inference.new_vars(holder);
                assert_eq!(vars.clone().count(), 3);
                let consume = Consume {
                    r#use: vars.clone(),
                    def: inference.new_vars(holder),
                };
                let generic_field = ProjectionElem::Field(FieldIdx::from_usize(0), generic_ty);
                let generic = InferCtxt::project_deeper(
                    consume.clone(),
                    holder,
                    &[generic_field],
                    &mut inference,
                )
                .unwrap();
                assert_eq!(generic.r#use, vars.start..vars.start + 1u32);
                let deep = InferCtxt::project_deeper(
                    consume.clone(),
                    holder,
                    &[ProjectionElem::Field(FieldIdx::from_usize(1), deep_ty)],
                    &mut inference,
                )
                .unwrap();
                assert_eq!(deep.r#use, vars.start + 1u32..vars.end);
                assert!(
                    InferCtxt::project_deeper(
                        consume,
                        holder,
                        &[
                            generic_field,
                            ProjectionElem::Deref,
                            ProjectionElem::Field(FieldIdx::from_usize(0), node_pointer)
                        ],
                        &mut inference,
                    )
                    .is_none()
                );
                super::GlobalAssumptionApplier {
                    global_assumptions: &globals,
                    struct_ctxt: &context.struct_ctxt,
                    database: inference.database,
                    tcx,
                }
                .apply(
                    holder,
                    None,
                    &mut std::iter::empty(),
                    &mut vars.clone(),
                    precision,
                );
                database.open_scope();
                database.push_assume_impl(vars.start, false);
                database.push_assume_impl(vars.start + 1u32, true);
                database.push_assume_impl(vars.start + 2u32, true);
                assert_eq!(database.check_scope(), Some(true));
                database.close_scope(false);
                database.push_assume_impl(vars.start + 1u32, false);
                database.push_assume_impl(vars.start + 2u32, true);
                assert_eq!(database.check_scope(), Some(false));
            }

            let output = program
                .functions
                .iter()
                .map(|&function| {
                    let body = tcx
                        .mir_drops_elaborated_and_const_checked(function)
                        .borrow();
                    (function, MixedBitSet::new_empty(body.local_decls.len()))
                })
                .collect();
            let ownership = WholeProgramAnalysis::analyze(CrateCtxt::new(&program), &output)
                .expect("instantiated generic-field ownership inference");
            assert!(ownership.precision(&function.to_def_id()) > 0);
            ownership.solidify(&program);
        },
    )
    .unwrap();
}
