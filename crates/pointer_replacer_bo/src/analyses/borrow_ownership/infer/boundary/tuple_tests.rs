use rustc_hir::{ItemKind, OwnerNode};

use super::*;
use crate::{analyses::borrow_ownership::ssa::constraint::Gen, utils::rustc::RustProgram};

#[derive(Default)]
struct FieldEquations(Vec<(Var, Var, Var)>);

impl Database for FieldEquations {
    fn push_linear_impl(&mut self, _: Var, _: Var, _: Var) {
        unreachable!()
    }

    fn push_assume_impl(&mut self, _: Var, _: bool) {
        unreachable!()
    }

    fn push_equal_impl(&mut self, _: Var, _: Var) {
        unreachable!()
    }

    fn push_less_equal_impl(&mut self, _: Var, _: Var) {
        unreachable!()
    }

    fn push_eq_min_impl(&mut self, input: Var, field: Var, parent: Var) {
        self.0.push((input, field, parent));
    }
}

#[test]
fn tuple_field_context_skips_unrepresented_depths_without_shifting_siblings() {
    ::utils::compilation::run_compiler_on_str(
        "pub struct Holder { pointers: (*mut *mut *mut *mut i32, *mut *mut i32) }
         pub struct Generic<T> { pointers: (*mut *mut T, *mut *mut i32) }
         pub type Instantiated = Generic<(*mut i32,)>;",
        |tcx| {
            let structs: Vec<_> = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|owner| {
                    let owner = owner.as_owner()?;
                    let OwnerNode::Item(item) = owner.node() else { return None };
                    matches!(item.kind, ItemKind::Struct(..)).then_some(item.owner_id.def_id)
                })
                .collect();
            let holder = *structs
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == "Holder")
                .unwrap();
            let mut context = CrateCtxt::new(&RustProgram {
                tcx,
                functions: Vec::new(),
                structs,
            });
            while context.struct_ctxt.max_ptr_chased() < 3 {
                context.struct_ctxt.increase_precision(tcx);
            }
            let ty = tcx.type_of(holder).instantiate_identity();
            let mut generator = Gen::new();
            let mut database = FieldEquations::default();
            let global = GlobalAssumptions::new(&context, &mut generator, &mut database);
            let fields: Vec<_> = global
                .fields(&context.struct_ctxt, &holder.to_def_id())
                .next()
                .unwrap()
                .collect();
            assert_eq!(fields.len(), 6);
            for precision in 1..=3 {
                database.0.clear();
                let width = context
                    .struct_ctxt
                    .with_max_precision(precision)
                    .measure(ty, 0);
                let input = database.new_vars(&mut generator, width);
                let mut input_values = input.clone();
                GlobalAssumptionApplier {
                    global_assumptions: &global,
                    struct_ctxt: &context.struct_ctxt,
                    database: &mut database,
                    tcx,
                }
                .apply(
                    ty,
                    None,
                    &mut std::iter::empty(),
                    &mut input_values,
                    precision,
                );
                assert!(input_values.next().is_none());
                let first = precision as u32;
                let second = first.min(2);
                let expected: Vec<_> = (1..first)
                    .map(|index| {
                        (
                            input.start + index,
                            fields[index as usize],
                            input.start + (index - 1),
                        )
                    })
                    .chain((1..second).map(|index| {
                        (
                            input.start + first + index,
                            fields[4 + index as usize],
                            input.start + (first + index - 1),
                        )
                    }))
                    .collect();
                assert_eq!(database.0, expected);
            }
            let instantiated = tcx
                .hir_crate(())
                .owners
                .iter()
                .find_map(|owner| {
                    let owner = owner.as_owner()?;
                    let OwnerNode::Item(item) = owner.node() else { return None };
                    if !matches!(item.kind, ItemKind::TyAlias(..)) {
                        return None;
                    }
                    (tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == "Instantiated")
                        .then_some(item.owner_id.def_id)
                })
                .unwrap();
            let ty = tcx.type_of(instantiated).instantiate_identity();
            let width = context.struct_ctxt.with_max_precision(2).measure(ty, 0);
            assert_eq!(width, 4);
            database.0.clear();
            let mut input = database.new_vars(&mut generator, width);
            GlobalAssumptionApplier {
                global_assumptions: &global,
                struct_ctxt: &context.struct_ctxt,
                database: &mut database,
                tcx,
            }
            .apply(ty, None, &mut std::iter::empty(), &mut input, 2);
            assert!(input.next().is_none());
            assert!(
                database.0.is_empty(),
                "opaque generic context cannot bind a sibling's globals"
            );
        },
    )
    .unwrap();
}
