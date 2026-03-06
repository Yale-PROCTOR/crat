use rustc_hash::FxHashMap;
use rustc_middle::mir::Body;

use super::InterCtxt;
use crate::analyses::{
    output_params::OutputParams,
    ownership::{
        CrateCtxt, Ownership, Param, Precision,
        call_graph::FnSig,
        infer::FnSummary,
        ssa::{
            constraint::{Database, Gen, Z3Database, initialize_local},
            consume::{Consume, initial_definitions},
            dom::compute_dominance_frontier,
            state::SSAState,
        },
    },
};

pub(super) fn initial_inter_ctxt(
    crate_ctxt: &CrateCtxt,
    output_params: &OutputParams,
    var_gen: &mut Gen,
    database: &mut Z3Database,
) -> InterCtxt {
    const INIT_PRECISION: Precision = 1;

    let mut fn_sigs = FxHashMap::default();
    fn_sigs.reserve(crate_ctxt.fns().len());
    for &did in crate_ctxt.fn_ctxt.fns() {
        let output_params = &output_params[&did.expect_local()];
        let body = &*crate_ctxt
            .tcx
            .mir_drops_elaborated_and_const_checked(did.expect_local())
            .borrow();
        let fn_sig = {
            let mut local_decls = body.local_decls.iter_enumerated();
            let (_, return_local_decl) = local_decls.next().unwrap();
            let ret = initialize_local(
                return_local_decl,
                var_gen,
                database,
                crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
            )
            .map(|sigs| Param::Normal(sigs));

            let args = local_decls
                .take(body.arg_count)
                .map(|(local, local_decl)| {
                    if output_params.contains(local) {
                        let r#use = initialize_local(
                            local_decl,
                            var_gen,
                            database,
                            crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
                        );
                        let def = initialize_local(
                            local_decl,
                            var_gen,
                            database,
                            crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
                        );
                        r#use.zip(def).map(|(r#use, def)| {
                            database
                                .push_assume::<crate::analyses::ownership::ssa::constraint::Debug>(
                                    (),
                                    r#use.start,
                                    true,
                                );
                            database
                                .push_assume::<crate::analyses::ownership::ssa::constraint::Debug>(
                                    (),
                                    def.start,
                                    true,
                                );
                            Param::Output(Consume { r#use, def })
                        })
                    } else {
                        initialize_local(
                            local_decl,
                            var_gen,
                            database,
                            crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
                        )
                        .map(|sigs| Param::Normal(sigs))
                    }
                })
                .collect();

            FnSig { ret, args }
        };
        fn_sigs.insert(did, fn_sig);
    }

    fn_sigs
}

#[inline]
pub(super) fn initial_ssa_state<'tcx>(crate_ctxt: &CrateCtxt<'tcx>, body: &Body<'tcx>) -> SSAState {
    let dominance_frontier = compute_dominance_frontier(body);
    let definitions = initial_definitions(body, crate_ctxt);
    SSAState::new(body, &dominance_frontier, definitions)
}

pub(super) fn refine_state(_body: &Body, fn_summary: FnSummary, _model: &[Ownership]) -> SSAState {
    // let ownership_transferred_locations =
    //     compute_ownership_transferred_locations(body, &fn_summary, model);

    let FnSummary { mut ssa_state, .. } = fn_summary;

    ssa_state.name_state.reset();
    ssa_state.join_points.reset();
    ssa_state.consume_chain.reset();
    ssa_state
}

// pub fn compute_ownership_transferred_locations(
//     body: &Body,
//     fn_summary: &FnSummary,
//     model: &[Ownership],
// ) -> SsoHashSet<Location> {
//     fn ownership_transferred(consume: Consume<&[Ownership]>) -> bool {
//         for (&r#use, &def) in consume.r#use.iter().zip(consume.def.iter()) {
//             if r#use == def {
//                 continue;
//             }
//             if r#use == Ownership::Owning || def == Ownership::Owning {
//                 return true;
//             }
//         }
//         false
//     }

//     let mut ownership_transferred_locations: SsoHashSet<Location> = SsoHashSet::default();
//     let fn_result = (fn_summary, model);

//     for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
//         let BasicBlockData { statements, .. } = bb_data;
//         let mut index = 0;
//         let mut deref_copy: Option<Location> = None;
//         for statement in statements {
//             let location = Location {
//                 block: bb,
//                 statement_index: index,
//             };
//             if matches!(&statement.kind, StatementKind::Assign(box (_, rvalue)) if matches!(rvalue, Rvalue::CopyForDeref(_)))
//             {
//                 let base_location = deref_copy.take().or(Some(location));
//                 deref_copy = base_location;
//                 index += 1;
//                 continue;
//             }
//             if let Some(base_location) = deref_copy.take() {
//                 let StatementKind::Assign(box (_, _)) = &statement.kind else { unreachable!() };

//                 let location_result = fn_result
//                     .location_results(base_location)
//                     .chain(fn_result.location_results(location));
//                 for (_, ownership_status) in location_result {
//                     if ownership_transferred(ownership_status) {
//                         ownership_transferred_locations.insert(location);
//                         ownership_transferred_locations.insert(base_location);
//                     }
//                 }

//                 index += 1;
//                 continue;
//             }

//             let location_result = fn_result.location_results(location);
//             for (_, ownership_status) in location_result {
//                 if ownership_transferred(ownership_status) {
//                     ownership_transferred_locations.insert(location);
//                 }
//             }

//             index += 1;
//         }
//     }

//     ownership_transferred_locations
// }
