//! era-5c 157 (relay 196, R864-1 class 2): which evidence clears two `as_mut_ptr()` results of one
//! array (libzahl `zmul`'s `zadd(b_low.as_mut_ptr(), b_low.as_mut_ptr(), …)` in the input). A trace:
//! the producer's audit rows in the census world, and the two sets `classify_pair` ORs — the
//! depth-0 origins and the Andersen points-to — for each call's first two arguments.

use std::collections::BTreeSet;

use points_to::andersen::{self, Var};
use rustc_middle::mir::TerminatorKind;

use crate::analyses::borrow_ownership::{
    a5_producer::audit_a5_site_branches, crate_slots::CrateSlots, origins::compute_origins,
};

/// The input's shape (C2Rust form): the call passes one array twice; the control passes two.
const ZADD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] #[derive(Copy, Clone)] pub struct Z { pub used: u64, pub sign: i32 }
pub unsafe fn zadd(a: *mut Z, b: *mut Z, c: *mut Z) {
    (*a).used = (*b).used + (*c).used;
    (*a).sign = (*b).sign;
}
pub unsafe fn zmul(c: *mut Z) {
    let mut x: [Z; 1] = [Z { used: 0, sign: 0 }; 1];
    let mut y: [Z; 1] = [Z { used: 0, sign: 0 }; 1];
    zadd(x.as_mut_ptr(), x.as_mut_ptr(), c);
    zadd(x.as_mut_ptr(), y.as_mut_ptr(), c);
}
"#;

#[test]
#[ignore = "era-5c 157: a trace; run with --ignored --nocapture"]
fn e5c_class2_trace_two_borrows_of_one_array() {
    ::utils::compilation::run_compiler_on_str(ZADD, |tcx| {
        let program = super::collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        for row in audit_a5_site_branches(&program, &slots, origins.native_flows()) {
            println!(
                "AUDIT {} bb{} -> {} #{}/#{} {} | {} classifier={:?} family={}",
                row.caller_path,
                row.block,
                row.target_path,
                row.left_parameter,
                row.right_parameter,
                row.left_operand,
                row.right_operand,
                row.classifier,
                row.family
            );
        }
        // The producer's Andersen, built as `audit_a5_site_branches` builds it.
        let arena = typed_arena::Arena::new();
        let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
        let config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: program
                .functions
                .iter()
                .filter(|did| tcx.visibility(did.to_def_id()).is_public())
                .map(|did| tcx.item_name(did.to_def_id()).to_string())
                .collect(),
        };
        let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
        let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
        let zmul = *program
            .functions
            .iter()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == "zmul")
            .expect("zmul");
        let body = tcx.mir_drops_elaborated_and_const_checked(zmul).borrow();
        let flow = &origins.native_flows()[&zmul].body;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call { args, .. } = &data.terminator().kind else { continue };
            if args.len() != 3 {
                continue;
            }
            let side = |index: usize| {
                let local = args[index].node.place().map(|place| place.local);
                let origins = local.and_then(|l| flow.depth0_origin_indices(&body, l, false));
                let points = local.and_then(|l| {
                    pre.vars.get(&Var::Local(zmul, l)).map(|&location| {
                        solutions[location]
                            .iter()
                            .map(|target| target.index())
                            .collect::<BTreeSet<_>>()
                    })
                });
                (local, origins, points)
            };
            println!(
                "SPLIT bb{} left={:?} right={:?}",
                block.as_u32(),
                side(0),
                side(1)
            );
        }
    })
    .expect("fixture compiles");
}
