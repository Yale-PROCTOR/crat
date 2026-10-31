//! Relay main/388 review-set (R1394-1): `demote`'s chain filter reads `safe_holder_set`, the set of
//! `safe_holders`' slots, instead of scanning the Vec per visited slot. The membership is the scan's
//! for every slot the review knows -- locals and fields, safe and not.

use rustc_hir::{ItemKind, OwnerNode};

use super::{CURRENT, begin};
use crate::{
    analyses::borrow_ownership::{
        crate_slots::CrateSlots, export, origin_flow::analyze_program_origin_flow, solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

const CODE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
pub struct Pair { pub a: *mut u8, pub b: *const u8 }
pub unsafe fn f(pair: *mut Pair, p: *const u8) -> u8 {
    let q: *const u8 = p;
    let r = malloc(4);
    (*pair).a = r;
    (*pair).b = q;
    free(r);
    *q
}
"#;

#[test]
fn r1394_the_safe_holder_set_answers_as_the_vec_scan_for_every_slot() {
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let flows = analyze_program_origin_flow(&program);
        // Locals are Ref, fields are not: the review knows safe and unsafe slots of both owners.
        let ((), _captured) = export::with_bo_export(|| {
            let scope = begin(&program, &slots, &flows, |slot| {
                matches!(slot, SlotRef::Local(..))
            });
            CURRENT.with(|current| {
                let current = current.borrow();
                let context = current.as_ref().expect("the retirement scope");
                let (mut safe, mut unsafe_) = (0, 0);
                for slot in context.keys.keys() {
                    let scan = context.safe_holders.iter().any(|(safe, _, _)| safe == slot);
                    assert_eq!(context.safe_holder_set.contains(slot), scan, "{slot:?}");
                    if scan {
                        safe += 1;
                    } else {
                        unsafe_ += 1;
                    }
                }
                assert_eq!(context.safe_holder_set.len(), context.safe_holders.len());
                assert!(
                    safe >= 2 && unsafe_ >= 2,
                    "both answers occur: {safe} / {unsafe_}"
                );
                assert!(
                    context
                        .keys
                        .keys()
                        .any(|slot| matches!(slot, SlotRef::Field(_))),
                    "the fixture has field slots"
                );
            });
            let _ = scope.finish();
        });
    })
    .unwrap();
}
