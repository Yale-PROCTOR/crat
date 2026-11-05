//! Local-route controls for destructor effects and constant-null arguments.

#[test]
fn e5_p_raw_local_box_drop_rejects_overlapping_caller_entry() {
    const CODE: &str = r#"
unsafe fn destroy(raw: *mut u8) {
    let _owner = Box::from_raw(raw);
}
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    destroy(p as *mut u8);
    value
}
"#;
    assert!(
        !super::tests::accepts(CODE, &[("caller", 1, 0)]),
        "a source Box drop in a Raw wrapper must not hide retirement from the caller's protected entry"
    );
}

#[test]
fn e5_p_local_free_of_literal_null_preserves_unrelated_caller_entry() {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::mir::Operand;

    use crate::analyses::{
        borrow_ownership::source_events,
        mir::{CallKind, TerminatorExt},
    };

    const CODE: &str = r#"
unsafe extern "C" { fn free(raw: *mut u8); }
unsafe fn release(raw: *mut u8) { free(raw); }
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    release(const { 0 as *mut u8 });
    value
}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let caller = tcx
            .hir_crate(())
            .owners
            .iter()
            .find_map(|owner| {
                let OwnerNode::Item(item) = owner.as_owner()?.node() else { return None };
                (matches!(item.kind, ItemKind::Fn { .. })
                    && tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == "caller")
                    .then_some(item.owner_id.def_id)
            })
            .expect("original caller body");
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let calls: Vec<_> = body
            .basic_blocks
            .iter()
            .filter_map(|data| data.terminator().as_call(tcx))
            .filter(|call| {
                matches!(call.func, CallKind::FreeStanding(callee)
                    if tcx.item_name(callee.to_def_id()).as_str() == "release")
            })
            .collect();
        assert_eq!(calls.len(), 1, "exact source wrapper call");
        assert_eq!(calls[0].args.len(), 1);
        let argument = &calls[0].args[0].node;
        assert!(matches!(argument, Operand::Constant(_)));
        assert!(
            argument.place().is_none(),
            "the test must exercise a constant route argument"
        );
        assert!(source_events::operand_is_null(argument, &[], tcx));
    })
    .unwrap_or_else(|error| error.raise());
    assert!(
        super::tests::accepts(CODE, &[("caller", 1, 0)]),
        "free(NULL) through a local wrapper retires no caller object"
    );
}
