//! Original source-library destruction, not generated rewriter drops. These
//! fixtures are compiled for analysis and never executed. A passing rejection
//! may already be covered by a MIR Drop; it is not automatically new RED evidence.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{Location, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};

use super::tests::accepts;
use crate::{
    analyses::{
        borrow_ownership::{
            export::PlaceKey,
            source_events::{self, SourceEvents, SourcePhase, SourceRole},
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

#[derive(Debug)]
struct OriginalDrop {
    location: Location,
    place: PlaceKey,
    payload_type: String,
    cleanup: bool,
}

struct Inspection {
    call: Location,
    original_drops: Vec<OriginalDrop>,
    events: SourceEvents,
}

fn is_box(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    let TyKind::Adt(definition, _) = ty.kind() else { return false };
    tcx.crate_name(definition.did().krate).as_str() == "alloc"
        && matches!(
            tcx.def_path_str(definition.did()).as_str(),
            "alloc::boxed::Box" | "std::boxed::Box"
        )
}

fn inspect(code: &str, expected_path: &str, in_place: bool) -> Inspection {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let callers: Vec<_> = functions.iter().copied().filter(|function|
            tcx.item_name(function.to_def_id()).as_str() == "caller").collect();
        assert_eq!(callers.len(), 1);
        let body = tcx.mir_drops_elaborated_and_const_checked(callers[0]).borrow();
        let mut calls = Vec::new();
        let mut constructors = 0;
        let mut original_drops = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let location = Location { block, statement_index: data.statements.len() };
            if let TerminatorKind::Drop { place, .. } = data.terminator().kind {
                original_drops.push(OriginalDrop { location, place: PlaceKey::from_place(place),
                    payload_type: place.ty(&*body, tcx).ty.to_string(), cleanup: data.is_cleanup });
            }
            let Some(call) = data.terminator().as_call(tcx) else { continue };
            let CallKind::RustLib(did) = call.func else { continue };
            let path = tcx.def_path_str(did);
            eprintln!("[D-LIBRARY-IDENTITY] crate={} item={} path={path} mem_drop={}",
                tcx.crate_name(did.krate), tcx.item_name(did),
                tcx.is_diagnostic_item(rustc_span::Symbol::intern("mem_drop"), did));
            if tcx.crate_name(did.krate).as_str() == "alloc" && path.contains("::boxed::")
                && tcx.item_name(did).as_str() == "from_raw"
            { constructors += 1; }
            // The pinned compiler pretty-prints these core definitions through
            // their std reexports; the actual defining crate remains core.
            let defining_path = path.strip_prefix("std::").map(|suffix| format!("core::{suffix}")).unwrap_or_else(|| path.clone());
            if defining_path != expected_path { continue; }
            // Full compiler-resolved crate/DefId path identifies the known
            // standard-library item; an unrelated local `drop` cannot match.
            assert_eq!(tcx.crate_name(did.krate).as_str(), "core");
            assert!(!did.is_local());
            assert_eq!(call.args.len(), 1);
            let argument = call.args[0].node.ty(&*body, tcx);
            let payload = if in_place {
                let TyKind::RawPtr(pointee, _) = argument.kind() else {
                    panic!("drop_in_place must receive the original pointer-to-Box operand");
                };
                *pointee
            } else { argument };
            assert!(is_box(tcx, payload), "the actual destruction/forget payload must be alloc::boxed::Box: {payload}");
            eprintln!("[D-LIBRARY-DROP] callee={did:?} path={path} location={location:?} payload={payload}");
            calls.push(location);
        }
        assert_eq!(constructors, 1, "one actual alloc Box::from_raw source call");
        assert_eq!(calls.len(), 1, "one original known-library call: {expected_path}");
        let events = source_events::collect(&RustProgram { tcx, functions, structs });
        for drop in &original_drops {
            assert!(events.retirements.keys().any(|key| key.function == "caller"
                && key.role == SourceRole::Drop && key.block == drop.location.block.as_u32()
                && key.statement == drop.location.statement_index),
                "an existing input-MIR Drop must remain inventoried: {drop:?}");
            eprintln!("[D-LIBRARY-DROP] original_drop={:?} place={:?} payload={} cleanup={}",
                drop.location, drop.place, drop.payload_type, drop.cleanup);
        }
        eprintln!("[D-LIBRARY-DROP] path={expected_path} original_drop_count={} inventory={events:?}", original_drops.len());
        Inspection { call: calls[0], original_drops, events }
    }).unwrap_or_else(|error| error.raise())
}

#[test]
fn e5_p_d_source_mem_drop_box_retires_the_protected_input() {
    const CODE: &str = r#"
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    let owner = Box::from_raw(p as *mut u8);
    core::mem::drop(owner);
    value
}
"#;
    let evidence = inspect(CODE, "core::mem::drop", false);
    assert!(
        !accepts(CODE, &[("caller", 1, 0)]),
        "source mem::drop(Box) needs retirement coverage or typed decline; call={:?}, existing_drops={:?}, inventory={:?}",
        evidence.call,
        evidence.original_drops,
        evidence.events
    );
}

#[test]
fn e5_p_d_source_drop_in_place_box_retires_the_protected_input() {
    const CODE: &str = r#"
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    let mut owner = core::mem::ManuallyDrop::new(Box::from_raw(p as *mut u8));
    core::ptr::drop_in_place(&mut *owner);
    value
}
"#;
    // ManuallyDrop prevents a second automatic Box drop; the intended source
    // shape has one destruction and never reads the destroyed owner afterward.
    let evidence = inspect(CODE, "core::ptr::drop_in_place", true);
    assert!(
        !accepts(CODE, &[("caller", 1, 0)]),
        "source drop_in_place(Box) needs retirement coverage or typed decline; call={:?}, existing_drops={:?}, inventory={:?}",
        evidence.call,
        evidence.original_drops,
        evidence.events
    );
}

#[test]
fn e5_p_d_source_forget_box_does_not_invent_retirement() {
    const CODE: &str = r#"
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    let owner = Box::from_raw(p as *mut u8);
    core::mem::forget(owner);
    value
}
"#;
    let evidence = inspect(CODE, "core::mem::forget", false);
    assert!(
        !evidence
            .events
            .retirements
            .keys()
            .any(|key| key.function == "caller"
                && key.block == evidence.call.block.as_u32()
                && key.statement == evidence.call.statement_index
                && key.phase == SourcePhase::Call
                && matches!(
                    key.role,
                    SourceRole::Free | SourceRole::ReallocOld | SourceRole::Drop
                )),
        "mem::forget itself has no source retirement"
    );
    assert!(
        accepts(CODE, &[("caller", 1, 0)]),
        "forget leaks the owner and must preserve the source-no-retirement control; existing_drops={:?}, inventory={:?}",
        evidence.original_drops,
        evidence.events
    );
}

#[test]
fn e5_p_d_dropping_a_raw_pointer_value_does_not_retire_its_pointee() {
    const CODE: &str = r#"
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    core::mem::drop(p);
    value
}
"#;
    assert!(
        accepts(CODE, &[("caller", 1, 0)]),
        "the compiler proves this payload needs no drop; its pointer value is not an owning object"
    );
}
