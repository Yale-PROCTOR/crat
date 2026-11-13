use rustc_middle::mir::{Local, Location, TerminatorKind, UnwindAction, VarDebugInfoContents};

use super::{
    tests_return_origin::{named_function, with_program},
    unwind::UnwindLiveness,
};
use crate::analyses::borrow_ownership::{
    copy_relax_tests::kinds,
    source_events::{self, SourceRole},
};

const LOCAL_BORROWS: &str = r#"
extern "Rust" { fn may_unwind(); }
pub unsafe fn shared() -> i32 {
    let value = 1;
    let p = &raw const value;
    let q = p.offset(0);
    may_unwind();
    *q
}
pub unsafe fn mutable() -> i32 {
    let mut value = 1;
    let p = &raw mut value;
    let q = p.offset(0);
    may_unwind();
    *q = 2;
    *q
}
pub unsafe fn aggregate() -> i32 {
    let value = 1;
    let p = &raw const value;
    let holder = (p,);
    may_unwind();
    *holder.0
}
#[derive(Clone, Copy)]
pub struct Point { x: i32, y: i32 }
pub unsafe fn pointee_data() -> i32 {
    let value = Point { x: 1, y: 2 };
    let p = &raw const value;
    let q = p.offset(0);
    may_unwind();
    let copied = *q;
    copied.x + copied.y
}
"#;

fn local(body: &rustc_middle::mir::Body<'_>, name: &str) -> Local {
    body.var_debug_info
        .iter()
        .find_map(|info| {
            if info.name.as_str() != name {
                return None;
            }
            let VarDebugInfoContents::Place(place) = info.value else { return None };
            place.as_local()
        })
        .expect("named fixture local")
}

#[test]
fn local_borrows_remain_references_across_possible_unwind() {
    let kinds = kinds(LOCAL_BORROWS);
    for name in [
        "shared::p",
        "shared::q",
        "mutable::p",
        "mutable::q",
        "aggregate::p",
        "pointee_data::p",
        "pointee_data::q",
    ] {
        assert_eq!(
            kinds.get(name).map(String::as_str),
            Some("ref"),
            "{name}: {kinds:?}"
        );
    }
    with_program(LOCAL_BORROWS, |program| {
        let inventory = source_events::collect(program);
        assert!(
            inventory
                .retirements
                .keys()
                .any(|event| event.role == SourceRole::UnwindStorage),
            "possible unwinding must remain inventoried"
        );
    });
}

const ESCAPES: &str = r#"
extern "Rust" { fn may_unwind(); fn keep(p: *const i32); fn keep_cell(p: *const *const i32); }
static mut SAVED: *const i32 = core::ptr::null();
static mut ADDRESS: usize = 0;
#[cfg(target_pointer_width = "64")] type PointerFloat = f64;
#[cfg(target_pointer_width = "32")] type PointerFloat = f32;
pub struct Holder { p: *const i32 }
pub struct Guard { p: *const i32 }
impl Drop for Guard { fn drop(&mut self) { unsafe { core::ptr::read_volatile(self.p); } } }
pub unsafe fn direct_call() -> i32 {
    let value = 1; let p = &raw const value;
    keep(p); may_unwind(); *p
}
pub unsafe fn indirect_call(callback: unsafe fn(*const i32)) -> i32 {
    let value = 1; let p = &raw const value;
    callback(p); may_unwind(); *p
}
pub unsafe fn static_store() -> i32 {
    let value = 1; let p = &raw const value;
    let q = p.offset(0); SAVED = q; may_unwind(); *p
}
pub unsafe fn pointee_store(out: *mut *const i32) -> i32 {
    let value = 1; let p = &raw const value;
    *out = p; may_unwind(); *p
}
pub unsafe fn aggregate_store(out: *mut Holder) -> i32 {
    let value = 1; let p = &raw const value;
    let holder = Holder { p }; *out = holder; may_unwind(); *p
}
pub unsafe fn address_of_carrier() -> i32 {
    let value = 1; let p = &raw const value;
    let pp = &raw const p; keep_cell(pp); may_unwind(); *p
}
pub unsafe fn integer_address() -> i32 {
    let value = 1; let p = &raw const value;
    ADDRESS = p as usize; may_unwind(); *p
}
pub unsafe fn address_method() -> i32 {
    let value = 1; let p = &raw const value;
    ADDRESS = p.addr(); may_unwind(); *p
}
pub unsafe fn reinterpreted_carrier() -> i32 {
    let value = 1; let p = &raw const value;
    let bits = (&raw const p).cast::<usize>();
    ADDRESS = *bits; may_unwind(); *p
}
pub unsafe fn floating_carrier() -> i32 {
    let value = 1; let p = &raw const value;
    let bits: PointerFloat = core::mem::transmute(p);
    let view = (&raw const bits).cast::<usize>();
    ADDRESS = *view; may_unwind(); *p
}
pub unsafe fn destructor() -> i32 {
    let value = 1; let p = &raw const value;
    let guard = Guard { p }; may_unwind(); *p
}
pub unsafe fn returned() -> *const i32 {
    let value = 1; let p = &raw const value;
    may_unwind(); p
}
"#;

#[test]
fn escaping_and_destructor_carriers_keep_unwind_obligations() {
    with_program(ESCAPES, |program| {
        for name in [
            "direct_call",
            "indirect_call",
            "static_store",
            "pointee_store",
            "aggregate_store",
            "address_of_carrier",
            "integer_address",
            "address_method",
            "reinterpreted_carrier",
            "floating_carrier",
            "destructor",
            "returned",
        ] {
            let function = named_function(program, name);
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let facts = UnwindLiveness::analyze(program.tcx, &body);
            let exits = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    (data.terminator().unwind() == Some(&UnwindAction::Continue)
                        || matches!(data.terminator().kind, TerminatorKind::UnwindResume))
                    .then_some(Location {
                        block,
                        statement_index: data.statements.len(),
                    })
                })
                .collect::<Vec<_>>();
            assert!(
                !exits.is_empty(),
                "{name} must have a real frame-exit unwind"
            );
            for exit in exits {
                assert!(!facts.ends_at(local(&body, "p"), exit), "{name}: {exit:?}");
            }
        }
    });
}

#[test]
fn escaped_native_loans_still_conflict_with_unwind_storage_retirement() {
    for function in [
        "direct_call",
        "indirect_call",
        "static_store",
        "pointee_store",
        "aggregate_store",
        "address_of_carrier",
        "integer_address",
        "address_method",
        "reinterpreted_carrier",
        "floating_carrier",
        "returned",
    ] {
        let review = super::tests_loans::review_local(ESCAPES, function, "p");
        assert!(
            review.conflicts.iter().any(|conflict| {
                conflict.source.role == SourceRole::UnwindStorage
                    && conflict.loan.is_some()
                    && conflict.target_key.starts_with(&format!("{function}::"))
            }),
            "{function}: escaped native loan must retain its unwind conflict: {review:?}"
        );
    }
}

#[test]
fn destructor_retirement_still_checks_the_native_loan() {
    let review = super::tests_loans::review_local(ESCAPES, "destructor", "p");
    assert!(
        review.conflicts.iter().any(|conflict| {
            conflict.source.role == SourceRole::Drop
                && conflict.loan.is_some()
                && conflict.target_key.starts_with("destructor::")
        }),
        "a live destructor alias must retain its retirement check: {review:?}"
    );
}

#[test]
fn cleanup_runs_before_local_obligations_end() {
    const CODE: &str = r#"
extern "Rust" { fn may_unwind(); }
pub struct Guard;
impl Drop for Guard { fn drop(&mut self) {} }
pub unsafe fn cleanup() -> i32 {
    let value = 1;
    let p = &raw const value;
    let guard = Guard;
    may_unwind();
    *p
}
"#;
    with_program(CODE, |program| {
        let function = named_function(program, "cleanup");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let facts = UnwindLiveness::analyze(program.tcx, &body);
        let p = local(&body, "p");
        let mut cleanup_edges = 0;
        let mut resumes = 0;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            if let Some(UnwindAction::Cleanup(successor)) = data.terminator().unwind() {
                assert!(body.basic_blocks[*successor].is_cleanup);
                assert!(!facts.ends_at(p, location), "cleanup still has to execute");
                cleanup_edges += 1;
            }
            if matches!(data.terminator().kind, TerminatorKind::UnwindResume) {
                assert!(
                    facts.ends_at(p, location),
                    "the nonescaping pointer ends after cleanup"
                );
                resumes += 1;
            }
        }
        assert!(
            cleanup_edges > 0 && resumes > 0,
            "the fixture must exercise cleanup and resume"
        );
    });
}
