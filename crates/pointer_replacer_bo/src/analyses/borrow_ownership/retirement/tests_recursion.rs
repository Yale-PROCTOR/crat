use super::{
    objects::ObjectRoot,
    routes,
    tests::accepts,
    tests_call_reach::object_facts,
    tests_return_origin::{named_function, with_program},
};
use crate::analyses::borrow_ownership::{
    copy_relax_tests::kinds,
    source_events::{self, SourceRole},
};

const FRESH_BUFFERS: &str = r#"
pub unsafe extern "C" fn direct(p: *mut i32, remaining: u32) {
    if remaining > 0 { direct(p, remaining - 1); }
    let scratch = std::vec::from_elem(0i32, 4);
    *p += scratch[0];
}
pub unsafe extern "C" fn outer(p: *mut i32) { direct(p, 2); }
pub unsafe extern "C" fn first(p: *mut i32, remaining: u32) {
    if remaining > 0 { second(p, remaining - 1); }
}
pub unsafe extern "C" fn second(p: *mut i32, remaining: u32) {
    if remaining > 0 { first(p, remaining - 1); }
    let scratch = std::vec::from_elem(0i32, 4);
    *p += scratch[0];
}
pub unsafe extern "C" fn indirect(p: *mut i32, remaining: u32) {
    let next: unsafe extern "C" fn(*mut i32, u32) = indirect;
    if remaining > 0 { next(p, remaining - 1); }
    let scratch = std::vec::from_elem(0i32, 4);
    *p += scratch[0];
}
"#;

#[test]
fn recursive_fresh_buffer_drops_preserve_reference_parameters() {
    let kinds = kinds(FRESH_BUFFERS);
    for function in ["direct", "outer", "first", "second", "indirect"] {
        assert_eq!(
            kinds.get(&format!("{function}::p")).map(String::as_str),
            Some("ref"),
            "{function}: {kinds:?}"
        );
    }
}

#[test]
fn recursive_fresh_effects_remain_finite_and_reach_outer_callers() {
    with_program(FRESH_BUFFERS, |program| {
        let events = source_events::collect(program);
        let facts = object_facts(program);
        let routed = routes::expand(program, &events, &facts);
        assert!(routed.problems.is_empty(), "{:?}", routed.problems);
        for name in ["direct", "outer", "first", "second", "indirect"] {
            let function = named_function(program, name);
            let drops = routed.frames[&function]
                .iter()
                .filter(|event| {
                    event.source.key.role == SourceRole::Drop && !event.route.is_empty()
                })
                .collect::<Vec<_>>();
            assert!(!drops.is_empty(), "{name} must retain routed destruction");
            assert!(
                drops.len() < 30,
                "{name}: recursive summaries must terminate with finite contexts"
            );
            for event in drops {
                assert!(
                    !event.objects.unknown && !event.objects.roots.is_empty(),
                    "{name}: {event:?}"
                );
                assert!(event.objects.roots.iter().all(|root| matches!(root,
                    ObjectRoot::Fresh { frame, site } if *frame == function && *site == event.location)),
                    "freshness is relative to the current call, not a fabricated dynamic epoch: {event:?}");
                assert!(event.uncertainty.is_none(), "{name}: {event:?}");
            }
        }
    });
}

#[test]
fn e5_p_recursive_raw_wrapper_cannot_hide_retirement_of_caller_entry() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
}
unsafe fn release_pair(p: *mut u8, q: *mut u8, remaining: u8) {
    if remaining == 0 {
        free(p);
    } else {
        release_pair(q, p, remaining - 1);
    }
}
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let fresh = malloc(1);
    release_pair(fresh, entry as *mut u8, 1);
    value
}
"#;
    assert!(
        !accepts(CODE, &[("caller", 1, 0)]),
        "the recursive swap retires the caller's protected input; the outer route cannot keep only the disjoint fresh argument"
    );
}

const MIXED_ROUTES: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe extern "C" fn release(raw: *mut u8) { free(raw); }
unsafe extern "C" fn pair(p: *mut u8, q: *mut u8, remaining: u8, choose: bool) {
    if choose { release(malloc(1)); } else { release(p); }
    if remaining > 0 { pair(q, p, remaining - 1, choose); }
}
pub unsafe extern "C" fn caller(entry: *const u8, choose: bool) -> u8 {
    let value = *entry;
    let fresh = malloc(1);
    pair(fresh, entry as *mut u8, 1, choose);
    value
}
"#;

#[test]
fn recursive_join_keeps_fresh_and_unknown_paths_separate() {
    with_program(MIXED_ROUTES, |program| {
        let events = source_events::collect(program);
        let facts = object_facts(program);
        let routed = routes::expand(program, &events, &facts);
        assert!(routed.problems.is_empty(), "{:?}", routed.problems);
        let pair = named_function(program, "pair");
        let recursive = routed.frames[&pair]
            .iter()
            .filter(|event| {
                event.source.key.function == "release"
                    && event.source.key.role == SourceRole::Free
                    && event
                        .route
                        .last()
                        .is_some_and(|step| step.caller == pair && step.callee == pair)
            })
            .collect::<Vec<_>>();
        assert!(
            recursive.iter().any(|event| !event.objects.unknown),
            "the recursive call must receive its fresh branch"
        );
        assert!(
            recursive.iter().any(|event| event.objects.unknown),
            "the same call must also retain its potentially retiring input branch"
        );
        let caller = named_function(program, "caller");
        assert!(
            routed.frames[&caller]
                .iter()
                .any(|event| { event.source.key.function == "release" && event.objects.unknown }),
            "recursive uncertainty must still propagate outside the cycle"
        );
    });
    assert!(
        !accepts(MIXED_ROUTES, &[("caller", 1, 0)]),
        "a fresh path cannot suppress the recursive swap that can retire entry"
    );
}

#[test]
fn recursive_release_of_a_caller_allocation_still_conflicts_with_its_borrow() {
    const CODE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe extern "C" fn release(p: *mut u8, remaining: u8) {
    if remaining > 0 { release(p, remaining - 1); } else { free(p); }
}
pub unsafe extern "C" fn caller() -> u8 {
    let owned = malloc(1);
    let view = &raw const *owned;
    let value = *view;
    release(owned, 1);
    value + *view
}
"#;
    let review = super::tests_loans::review_local(CODE, "caller", "view");
    assert!(
        review.conflicts.iter().any(|conflict| {
            conflict.source.role == SourceRole::Free && conflict.target_key.starts_with("caller::")
        }),
        "callee inputs may release a caller allocation already borrowed there: {review:?}"
    );
}

#[test]
fn escaped_allocation_roots_do_not_supply_a_recursive_freshness_proof() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
    fn clobber(cell: *mut *mut u8);
}
pub unsafe extern "C" fn escaped(entry: *const u8, remaining: u8) -> u8 {
    let mut raw = malloc(1);
    if remaining > 0 { raw = malloc(2); }
    clobber(&raw mut raw);
    if remaining > 0 { escaped(entry, remaining - 1); }
    let value = *entry;
    free(raw);
    value
}
"#;
    with_program(CODE, |program| {
        let events = source_events::collect(program);
        let facts = object_facts(program);
        let routed = routes::expand(program, &events, &facts);
        assert!(routed.problems.is_empty(), "{:?}", routed.problems);
        let function = named_function(program, "escaped");
        let frees = routed.frames[&function]
            .iter()
            .filter(|event| event.source.key.role == SourceRole::Free)
            .collect::<Vec<_>>();
        assert!(
            frees.iter().any(|event| {
                event.route.is_empty()
                    && event.objects.unknown
                    && event
                        .objects
                        .roots
                        .iter()
                        .any(|root| matches!(root, ObjectRoot::Fresh { .. }))
            }),
            "the clobber must retain a Fresh root alongside its unknown alternative"
        );
        assert!(
            frees.iter().any(|event| {
                !event.route.is_empty() && event.objects.unknown && event.objects.roots.is_empty()
            }),
            "partial evidence cannot enter the preserved recursive class"
        );
    });
    assert!(!accepts(CODE, &[("escaped", 1, 0)]));
}

#[test]
fn missing_recursive_route_evidence_overrides_fresh_objects() {
    with_program(FRESH_BUFFERS, |program| {
        let mut events = source_events::collect(program);
        for call in &mut events.calls {
            if call.caller == "direct" && call.callee == "direct" {
                call.events.retain(|event| event.role != SourceRole::Drop);
            }
        }
        let facts = object_facts(program);
        let routed = routes::expand(program, &events, &facts);
        assert!(
            routed
                .problems
                .iter()
                .any(|problem| { problem.reason == super::RouteReason::MissingRouteEvent })
        );
        let direct = named_function(program, "direct");
        let cyclic = routed.frames[&direct]
            .iter()
            .filter(|event| {
                event.source.key.role == SourceRole::Drop
                    && event
                        .route
                        .last()
                        .is_some_and(|step| step.caller == direct && step.callee == direct)
            })
            .collect::<Vec<_>>();
        assert!(!cyclic.is_empty());
        assert!(
            cyclic.iter().all(|event| event.objects.unknown),
            "known allocations cannot repair missing route evidence"
        );
    });
}

#[test]
fn mixed_or_unknown_recursive_releases_still_reject_incoming_borrows() {
    const CODE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); fn opaque() -> *mut u8; }
pub unsafe extern "C" fn mixed(p: *mut u8, remaining: u8, choose: bool) {
    let raw = if choose { malloc(1) } else { p };
    if remaining > 0 { mixed(p, remaining - 1, choose); }
    free(raw);
}
pub unsafe extern "C" fn unknown(p: *const u8, remaining: u8) -> u8 {
    if remaining > 0 { unknown(p, remaining - 1); }
    let value = *p;
    free(opaque());
    value
}
pub unsafe extern "C" fn owning_elements(p: *mut u8, remaining: u8) -> u8 {
    if remaining > 0 { owning_elements(p, remaining - 1); }
    let value = *p;
    let owners = std::vec::from_elem(Box::from_raw(p), 1);
    value
}
"#;
    for function in ["mixed", "unknown", "owning_elements"] {
        assert!(
            !accepts(CODE, &[(function, 1, 0)]),
            "{function} lacks a closed callee-fresh release proof"
        );
    }
}
