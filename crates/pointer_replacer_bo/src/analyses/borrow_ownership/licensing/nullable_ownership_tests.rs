use super::{super::SlotKind, tests::inspect};

#[test]
fn conditional_allocation_into_a_null_local_keeps_ownership() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn run(flag: bool) {
    let mut p = 0 as *mut u8;
    if flag { p = malloc(8) as *mut u8; }
    free(p as *mut core::ffi::c_void);
}
"#,
    );
    fixture.assert_kind("run::p", SlotKind::Owning);
    for snapshot in fixture.export.ownership_licensing.as_ref().unwrap() {
        snapshot.validate().expect("nullable ownership receipt");
    }
}

#[test]
fn null_constructors_copies_and_nested_paths_keep_nullable_owners() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
const NONE: *mut u8 = 0 as *mut u8;
pub unsafe fn calloc_owner(flag: bool) {
    let mut p = core::ptr::null_mut::<u8>();
    if flag { p = calloc(4, 2) as *mut u8; }
    free(p as *mut core::ffi::c_void);
}
pub unsafe fn copied_owner(flag: bool) {
    let empty = NONE;
    let mut p = empty;
    if flag {
        let allocated = malloc(8) as *mut u8;
        p = allocated;
    }
    free(p as *mut core::ffi::c_void);
}
pub unsafe fn nested_owner(first: bool, second: bool) {
    let mut p = NONE;
    if first {
        if second { p = malloc(8) as *mut u8; }
    } else {
        p = malloc(16) as *mut u8;
    }
    free(p as *mut core::ffi::c_void);
}
pub unsafe fn reversed_owner(flag: bool) {
    let mut p = NONE;
    if flag {} else { p = malloc(8) as *mut u8; }
    free(p as *mut core::ffi::c_void);
}
"#,
    );
    for key in [
        "calloc_owner::p",
        "copied_owner::p",
        "nested_owner::p",
        "reversed_owner::p",
    ] {
        fixture.assert_kind(key, SlotKind::Owning);
    }
}

#[test]
fn null_receivers_accept_direct_allocator_and_local_call_results() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn make() -> *mut u8 { malloc(8) }
pub unsafe fn direct(flag: bool) {
    let mut p = core::ptr::null_mut();
    if flag { p = malloc(8); }
    free(p);
}
pub unsafe fn wrapped(flag: bool) {
    let mut p = core::ptr::null_mut();
    if flag { p = make(); }
    free(p);
}
"#,
    );
    for key in ["make::_0", "direct::p", "wrapped::p"] {
        fixture.assert_kind(key, SlotKind::Owning);
    }
    let equations = fixture.export.ownership_equations.as_ref().unwrap();
    assert!(equations.iter().any(|row| {
        row.operation == "null-overwrite"
            && row.point.function.as_deref() == Some("wrapped")
            && row.point.phase == "statement"
    }));
}

#[test]
fn live_overwrites_nonzero_constants_and_leaks_do_not_gain_ownership() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
pub unsafe fn overwrite_live(flag: bool) {
    let mut p = malloc(8);
    if flag { p = malloc(16); }
    free(p);
}
pub unsafe fn overwrite_with_null(flag: bool) {
    let mut p = malloc(8);
    if flag { p = core::ptr::null_mut(); }
    free(p);
}
pub unsafe fn sentinel(flag: bool) {
    let mut p = 1 as *mut u8;
    if flag { p = malloc(8); }
    free(p);
}
pub unsafe fn leak(flag: bool) -> bool {
    let mut p = core::ptr::null_mut();
    if flag { p = malloc(8); }
    p.is_null()
}
pub unsafe fn loop_overwrite(count: usize) {
    let mut p = core::ptr::null_mut();
    for _ in 0..count { p = malloc(8); }
    free(p);
}
"#,
    );
    for key in [
        "overwrite_live::p",
        "overwrite_with_null::p",
        "sentinel::p",
        "leak::p",
        "loop_overwrite::p",
    ] {
        fixture.assert_kind(key, SlotKind::Raw);
    }
    let equations = fixture.export.ownership_equations.as_ref().unwrap();
    assert!(!equations.iter().any(|row| {
        row.operation == "null-overwrite"
            && matches!(
                row.point.function.as_deref(),
                Some("overwrite_live" | "overwrite_with_null" | "sentinel" | "loop_overwrite")
            )
    }));
}

#[test]
fn clobbered_locals_and_lookalike_null_constructors_supply_no_null_proof() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
    fn clobber(cell: *mut *mut u8);
    fn opaque() -> *mut u8;
}
unsafe fn null_mut() -> *mut u8 { malloc(8) }
pub unsafe fn called(flag: bool) {
    let mut p = core::ptr::null_mut();
    clobber(&raw mut p);
    if flag { p = malloc(16); }
    free(p);
}
pub unsafe fn stored(flag: bool) {
    let mut p = core::ptr::null_mut();
    let cell = &raw mut p;
    *cell = opaque();
    if flag { p = malloc(16); }
    free(p);
}
pub unsafe fn lookalike(flag: bool) {
    let mut p = null_mut();
    if flag { p = malloc(16); }
    free(p);
}
"#,
    );
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    assert!(
        !fixture
            .export
            .ownership_equations
            .as_ref()
            .unwrap()
            .iter()
            .any(|row| row.operation == "null-overwrite"),
        "a cell that may hold an allocation cannot discharge its old-owner obligation"
    );
    fixture.assert_kind("lookalike::p", SlotKind::Raw);
}

#[test]
fn nullable_allocation_keeps_copy_conservation_and_one_owned_release() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
pub unsafe fn run(flag: bool) {
    let mut p = core::ptr::null_mut();
    if flag { p = malloc(8); }
    let q = p;
    free(p);
    free(q);
}
"#,
    );
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    let equations = fixture.export.ownership_equations.as_ref().unwrap();
    let values = fixture.export.version_owns.as_ref().unwrap();
    let value = |var| values[super::super::ssa::constraint::Var::from_u32(var)];
    let sinks = equations
        .iter()
        .filter(|row| row.operation == "sink")
        .collect::<Vec<_>>();
    assert_eq!(sinks.len(), 2);
    assert_eq!(
        sinks.iter().filter(|row| value(row.variables[0])).count(),
        1,
        "one allocation cannot supply two owning releases"
    );
    let active_copies = equations
        .iter()
        .filter(|row| row.operation == "linear" && value(row.variables[2]))
        .collect::<Vec<_>>();
    assert!(!active_copies.is_empty(), "exercise an allocated copy");
    for row in active_copies {
        assert_eq!(
            u8::from(value(row.variables[0])) + u8::from(value(row.variables[1])),
            1,
            "the allocation's responsibility is transferred, never duplicated"
        );
    }
    for sink in sinks {
        assert!(
            equations.iter().any(|row| {
                row.point == sink.point
                    && row.operation == "assume"
                    && row.assumption_class.as_deref() == Some("libc-rule")
                    && row.value == Some(false)
                    && !value(row.variables[0])
            }),
            "release still clears its post-value"
        );
    }
}

#[test]
fn a_callee_cannot_overwrite_an_exposed_call_destination_using_its_pre_call_null() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn fill(cell: *mut *mut u8) -> *mut u8 {
    *cell = malloc(8);
    malloc(16)
}
pub unsafe fn run(flag: bool) {
    let mut p = core::ptr::null_mut();
    if flag { p = fill(&raw mut p); }
    free(p);
}
"#,
    );
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    assert!(
        !fixture
            .export
            .ownership_equations
            .as_ref()
            .unwrap()
            .iter()
            .any(|row| row.operation == "null-overwrite"
                && row.point.function.as_deref() == Some("run")),
        "the value retired by the return store may have been changed by the call"
    );
}
