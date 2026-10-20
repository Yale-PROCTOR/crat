//! O01/O06 objective controls. Fixture programs are analyzed, never executed.

use super::{
    super::{SlotKind, ownership_boundary::Role, ownership_occurrence::Availability},
    tests::inspect,
};

#[test]
fn o06_fresh_buffer_return_owns_outer_allocation_despite_borrowed_character_field() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(bytes: usize) -> *mut core::ffi::c_void;
    fn free(pointer: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Buffer { data: *mut u8, len: usize }
pub unsafe fn buffer_new_with_string_length(data: *mut u8, len: usize) -> *mut Buffer {
    let buffer = malloc(core::mem::size_of::<Buffer>()) as *mut Buffer;
    (*buffer).data = data;
    (*buffer).len = len;
    buffer
}
pub unsafe fn buffer_new_with_string(data: *mut u8) -> *mut Buffer {
    buffer_new_with_string_length(data, 1)
}
pub unsafe fn read_string(data: *mut u8) -> u8 {
    let buffer = buffer_new_with_string(data);
    let value = *(*buffer).data;
    free(buffer as *mut core::ffi::c_void);
    value
}
"#,
    );
    let equations = fixture
        .export
        .ownership_equations
        .as_ref()
        .expect("actual ownership equations");
    let sources: Vec<_> = equations
        .iter()
        .filter(|row| row.operation == "source")
        .collect();
    assert_eq!(sources.len(), 1, "only the outer Buffer is allocated");
    let source = sources[0].endpoint.as_ref().expect("typed Source endpoint");
    assert_eq!(source.function, "buffer_new_with_string_length");
    assert_eq!(source.callee, "malloc");
    let sinks: Vec<_> = equations
        .iter()
        .filter(|row| row.operation == "sink")
        .collect();
    assert_eq!(
        sinks.len(),
        1,
        "the character storage is not freed by this fixture"
    );
    assert_eq!(sinks[0].endpoint.as_ref().unwrap().function, "read_string");

    let boundaries = fixture
        .export
        .ownership_boundary_substitutions
        .as_ref()
        .expect("actual call substitutions");
    for (caller, callee) in [
        ("buffer_new_with_string", "buffer_new_with_string_length"),
        ("read_string", "buffer_new_with_string"),
    ] {
        let rows: Vec<_> = boundaries
            .iter()
            .filter(|row| {
                row.role == Role::ReturnReceiver
                    && row.point.function.as_deref() == Some(caller)
                    && row.callee.as_deref() == Some(callee)
            })
            .collect();
        assert_eq!(rows.len(), 1, "one exact receiver for {caller} -> {callee}");
        assert!(matches!(
            rows[0].actual_occurrence,
            Availability::Present(_)
        ));
        assert!(!rows[0].matched.is_empty());
    }

    for key in [
        "buffer_new_with_string_length::buffer",
        "buffer_new_with_string_length::_0",
        "buffer_new_with_string::_0",
        "read_string::buffer",
    ] {
        fixture.assert_kind(key, SlotKind::Owning);
    }
    fixture.assert_not_owning("Buffer.data");
}

#[test]
fn o01_o05_borrowed_buffer_return_and_alias_remain_ref() {
    let fixture = inspect(
        r#"
pub struct Buffer { data: *mut u8, len: usize }
pub unsafe fn borrowed(buffer: *mut Buffer) -> *mut Buffer {
    let view = buffer;
    let _length = (*view).len;
    view
}
"#,
    );
    let equations = fixture
        .export
        .ownership_equations
        .as_ref()
        .expect("actual ownership equations");
    assert!(
        equations
            .iter()
            .all(|row| row.operation != "source" && row.operation != "sink")
    );
    let boundaries = fixture
        .export
        .ownership_boundary_substitutions
        .as_ref()
        .expect("actual borrowed-return substitutions");
    for role in [Role::Entry, Role::ExitReturn] {
        assert!(
            boundaries.iter().any(|row| row.role == role
                && row.point.function.as_deref() == Some("borrowed")
                && !row.matched.is_empty()),
            "borrowed return retains its actual {role:?} correspondence"
        );
    }
    for key in ["borrowed::buffer", "borrowed::view", "borrowed::_0"] {
        fixture.assert_kind(key, SlotKind::Ref);
    }
}

#[test]
fn o03_fresh_return_receiver_cannot_be_ref_when_final_zero_refuses_ownership() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(bytes: usize) -> *mut core::ffi::c_void; }
pub struct Buffer { data: *mut u8, len: usize }
pub unsafe fn buffer_new() -> *mut Buffer {
    let buffer = malloc(core::mem::size_of::<Buffer>()) as *mut Buffer;
    (*buffer).data = 0 as *mut u8;
    (*buffer).len = 1;
    buffer
}
pub unsafe fn read_length() -> usize {
    let buffer = buffer_new();
    (*buffer).len
}
"#,
    );
    assert!(fixture.accepted, "fixture must reach kind selection");
    assert_eq!(
        fixture.kinds.get("read_length::buffer"),
        Some(&SlotKind::Raw),
        "a fresh return has no borrow origin; with unchanged live-local final-zero, a refused owner stays Raw"
    );
    let equations = fixture.export.ownership_equations.as_ref().unwrap();
    assert!(!equations.iter().any(|row| row.operation == "sink"));
    assert!(
        equations
            .iter()
            .any(|row| row.point.function.as_deref() == Some("read_length")
                && row.operation == "assume"
                && row.assumption_class.as_deref() == Some("temporary-finalization")
                && row.value == Some(false)),
        "the final-zero law stays present"
    );
}

#[test]
fn o07_nullable_owner_and_nullable_borrow_keep_distinct_kinds() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make(empty: bool) -> *mut i32 {
    if empty { 0 as *mut i32 } else { malloc(4) }
}
pub unsafe fn run(empty: bool) { let p = make(empty); free(p); }
pub unsafe fn borrowed(empty: bool, p: *mut i32) -> *mut i32 {
    if empty { 0 as *mut i32 } else { p }
}
pub fn null_only() -> *mut i32 { 0 as *mut i32 }
"#,
    );
    for key in ["make::_0", "run::p"] {
        fixture.assert_kind(key, SlotKind::Owning);
    }
    for key in ["borrowed::p", "borrowed::_0", "null_only::_0"] {
        fixture.assert_kind(key, SlotKind::Ref);
    }
}

#[test]
fn o07_nullable_fresh_receiver_does_not_gain_ref_after_owner_refusal() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make(empty: bool) -> *mut i32 {
    if empty { 0 as *mut i32 } else { malloc(4) }
}
pub unsafe fn run(empty: bool) -> bool { let p = make(empty); p.is_null() }
"#,
    );
    fixture.assert_kind("run::p", SlotKind::Raw);
}

#[test]
fn o08_opaque_and_integer_pointer_results_keep_ordinary_raw_preference() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn opaque() -> *mut i32; }
pub unsafe fn unknown() -> *mut i32 { opaque() }
pub fn integer(address: usize) -> *mut i32 { address as *mut i32 }
"#,
    );
    fixture.assert_kind("unknown::_0", SlotKind::Raw);
    fixture.assert_kind("integer::_0", SlotKind::Raw);
}
