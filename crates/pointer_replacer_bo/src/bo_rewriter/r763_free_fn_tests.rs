//! **R763-1 item 2 (wave-6o 095 STOP 1) — a free through the program's allocator
//! function pointer.** binn's emitted `binn_free(item: Option<&mut binn>)` releases
//! `item` itself through `free_fn`, a `static mut` function pointer every assignment
//! of which is a deallocator (`Some(free)` in `check_alloc_functions`, the setter
//! `binn_set_alloc_functions`'s formal). A reference formal is protected for the
//! call, so the release is "deallocation through a strongly protected tag" under
//! Tree Borrows. The freed-slot gate (S2-2) saw only direct `free(..)` calls.
use super::wave6a_allocation_tests::{emitted, reason_of};

fn program(extra_assignment: &str) -> String {
    format!(
        r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_upper_case_globals)]
extern "C" {{
    fn free(p: *mut core::ffi::c_void);
}}
pub struct Item {{ pub allocated: i32, pub value: i32 }}
#[no_mangle]
pub static mut free_fn: Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()> = None;
unsafe extern "C" fn log_only(p: *mut core::ffi::c_void) {{}}
#[no_mangle]
pub unsafe extern "C" fn set_alloc(mut new_free: Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>) {{
    free_fn = new_free;
}}
unsafe extern "C" fn check_alloc() {{
    if free_fn.is_none() {{
        free_fn = Some(free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ());
    }}
    {extra_assignment}
}}
#[no_mangle]
pub unsafe extern "C" fn release(mut item: *mut Item) {{
    if item.is_null() {{ return; }}
    (*item).value = 0;
    if (*item).allocated != 0 {{
        free_fn.expect("non-null function pointer")(item as *mut core::ffi::c_void);
    }}
}}
"#
    )
}

#[test]
fn r763_b_a_formal_released_through_a_deallocator_pointer_is_freed() {
    let out = emitted("r763_free_fn", &program(""));
    assert_eq!(
        reason_of(&out.degradations, "release::item").as_deref(),
        Some("freed-slot"),
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
}

/// Control: a function pointer one of whose assignments is NOT a deallocator is not
/// a free; the formal keeps its reference form.
#[test]
fn r763_b_control_a_pointer_also_assigned_a_non_deallocator_is_not_a_free() {
    let out = emitted(
        "r763_free_fn_control",
        &program(
            "free_fn = Some(log_only as unsafe extern \"C\" fn(*mut core::ffi::c_void) -> ());",
        ),
    );
    assert_ne!(
        reason_of(&out.degradations, "release::item").as_deref(),
        Some("freed-slot"),
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
}
