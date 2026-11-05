//! Wave-6o (relay 018 §1 / R304-2): a pending sibling-overlap row is a STATED
//! HOLD, so the null-init family consults the pending inventory before
//! delivering a local whose boundary site is in it.
//!
//! binn `binn_new::item` is the corpus row (main 039 §2): delivered as
//! `Option<&mut binn>` at `binn_create(item, ..)` arg 0 while the instrument
//! held that site `t1-sibling-overlap … pending`, and the bridge-custody
//! comparator refused the program (`item:type:-!=Option<&mut binn_struct>`).
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

/// The corpus shape: `item` is null-initialized, re-pointed from the
/// allocator, and passed at arg 0 of a local callee that also receives a
/// pointer sibling (`pointer`) the callee WRITES through — a risky sibling —
/// while `item` stays live after the call (`(*item).allocated = 1`).
const BINN_NEW: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
#[repr(C)]
pub struct binn { pub header: i32, pub allocated: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
unsafe extern "C" { fn binn_malloc(size: i32) -> *mut core::ffi::c_void; fn binn_free(p: *mut core::ffi::c_void); }
unsafe fn binn_create(mut item: *mut binn, mut type_0: i32, mut size: i32, mut pointer: *mut core::ffi::c_void) -> i32 {
    if item.is_null() { return 0 as i32; }
    let mut next = item as *mut u8;
    (*item).header = type_0;
    (*item).size = size;
    if pointer.is_null() { (*item).ptr = binn_malloc(size); } else { *(pointer as *mut i32) = size; (*item).ptr = pointer; }
    return 1 as i32;
}
pub unsafe fn binn_new(mut type_0: i32, mut size: i32, mut pointer: *mut core::ffi::c_void) -> *mut binn {
    let mut item = 0 as *mut binn;
    item = binn_malloc(::core::mem::size_of::<binn>() as i32) as *mut binn;
    if binn_create(item, type_0, size, pointer) == 0 as i32 {
        binn_free(item as *mut core::ffi::c_void);
        return 0 as *mut binn;
    }
    (*item).allocated = 1 as i32;
    return item;
}
"#;

/// The control: the SAME call with a pointer sibling that the callee only
/// READS through. A potential exists (the instrument builds one for every
/// pointer sibling), but a read-only sibling is not risky, so no row is
/// pending and the declaration is inserted exactly as before.
const READ_ONLY_SIBLING: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
#[repr(C)]
pub struct binn { pub header: i32, pub allocated: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
unsafe extern "C" { fn binn_malloc(size: i32) -> *mut core::ffi::c_void; fn binn_free(p: *mut core::ffi::c_void); }
unsafe fn binn_create(mut item: *mut binn, mut type_0: i32, mut size: i32, mut pointer: *mut core::ffi::c_void) -> i32 {
    if item.is_null() { return 0 as i32; }
    let mut next = item as *mut u8;
    (*item).header = type_0;
    (*item).size = size;
    if pointer.is_null() { (*item).ptr = binn_malloc(size); } else { (*item).size = *(pointer as *mut i32); }
    return 1 as i32;
}
pub unsafe fn binn_new(mut type_0: i32, mut size: i32, mut pointer: *mut core::ffi::c_void) -> *mut binn {
    let mut item = 0 as *mut binn;
    item = binn_malloc(::core::mem::size_of::<binn>() as i32) as *mut binn;
    if binn_create(item, type_0, size, pointer) == 0 as i32 {
        binn_free(item as *mut core::ffi::c_void);
        return 0 as *mut binn;
    }
    (*item).allocated = 1 as i32;
    return item;
}
"#;

fn decision_of(input: &str, function: &str, binding: &str) -> String {
    assert!(verify::type_checks_str(input));
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived local");
        match decision {
            Decision::Degraded(degradation) => degradation.reason.key().to_owned(),
            other => format!("{other:?}").chars().take(40).collect::<String>(),
        }
    })
    .expect("fixture compiler context")
}

#[test]
fn wave6o_null_init_local_at_a_pending_sibling_site_stays_raw() {
    assert_eq!(
        decision_of(BINN_NEW, "binn_new", "item"),
        "pending-sibling-overlap",
        "a pending sibling-overlap row is a stated hold (R304-2): the null-init family may not deliver over it"
    );
    let output = ast_emitted_source_of(BINN_NEW).expect("native emission");
    assert!(
        !output.contains("item: Option<"),
        "the held local keeps its raw declaration:\n{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

#[test]
fn wave6o_null_init_local_with_no_pending_row_still_receives_its_declaration() {
    let decision = decision_of(READ_ONLY_SIBLING, "binn_new", "item");
    eprintln!("WAVE6O_PENDING_CONTROL_DECISION {decision}");
    assert!(
        decision.starts_with("Opt"),
        "a read-only sibling is not risky: no pending row, so the declaration is inserted as before"
    );
    let output = ast_emitted_source_of(READ_ONLY_SIBLING).expect("native emission");
    assert!(
        output.contains("item: Option<&mut "),
        "the control must still deliver:\n{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}
