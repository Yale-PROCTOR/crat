//! **R857-2 / R858-4 (reading (A); fan-out 074, era-5c 151) — the backstop for a
//! lent formal released through a function pointer.** brotli's
//! `BrotliEncoderDestroyInstance` is emitted at the frame with `state:
//! Option<&mut BrotliEncoderState>` and frees that referent during the call
//! through `(*m).free_func` (`BrotliDefaultFreeFunc` calls `free`): deallocating
//! behind a protected reference argument is UB under Tree Borrows and Stacked
//! Borrows (the fan-out's `repro/`, Miri). A lent formal handed to an indirect
//! call whose program-assigned targets include a releasing function is decided
//! raw (`held:released-through-indirect-call`); a target only a client supplies
//! is outside the claim (R816).
//!
//! The model is pinned to the frame's verdict (`Ref`, which the lend gives the
//! formal at the frame) with `test_model_override`, so the witness reads the
//! generator's decision, not the solver's.

use crate::analyses::borrow_ownership::SlotKind;

struct Outcome {
    source: String,
    reasons: Vec<(String, String)>,
}

fn outcome(marker: &str, text: &str) -> Outcome {
    outcome_with(marker, text, &["DestroyInstance::state"])
}

/// The frame's verdict pinned for each named formal (`Ref`).
fn outcome_with(marker: &str, text: &str, formals: &[&str]) -> Outcome {
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set(
        marker,
        Vec::new(),
        formals
            .iter()
            .map(|formal| ((*formal).to_owned(), SlotKind::Ref))
            .collect(),
    );
    // The census's A5 world (an A5 pair at a local helper's call trips the open
    // world's proof-site assertion, R805-7).
    let result = super::rewrite_m1_census_world(text);
    super::test_model_override::clear();
    match result {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            ..
        } => {
            println!("SOURCE\n{source}");
            for d in &degradations {
                println!("DEGRADED {} {}", d.subject, d.reason.key());
            }
            assert!(super::verify::type_checks_str(&source), "{source}");
            Outcome {
                source,
                reasons: degradations
                    .iter()
                    .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
                    .collect(),
            }
        }
        other => panic!("the fixture must emit: {other:?}"),
    }
}

fn reason_of<'a>(outcome: &'a Outcome, subject: &str) -> Option<&'a str> {
    outcome
        .reasons
        .iter()
        .find(|(s, _)| s.starts_with(subject))
        .map(|(_, r)| r.as_str())
}

fn signature<'a>(source: &'a str, function: &str) -> &'a str {
    source
        .lines()
        .find(|line| line.contains(&format!("fn {function}(")))
        .unwrap_or_default()
}

/// The brotli shape. `ASSIGN` is the program's own store into `free_func`.
fn fixture(marker: &str, release: &str, assign: &str) -> String {
    format!(
        "// {marker}\n\
         #![allow(dead_code, unused_unsafe, unused_mut, non_snake_case, non_camel_case_types)]\n\
         extern \"C\" {{\n\
             fn free(p: *mut core::ffi::c_void);\n\
         }}\n\
         pub type brotli_free_func =\n\
             Option<unsafe extern \"C\" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ()>;\n\
         #[derive(Copy, Clone)]\n\
         #[repr(C)]\n\
         pub struct MemoryManager {{\n\
             pub free_func: brotli_free_func,\n\
             pub opaque: *mut core::ffi::c_void,\n\
         }}\n\
         #[derive(Copy, Clone)]\n\
         #[repr(C)]\n\
         pub struct State {{\n\
             pub memory_manager_: MemoryManager,\n\
             pub k: i32,\n\
         }}\n\
         unsafe extern \"C\" fn DefaultFree(mut opaque: *mut core::ffi::c_void, mut address: *mut core::ffi::c_void) {{\n\
             {release}\n\
         }}\n\
         pub unsafe fn InitMemoryManager(mut m: *mut MemoryManager, mut free_f: brotli_free_func,\n\
             mut opaque: *mut core::ffi::c_void) {{\n\
             {assign}\n\
             (*m).opaque = opaque;\n\
         }}\n\
         unsafe fn Cleanup(mut s: *mut State) {{\n\
             (*s).k = 0;\n\
         }}\n\
         pub unsafe fn DestroyInstance(mut state: *mut State) {{\n\
             if state.is_null() {{\n\
                 return;\n\
             }}\n\
             let mut m: *mut MemoryManager = &mut (*state).memory_manager_;\n\
             let mut free_func: brotli_free_func = (*m).free_func;\n\
             let mut opaque = (*m).opaque;\n\
             Cleanup(state);\n\
             free_func.expect(\"non-null function pointer\")(opaque, state as *mut core::ffi::c_void);\n\
         }}\n"
    )
}

const DEFAULT_ASSIGNED: &str = "if free_f.is_none() {\n\
        (*m).free_func = Some(DefaultFree as unsafe extern \"C\" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ());\n\
    } else {\n\
        (*m).free_func = free_f;\n\
    }";

/// **The witness.** The program assigns `DefaultFree`, which frees its argument
/// 1, to `free_func`: the lent `state` is decided raw under the backstop's
/// reason, so the emitted function frees no reference.
#[test]
fn r857_2_a_lent_formal_released_through_a_function_pointer_is_raw() {
    let out = outcome(
        "r857-2-released",
        &fixture("r857-2-released", "free(address);", DEFAULT_ASSIGNED),
    );
    assert_eq!(
        reason_of(&out, "DestroyInstance::state"),
        Some("held:released-through-indirect-call"),
        "{:?}",
        out.reasons
    );
    let destroy = signature(&out.source, "DestroyInstance");
    assert!(destroy.contains("state: *mut State"), "raw: {destroy}");
}

/// **Control 1.** The program assigns a function of the same type that does not
/// release: the formal keeps the form the frame gives it.
#[test]
fn r857_2_control_a_non_releasing_assigned_target_stays_lent() {
    let out = outcome(
        "r857-2-nonreleasing",
        &fixture(
            "r857-2-nonreleasing",
            "let _ = (opaque, address);",
            DEFAULT_ASSIGNED,
        ),
    );
    assert_eq!(
        reason_of(&out, "DestroyInstance::state"),
        None,
        "{:?}",
        out.reasons
    );
    let destroy = signature(&out.source, "DestroyInstance");
    assert!(
        !destroy.contains("state: *mut State"),
        "delivered: {destroy}"
    );
}

/// **Control 2.** Only a client supplies `free_func` (an entry's argument with no
/// program caller); the releasing function is never assigned: outside the claim
/// (R816), so not held.
#[test]
fn r857_2_control_a_client_supplied_target_is_outside_the_claim() {
    let out = outcome(
        "r857-2-client",
        &fixture(
            "r857-2-client",
            "free(address);",
            "(*m).free_func = free_f;",
        ),
    );
    assert_eq!(
        reason_of(&out, "DestroyInstance::state"),
        None,
        "{:?}",
        out.reasons
    );
    let destroy = signature(&out.source, "DestroyInstance");
    assert!(
        !destroy.contains("state: *mut State"),
        "delivered: {destroy}"
    );
}

/// **The review's HIGH-1 (stand-in, R820-2).** The caller's own formal reaches the
/// release through a LOCAL helper that frees it through the function pointer
/// (brotli's `BrotliFree(m, p)` shape): the lend gives the caller no waiver site
/// of its own, yet its reference is freed while its protector is live. Held.
#[test]
fn r857_2_a_formal_released_through_a_local_helper_is_raw() {
    let marker = "r857-2-helper";
    let text = format!(
        "// {marker}\n\
         #![allow(dead_code, unused_unsafe, unused_mut, non_snake_case, non_camel_case_types)]\n\
         extern \"C\" {{\n\
             fn free(p: *mut core::ffi::c_void);\n\
         }}\n\
         pub type brotli_free_func =\n\
             Option<unsafe extern \"C\" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ()>;\n\
         #[derive(Copy, Clone)]\n\
         #[repr(C)]\n\
         pub struct MemoryManager {{\n\
             pub free_func: brotli_free_func,\n\
             pub opaque: *mut core::ffi::c_void,\n\
         }}\n\
         #[derive(Copy, Clone)]\n\
         #[repr(C)]\n\
         pub struct Obj {{\n\
             pub k: i32,\n\
         }}\n\
         unsafe extern \"C\" fn DefaultFree(mut opaque: *mut core::ffi::c_void, mut address: *mut core::ffi::c_void) {{\n\
             free(address);\n\
         }}\n\
         pub unsafe fn InitMemoryManager(mut m: *mut MemoryManager, mut free_f: brotli_free_func,\n\
             mut opaque: *mut core::ffi::c_void) {{\n\
             {DEFAULT_ASSIGNED}\n\
             (*m).opaque = opaque;\n\
         }}\n\
         unsafe fn BrotliFree(mut m: *mut MemoryManager, mut p: *mut core::ffi::c_void) {{\n\
             (*m).free_func.expect(\"non-null function pointer\")((*m).opaque, p);\n\
         }}\n\
         pub unsafe fn Release(mut m: *mut MemoryManager, mut obj: *mut Obj) {{\n\
             (*obj).k = 0;\n\
             BrotliFree(m, obj as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let out = outcome_with(marker, &text, &["Release::obj"]);
    assert_eq!(
        reason_of(&out, "Release::obj"),
        Some("held:released-through-indirect-call"),
        "{:?}",
        out.reasons
    );
    let release = signature(&out.source, "Release");
    assert!(release.contains("obj: *mut Obj"), "raw: {release}");
}

/// binn's shape: the program stores libc `free` itself into a static function
/// pointer and calls it on the formal. Raw: the freed-slot gate (R763) already
/// decides it (binn `binn_free#1` at the frame), the backstop otherwise.
#[test]
fn r857_2_a_formal_released_through_a_static_holding_libc_free_is_raw() {
    let marker = "r857-2-static-free";
    let text = format!(
        "// {marker}\n\
         #![allow(dead_code, unused_unsafe, unused_mut, non_snake_case, non_camel_case_types, non_upper_case_globals)]\n\
         extern \"C\" {{\n\
             fn free(p: *mut core::ffi::c_void);\n\
         }}\n\
         #[derive(Copy, Clone)]\n\
         #[repr(C)]\n\
         pub struct Item {{\n\
             pub k: i32,\n\
         }}\n\
         pub static mut free_fn: Option<unsafe extern \"C\" fn(*mut core::ffi::c_void) -> ()> = None;\n\
         unsafe fn check_alloc_functions() {{\n\
             if free_fn.is_none() {{\n\
                 free_fn = Some(free as unsafe extern \"C\" fn(*mut core::ffi::c_void) -> ());\n\
             }}\n\
         }}\n\
         pub unsafe fn item_free(mut item: *mut Item) {{\n\
             check_alloc_functions();\n\
             (*item).k = 0;\n\
             free_fn.expect(\"non-null function pointer\")(item as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let out = outcome_with(marker, &text, &["item_free::item"]);
    assert!(
        matches!(
            reason_of(&out, "item_free::item"),
            Some("freed-slot" | "held:released-through-indirect-call")
        ),
        "{:?}",
        out.reasons
    );
    let function = signature(&out.source, "item_free");
    assert!(function.contains("item: *mut Item"), "raw: {function}");
}
