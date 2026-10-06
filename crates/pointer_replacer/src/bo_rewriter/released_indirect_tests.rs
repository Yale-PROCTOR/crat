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

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::analyses::borrow_ownership::SlotKind;

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Outcome {
    source: String,
    reasons: Vec<(String, String)>,
}

fn outcome(marker: &str, text: &str) -> Outcome {
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set(
        marker,
        Vec::new(),
        vec![("DestroyInstance::state".to_owned(), SlotKind::Ref)],
    );
    let dir = std::env::temp_dir().join(format!(
        "crat-r857-released-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let root = dir.join("lib.rs");
    std::fs::write(&root, text).expect("fixture root");
    let result = super::rewrite_m1_path(&root);
    super::test_model_override::clear();
    let _ = std::fs::remove_dir_all(&dir);
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
