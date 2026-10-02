//! **R674-6 / R675 — main's 53 line, re-cut for 54 (R761-1).** The PAIR rendering's
//! E0425 witness (`e53e81e49`). The (iii-a) witnesses of `40b43b8a6` travel with their
//! fix `ea01deb2b`, which needs wave-5d's element-pointer arm and the guard's per-caller
//! conjunct (`94488538c`) after wave-6l's line A, so they are not in this file yet.
use super::wave6a_allocation_tests::{compact, emitted};

/// **The PAIR rendering's E0425 (main 131e; wave-5d 098 STOP 1).** The same-object
/// PAIR arm hoists `(*t).root` for a call to `start`, whose surfaced helper
/// `__crat_safe_start` lives in `provider` and is not what `consumer`'s `use`
/// imports. The arm re-parses the call from its printed text, so the rendered
/// callee is a new node and `wave5r_helper_path::qualify`, which finds a helper's
/// calls by their callee span, never qualifies it: before the fix (52's
/// `fd4a06ccf` and this line) the program degrades (`recovery-degraded`) on
/// `cannot find function __crat_safe_start`.
/// wave-5d's fixture, verbatim.
const PAIR_E0425: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
extern "C" {
    fn getenv(name: *const i8) -> *mut i8;
}
pub struct Tree { pub root: *mut i32, pub length: u32 }
pub mod provider {
    pub unsafe fn start(t: *mut crate::Tree, q: *mut i32, p: *const i32) -> *const i8 {
        (*t).length += 1;
        if *p == 0 {
            return 0 as *const i8;
        }
        crate::getenv(b"HOME\0" as *const u8 as *const i8) as *const i8
    }
    pub fn install() {
        let _callback: unsafe fn(*mut crate::Tree, *mut i32, *const i32) -> *const i8 = start;
    }
}
pub mod consumer {
    use crate::provider::start;
    pub unsafe fn imported(t: *mut crate::Tree, p: *const i32) -> i32 {
        let mut s = start(t, (*t).root, p);
        let mut i: usize = 0;
        while *s.offset(i as isize) != 0 {
            i = i.wrapping_add(1);
        }
        i as i32
    }
}
"#;

#[test]
fn r675_pair_e0425_a_hoisted_call_to_a_surfaced_imported_helper_is_qualified() {
    let out = emitted("r675_pair_e0425", PAIR_E0425);
    let flat = compact(&out.source);
    assert!(
        flat.contains("__crat_pair_raw_"),
        "the call takes the PAIR raw view (the arm under test): {}",
        out.source
    );
    assert!(
        flat.contains("crate::provider::__crat_safe_start("),
        "the hoisted call reaches the helper through its defining module: {}",
        out.source
    );
}
