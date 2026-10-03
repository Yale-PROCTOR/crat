//! **R674-6 / R675 — main's 53 line, re-cut for 54 (R761-1).** The PAIR rendering's
//! E0425 witness (`e53e81e49`), then the (iii-a) witnesses of `40b43b8a6`, re-cut after
//! wave-5d's element-pointer arm with their fix `ea01deb2b`.
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

/// **(iii-a) — R641-2's slice-root exemption follows placement.** brotli
/// `FindLongestMatchH5::data#3` (52: `unplaceable:slice-use-evidence-held`):
/// its decision is `Slice`, so the seam's element-spine exemption admitted the
/// one-element adapter `from_ref(&*data.offset(k))` into `HashBytesH5`, which
/// reads four bytes — and the spine that makes that argument a tail view was
/// never placed, because another of the root's slice uses is held (here the
/// hand-on into `opaque`, whose raw parameter is never settled safe).
const H5_UNPLACED_ROOT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> u32 {
    return *(p as *const u32);
}
unsafe extern "C" fn HashBytesH5(mut data: *const u8, shift: i32) -> u32 {
    let mut h = BrotliUnalignedRead32(data as *const core::ffi::c_void).wrapping_mul(0x1e35a7bd as u32);
    return h >> shift;
}
unsafe extern "C" fn FindMatchLengthWithLimit(mut s1: *const u8, mut s2: *const u8, mut limit: usize) -> usize {
    let mut matched = 0 as i32 as usize;
    while matched < limit && *s1.offset(matched as isize) as i32 == *s2.offset(matched as isize) as i32 {
        matched = matched.wrapping_add(1);
    }
    if matched == 0 {
        s2 = s1;
    }
    return matched.wrapping_add(*s2 as usize);
}
unsafe extern "C" fn FindLongestMatchH5(mut data: *const u8, mut mask: usize, mut cur_ix: usize) -> u32 {
    let cur_ix_masked = cur_ix & mask;
    let seen = FindMatchLengthWithLimit(&*data.offset(1 as i32 as isize), &*data.offset(cur_ix_masked as isize), 8);
    let first = *data.offset(cur_ix_masked as isize);
    let key = HashBytesH5(&*data.offset(cur_ix_masked as isize), 3);
    return key.wrapping_add(first as u32).wrapping_add(seen as u32);
}
unsafe extern "C" fn StoreH5(mut data: *const u8, mut mask: usize, mut ix: usize) -> u32 {
    let first = *data.offset((ix & mask) as isize);
    let key = HashBytesH5(&*data.offset((ix & mask) as isize), 3);
    return key.wrapping_add(first as u32);
}
pub unsafe extern "C" fn entry(mut buf: *const u8) -> u32 {
    return FindLongestMatchH5(buf, 63, 5).wrapping_add(StoreH5(buf, 63, 7));
}
"#;

fn one_element_adapters(source: &str) -> usize {
    let own = source
        .split("pub mod slice_cursor")
        .next()
        .unwrap_or(source);
    let flat = compact(own);
    flat.matches("slice::from_ref(").count() + flat.matches("slice::from_mut(").count()
}

#[test]
fn r674_iii_a_an_unplaced_slice_root_gives_no_one_element_adapter_into_a_wide_reader() {
    let out = emitted("r674-h5-unplaced-root", H5_UNPLACED_ROOT);
    eprintln!(
        "{}",
        out.source
            .split("pub mod slice_cursor")
            .next()
            .unwrap_or("")
    );
    assert_eq!(
        one_element_adapters(&out.source),
        0,
        "a root whose slice is not placed has no tail view: its element address must not reach \
         HashBytesH5's four-byte read as a one-element slice\n{}",
        out.source
    );
}

/// **(iii-a) control — a PLACED root keeps its tail view.** The same callee
/// and the same element address, from a caller whose slice is placed: the
/// argument renders as the root's own suffix (R641-2's reason for the
/// exemption, r609's `code_lengths` / `storeh2`), with no one-element adapter.
const H5_PLACED_ROOT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> u32 {
    return *(p as *const u32);
}
unsafe extern "C" fn HashBytesH5(mut data: *const u8, shift: i32) -> u32 {
    let mut h = BrotliUnalignedRead32(data as *const core::ffi::c_void).wrapping_mul(0x1e35a7bd as u32);
    return h >> shift;
}
unsafe extern "C" fn StoreH5(mut data: *const u8, mut mask: usize, mut ix: usize) -> u32 {
    let first = *data.offset((ix & mask) as isize);
    let key = HashBytesH5(&*data.offset((ix & mask) as isize), 3);
    return key.wrapping_add(first as u32);
}
pub unsafe extern "C" fn entry(mut buf: *const u8) -> u32 {
    return StoreH5(buf, 63, 7);
}
"#;

#[test]
fn r674_iii_a_control_a_placed_slice_root_keeps_its_tail_view() {
    let out = emitted("r674-h5-placed-root", H5_PLACED_ROOT);
    let flat = compact(&out.source);
    // Restated for 54 (R761-1, R217-2): the one one-element adapter left is
    // `entry`'s thin `buf` handed on whole, `StoreH5(core::slice::from_ref(buf), ..)`
    // — shape (i), which 53 held through the thin-caller hold that R761-1 leaves out
    // and 55's thin-into-fat rule delivers as a slice. The element address under test
    // takes no adapter (below). RED first: at `89f4c0046` the count read 1, not 0.
    assert_eq!(one_element_adapters(&out.source), 1, "{}", out.source);
    assert!(
        flat.contains("StoreH5(core::slice::from_ref(buf),63,7)"),
        "the one adapter is shape (i)'s, at the thin caller\n{}",
        out.source
    );
    assert!(
        flat.contains("fnStoreH5(mutdata:&[u8]"),
        "the placed caller keeps its slice\n{}",
        out.source
    );
    assert!(
        flat.contains("HashBytesH5((&(data)[(ix&mask)..])")
            || flat.contains("HashBytesH5((&(data)[(ix&mask)..]).as_ptr()"),
        "the element address renders as the root's tail view\n{}",
        out.source
    );
}
