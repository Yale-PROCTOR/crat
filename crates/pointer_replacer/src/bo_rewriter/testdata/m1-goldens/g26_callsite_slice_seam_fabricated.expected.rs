#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn g26_sum(buf: &[i32]) -> i32 {
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < 4 {
        s += buf[i];
        i += 1;
    }
    s
}
pub unsafe fn g26_caller(data: *mut i32) -> i32 {
    let t = g26_sum(core::slice::from_raw_parts(
        data,
        crate::FALLBACK_SLICE_EXTENT,
    ));
    *data = t;
    t
}

const FALLBACK_SLICE_EXTENT: usize = 1024;
