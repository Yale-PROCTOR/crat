#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn g25_total(buf: &[i32], n: usize) -> i32 {
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < n {
        s += buf[i];
        i += 1;
    }
    s
}
pub unsafe fn g25_caller(data: *mut i32, n: usize) -> i32 {
    let t = g25_total(core::slice::from_raw_parts(data, (n) as usize), n);
    *data = t;
    t
}
