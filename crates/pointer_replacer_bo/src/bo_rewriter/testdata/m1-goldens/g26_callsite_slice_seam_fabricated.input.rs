#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn g26_sum(buf: *mut i32) -> i32 {
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < 4 {
        s += *buf.offset(i as isize);
        i += 1;
    }
    s
}
pub unsafe fn g26_caller(data: *mut i32) -> i32 {
    let t = g26_sum(data);
    *data = t;
    t
}
