#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn g24_total(buf: *mut i32, n: usize) -> i32 {
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < n {
        s += *buf.offset(i as isize);
        i += 1;
    }
    s
}
pub fn g24_caller() -> i32 {
    let mut x: i32 = 3;
    unsafe { g24_total(&mut x, 1) }
}
