#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn g23_probe(p: *mut i32) -> i32 {
    if p.is_null() { 0 } else { *p }
}
pub fn g23_caller() -> i32 {
    let mut x: i32 = 7;
    unsafe { g23_probe(&mut x) }
}
