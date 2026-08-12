#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn g23_probe(p: Option<&i32>) -> i32 {
    if p.is_none() { 0 } else { *p.unwrap() }
}
pub fn g23_caller() -> i32 {
    let mut x: i32 = 7;
    unsafe { g23_probe(Some(&mut x)) }
}
