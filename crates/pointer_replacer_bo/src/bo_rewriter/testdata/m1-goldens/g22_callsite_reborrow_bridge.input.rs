#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub struct G22Node {
    pub key: i32,
}
pub unsafe fn g22_probe(n: *mut G22Node) -> i32 {
    if n.is_null() {
        return 0;
    }
    (*n).key
}
pub unsafe fn g22_caller(node: *mut G22Node) -> *mut G22Node {
    let _b = g22_probe(node);
    node
}
