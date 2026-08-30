#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub struct G22Node {
    pub key: i32,
}
pub unsafe fn g22_probe(n: Option<&G22Node>) -> i32 {
    if n.is_none() {
        return 0;
    }
    (*n.unwrap()).key
}
pub unsafe fn g22_caller(node: *mut G22Node) -> *mut G22Node {
    let _b = g22_probe({
        let __crat_call_adapter_ptr = node;
        if __crat_call_adapter_ptr.is_null() {
            None
        } else {
            Some(&*__crat_call_adapter_ptr)
        }
    });
    node
}
