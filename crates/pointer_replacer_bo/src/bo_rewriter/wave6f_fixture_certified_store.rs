// w6f-certified-store-frame
#![allow(dead_code, unused_mut, unused_unsafe, non_camel_case_types, unused_variables, unused_assignments)]
extern "C" {
    fn malloc(_: u64) -> *mut ::std::ffi::c_void;
    fn free(_: *mut ::std::ffi::c_void);
}
#[repr(C)]
pub struct item {
    pub v: i32,
}
#[repr(C)]
pub struct holder {
    pub item: *mut item,
}
pub unsafe extern "C" fn make_item(mut v: i32) -> *mut item {
    let mut p: *mut item = malloc(::std::mem::size_of::<item>() as u64) as *mut item;
    (*p).v = v;
    return p;
}
pub unsafe extern "C" fn attach(mut h: *mut holder, mut v: i32) {
    (*h).item = make_item(v);
}
pub unsafe extern "C" fn value(mut h: *mut holder) -> i32 {
    return (*(*h).item).v;
}
pub unsafe extern "C" fn release(mut h: *mut holder) {
    free((*h).item as *mut ::std::ffi::c_void);
    (*h).item = 0 as *mut item;
}
