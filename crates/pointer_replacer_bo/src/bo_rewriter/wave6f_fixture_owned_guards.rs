// w6f-owned-guards-frame
#![allow(dead_code, unused_mut, unused_unsafe, non_camel_case_types, unused_variables, unused_assignments)]
extern "C" {
    fn malloc(_: u64) -> *mut std::ffi::c_void;
    fn free(_: *mut std::ffi::c_void);
}
#[repr(C)]
pub struct Common {
    pub extra: i32,
}
#[repr(C)]
pub struct Hx {
    pub n: i32,
    pub common: *mut Common,
}
#[repr(C)]
pub struct Outer {
    pub common: Common,
    pub inner: Hx,
}
impl ::core::marker::Copy for Common {}
impl ::core::clone::Clone for Common {
    fn clone(&self) -> Common {
        *self
    }
}
impl ::core::marker::Copy for Hx {}
impl ::core::clone::Clone for Hx {
    fn clone(&self) -> Hx {
        *self
    }
}
pub unsafe extern "C" fn initialize(mut common: *mut Common, mut self_0: *mut Hx) {
    (*self_0).n = 1;
    (*self_0).common = common;
}
pub unsafe extern "C" fn setup(mut o: *mut Outer) {
    initialize(malloc(::std::mem::size_of::<Common>() as u64) as *mut Common, &mut (*o).inner);
}
pub unsafe extern "C" fn release(mut self_0: *mut Hx) {
    free((*self_0).common as *mut std::ffi::c_void);
}
