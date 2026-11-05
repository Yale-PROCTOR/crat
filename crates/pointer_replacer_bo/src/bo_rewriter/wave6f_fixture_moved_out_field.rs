// w6f-moved-out-field-frame
// R456-5: ownership-fields 041 §3's `Holder.buf` fixture, verbatim as their
// dry14 candidate dump spells the INPUT. The field's value is moved OUT into
// a local, the field is nulled, and the local is freed — the moved-out load,
// which is the shape every avl / bst / quadtree node field becomes once the
// model settles it Owning.
#![allow(
    dead_code,
    unused_mut,
    unused_unsafe,
    unused_assignments,
    unused_variables,
    non_camel_case_types,
    non_snake_case
)]
extern "C" {
    fn malloc(_: u64) -> *mut std::ffi::c_void;
    fn free(_: *mut std::ffi::c_void);
}
#[repr(C)]
pub struct Holder {
    pub buf: *mut u8,
    pub len: i32,
}
#[no_mangle]
pub unsafe extern "C" fn run() {
    let mut h = malloc(::std::mem::size_of::<Holder>() as u64) as *mut Holder;
    (*h).buf = malloc(64 as u64) as *mut u8;
    (*h).len = 64 as i32;
    let mut b = (*h).buf;
    (*h).buf = 0 as *mut u8;
    free(b as *mut std::ffi::c_void);
    free(h as *mut std::ffi::c_void);
}
