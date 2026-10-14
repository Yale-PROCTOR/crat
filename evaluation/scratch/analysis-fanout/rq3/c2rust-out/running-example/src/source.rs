extern "C" {
    fn malloc(__size: size_t) -> *mut ::core::ffi::c_void;
}
pub type size_t = usize;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct node_t {
    pub data: ::core::ffi::c_int,
    pub next: *mut node_t,
}
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<
    ::core::ffi::c_void,
>();
#[no_mangle]
pub unsafe extern "C" fn new() -> *mut node_t {
    let mut n = malloc(::core::mem::size_of::<node_t>() as size_t) as *mut node_t;
    (*n).next = ::core::ptr::null_mut::<node_t>();
    return n;
}
#[no_mangle]
pub unsafe extern "C" fn push(mut list: *mut node_t, mut x: ::core::ffi::c_int) {
    let mut n = malloc(::core::mem::size_of::<node_t>() as size_t) as *mut node_t;
    (*n).data = x;
    (*n).next = (*list).next;
    (*list).next = n;
}
#[no_mangle]
pub unsafe extern "C" fn replace(
    mut dst: *mut ::core::ffi::c_int,
    mut x: ::core::ffi::c_int,
) {
    *dst = x;
}
#[no_mangle]
pub unsafe extern "C" fn replace_first(
    mut list: *mut node_t,
    mut x: ::core::ffi::c_int,
) {
    replace(&raw mut (*(*list).next).data, x);
}
#[no_mangle]
pub unsafe extern "C" fn first(mut list: *mut node_t) -> ::core::ffi::c_int {
    return (*(*list).next).data;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    let mut list = new();
    push(list, 1 as ::core::ffi::c_int);
    let mut sublist = (*list).next;
    push(sublist, 2 as ::core::ffi::c_int);
    replace_first(list, 3 as ::core::ffi::c_int);
    replace_first(sublist, 4 as ::core::ffi::c_int);
    return 0;
}
pub fn main() {
    unsafe { ::std::process::exit(main_0() as i32) }
}
