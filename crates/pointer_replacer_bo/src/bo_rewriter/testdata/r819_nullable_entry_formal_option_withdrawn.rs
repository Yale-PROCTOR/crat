#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, static_mut_refs)]
// R819-1 item 1: binn's `binn_map_pair::pid` shape. An exported entry hands its
// formal `pid` to a callee that null-tests it, so `pid` carries nullability;
// the callee's class is held (a converted argument bridged into a retaining
// raw formal), so the entry's Option stage is withdrawn.
pub static mut KEPT: *mut i32 = 0 as *mut i32;
unsafe fn keep(mut p: *mut i32) {
    KEPT = p;
}
unsafe fn read_pair(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut pid: *mut i32) -> i32 {
    if ptr.is_null() {
        return 0;
    }
    if !pid.is_null() {
        *pid = pos;
        keep(pid);
    }
    1
}
#[no_mangle]
pub unsafe extern "C" fn map_pair(mut map: *mut core::ffi::c_void, mut pos: i32, mut pid: *mut i32) -> i32 {
    read_pair(map, pos, pid)
}
