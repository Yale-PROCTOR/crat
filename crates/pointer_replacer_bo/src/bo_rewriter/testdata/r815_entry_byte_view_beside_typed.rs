#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
// R815-6: binn's `binn_object_blob` shape. An exported entry with no caller in
// the program hands on, bare, a byte formal (`key`) beside a typed one
// (`psize`); under P8 the two are views of different outside objects.
#[repr(C)]
pub struct binn {
    pub header: i32,
    pub type_0: i32,
    pub size: i32,
    pub ptr: *mut core::ffi::c_void,
}
unsafe fn search_for_key(mut p: *mut u8, mut key: *const i8) -> *mut u8 {
    let mut i: isize = 0;
    while *key.offset(i) != 0 {
        if *p.offset(i) as i8 != *key.offset(i) {
            return 0 as *mut u8;
        }
        i += 1;
    }
    p.offset(i)
}
unsafe fn get_value(mut p: *mut u8, mut value: *mut binn) -> i32 {
    (*value).type_0 = *p as i32;
    (*value).size = *p.offset(1) as i32;
    (*value).ptr = p.offset(2) as *mut core::ffi::c_void;
    1
}
unsafe fn object_get_value(mut ptr: *mut core::ffi::c_void, mut key: *const i8, mut value: *mut binn) -> i32 {
    if ptr.is_null() || key.is_null() || value.is_null() {
        return 0;
    }
    let mut p = search_for_key(ptr as *mut u8, key);
    if p.is_null() {
        return 0;
    }
    get_value(p, value)
}
#[no_mangle]
pub unsafe extern "C" fn binn_object_get(
    mut ptr: *mut core::ffi::c_void,
    mut key: *const i8,
    mut type_0: i32,
    mut pvalue: *mut core::ffi::c_void,
    mut psize: *mut i32,
) -> i32 {
    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if object_get_value(ptr, key, &mut value) == 0 {
        return 0;
    }
    *(pvalue as *mut *mut core::ffi::c_void) = value.ptr;
    if !psize.is_null() {
        *psize = value.size;
    }
    1
}
#[no_mangle]
pub unsafe extern "C" fn binn_object_blob(
    mut obj: *mut core::ffi::c_void,
    mut key: *const i8,
    mut psize: *mut i32,
) -> *mut core::ffi::c_void {
    let mut value = 0 as *mut core::ffi::c_void;
    binn_object_get(obj, key, 0xc0, &mut value as *mut *mut core::ffi::c_void as *mut core::ffi::c_void, psize);
    value
}
#[no_mangle]
pub unsafe extern "C" fn binn_object_int32(mut obj: *mut core::ffi::c_void, mut key: *const i8) -> i32 {
    let mut value: i32 = 0;
    binn_object_get(obj, key, 0x61, &mut value as *mut i32 as *mut core::ffi::c_void, 0 as *mut i32);
    value
}
