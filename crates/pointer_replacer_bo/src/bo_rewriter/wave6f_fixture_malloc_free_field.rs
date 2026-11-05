// w6f-malloc-free-field-frame
//! The commonest owned-field idiom in C, reduced: a field allocated from
//! `malloc`, NULL-tested, and released with `free(s->buf)`. Every site is a
//! STORE of a call result, a NULL test or a CAST into the deallocator — none of
//! them `Load` / `CallArgument` / `Assignment` / a Subject rhs, and no
//! function stores a parameter into the field. Relay 064: is such a
//! transaction's `dependent_owners` EMPTY (defect B of report 059 reachable),
//! or merely representable?
#![allow(dead_code, non_camel_case_types, non_snake_case, unused_mut, unused_unsafe)]

extern "C" {
    fn malloc(_: u64) -> *mut std::ffi::c_void;
    fn free(_: *mut std::ffi::c_void);
}

#[repr(C)]
pub struct holder {
    pub buf: *mut u8,
    pub len: u64,
}

pub unsafe extern "C" fn holder_init(mut s: *mut holder) -> i32 {
    (*s).buf = malloc(8) as *mut u8;
    if ((*s).buf).is_null() {
        return -1;
    }
    (*s).len = 8;
    return 0;
}

pub unsafe extern "C" fn holder_fini(mut s: *mut holder) {
    free((*s).buf as *mut std::ffi::c_void);
}
