// w6f-owned-subfield-write-frame
//! wave-6a 077 §1, routed to wave-6f (R531-7): a WRITE through a delivered owned
//! field, one projection below the deref — `(*(*t).entries).key = 3` — rendered
//! `(*(*t).entries.as_deref().unwrap()).key = 3`, which is E0594 (assignment
//! through a `&` reference), and the whole program failed to emit. The deref's
//! parent is the `.key` projection, not the assignment, so a "written" test that
//! only asks whether the deref itself is the assignment's left side misses it.
//! Covers the plain assignment, a compound assignment one level down, and a read.
#![allow(dead_code, non_camel_case_types, non_snake_case, unused_mut, unused_unsafe)]

extern "C" {
    fn malloc(_: u64) -> *mut std::ffi::c_void;
    fn free(_: *mut std::ffi::c_void);
}

#[repr(C)]
pub struct entry {
    pub key: i32,
    pub value: i32,
}
#[automatically_derived]
impl ::core::marker::Copy for entry {}
#[automatically_derived]
impl ::core::clone::Clone for entry {
    #[inline]
    fn clone(&self) -> entry {
        *self
    }
}

#[repr(C)]
pub struct table {
    pub entries: *mut entry,
    pub length: u64,
}

pub unsafe extern "C" fn table_init(mut t: *mut table) -> i32 {
    (*t).entries = malloc(8) as *mut entry;
    if ((*t).entries).is_null() {
        return -1;
    }
    (*t).length = 1;
    return 0;
}

pub unsafe extern "C" fn table_set(mut t: *mut table) {
    (*(*t).entries).key = 3;
    (*(*t).entries).value += 1;
}

pub unsafe extern "C" fn table_get(mut t: *mut table) -> i32 {
    return (*(*t).entries).key;
}

pub unsafe extern "C" fn table_fini(mut t: *mut table) {
    free((*t).entries as *mut std::ffi::c_void);
}
