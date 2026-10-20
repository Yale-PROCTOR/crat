#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type Int32 = std::os::raw::c_int;
pub type UChar = std::os::raw::c_uchar;
// The four DState fields the call reads (c2rust-lib.rs:5199-5202); the rest of DState is not read.
#[repr(C)]
pub struct DState { pub len: [[UChar; 258]; 6], pub limit: [[Int32; 258]; 6], pub base: [[Int32; 258]; 6], pub perm: [[Int32; 258]; 6] }
pub unsafe extern "C" fn BZ2_hbCreateDecodeTables(mut limit: *mut Int32,
    mut base: *mut Int32, mut perm: *mut Int32, mut length: *mut UChar,
    mut minLen: Int32, mut maxLen: Int32, mut alphaSize: Int32) {
    let mut pp: Int32 = 0;
    let mut i: Int32 = 0;
    let mut j: Int32 = 0;
    let mut vec: Int32 = 0;
    pp = 0 as std::os::raw::c_int;
    i = minLen;
    while i <= maxLen {
        j = 0 as std::os::raw::c_int;
        while j < alphaSize {
            if *length.offset(j as isize) as std::os::raw::c_int == i {
                *perm.offset(pp as isize) = j;
                pp += 1
            }
            j += 1
        }
        i += 1
    }
    i = 0 as std::os::raw::c_int;
    while i < 23 as std::os::raw::c_int {
        *base.offset(i as isize) = 0 as std::os::raw::c_int;
        i += 1
    }
    i = 0 as std::os::raw::c_int;
    while i < alphaSize {
        *base.offset((*length.offset(i as isize) as std::os::raw::c_int +
                                1 as std::os::raw::c_int) as isize) += 1;
        i += 1
    }
    i = 1 as std::os::raw::c_int;
    while i < 23 as std::os::raw::c_int {
        *base.offset(i as isize) +=
            *base.offset((i - 1 as std::os::raw::c_int) as isize);
        i += 1
    }
    i = 0 as std::os::raw::c_int;
    while i < 23 as std::os::raw::c_int {
        *limit.offset(i as isize) = 0 as std::os::raw::c_int;
        i += 1
    }
    vec = 0 as std::os::raw::c_int;
    i = minLen;
    while i <= maxLen {
        vec +=
            *base.offset((i + 1 as std::os::raw::c_int) as isize) -
                *base.offset(i as isize);
        *limit.offset(i as isize) = vec - 1 as std::os::raw::c_int;
        vec <<= 1 as std::os::raw::c_int;
        i += 1
    }
    i = minLen + 1 as std::os::raw::c_int;
    while i <= maxLen {
        *base.offset(i as isize) =
            ((*limit.offset((i - 1 as std::os::raw::c_int) as isize) +
                                1 as std::os::raw::c_int) << 1 as std::os::raw::c_int) -
                *base.offset(i as isize);
        i += 1
    };
}
// The call, verbatim from BZ2_decompress (c2rust-lib.rs:12562-12574).
pub unsafe extern "C" fn decode_tables(mut s: *mut DState, mut t: Int32, mut minLen: Int32, mut maxLen: Int32, mut alphaSize: Int32) {
    BZ2_hbCreateDecodeTables(&mut *(*(*s).limit.as_mut_ptr().offset(t
                                        as
                                        isize)).as_mut_ptr().offset(0 as std::os::raw::c_int as
                        isize),
        &mut *(*(*s).base.as_mut_ptr().offset(t as
                                        isize)).as_mut_ptr().offset(0 as std::os::raw::c_int as
                        isize),
        &mut *(*(*s).perm.as_mut_ptr().offset(t as
                                        isize)).as_mut_ptr().offset(0 as std::os::raw::c_int as
                        isize),
        &mut *(*(*s).len.as_mut_ptr().offset(t as
                                        isize)).as_mut_ptr().offset(0 as std::os::raw::c_int as
                        isize), minLen, maxLen, alphaSize);
}
