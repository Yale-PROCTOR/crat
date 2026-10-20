#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_uchar = u8; pub type c_uint = u32; pub type c_int = i32; pub type c_ulong = u64; pub type c_char = i8; pub type c_void = core::ffi::c_void; }
pub type size_t = libc::c_ulong;
unsafe extern "C" { fn realloc(p: *mut libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; }
        unsafe extern "C" fn lodepng_realloc(mut ptr: *mut libc::c_void,
            mut new_size: size_t) -> *mut libc::c_void {
            return realloc(ptr, new_size);
        }
        unsafe extern "C" fn lodepng_addofl(mut a: size_t, mut b: size_t,
            mut result: *mut size_t) -> libc::c_int {
            *result = a.wrapping_add(b);
            return (*result < a) as libc::c_int;
        }
        unsafe extern "C" fn lodepng_read32bitInt(mut buffer:
                *const libc::c_uchar) -> libc::c_uint {
            return (*buffer.offset(0 as libc::c_int as isize) as libc::c_uint)
                                << 24 as libc::c_uint |
                            (*buffer.offset(1 as libc::c_int as isize) as libc::c_uint)
                                << 16 as libc::c_uint |
                        (*buffer.offset(2 as libc::c_int as isize) as libc::c_uint)
                            << 8 as libc::c_uint |
                    *buffer.offset(3 as libc::c_int as isize) as libc::c_uint;
        }
        pub unsafe extern "C" fn lodepng_chunk_length(mut chunk:
                *const libc::c_uchar) -> libc::c_uint {
            return lodepng_read32bitInt(chunk);
        }
        pub unsafe extern "C" fn lodepng_chunk_append(mut out:
                *mut *mut libc::c_uchar, mut outsize: *mut size_t,
            mut chunk: *const libc::c_uchar) -> libc::c_uint {
            let mut i: libc::c_uint = 0;
            let mut total_chunk_length: size_t = 0;
            let mut new_length: size_t = 0;
            let mut chunk_start = 0 as *mut libc::c_uchar;
            let mut new_buffer = 0 as *mut libc::c_uchar;
            if lodepng_addofl(lodepng_chunk_length(chunk) as size_t,
                        12 as libc::c_int as size_t, &mut total_chunk_length) != 0 {
                return 77 as libc::c_int as libc::c_uint;
            }
            if lodepng_addofl(*outsize, total_chunk_length, &mut new_length)
                    != 0 {
                return 77 as libc::c_int as libc::c_uint;
            }
            new_buffer =
                lodepng_realloc(*out as *mut libc::c_void, new_length) as
                    *mut libc::c_uchar;
            if new_buffer.is_null() {
                return 83 as libc::c_int as libc::c_uint;
            }
            *out = new_buffer;
            *outsize = new_length;
            chunk_start =
                &mut *(*out).offset(new_length.wrapping_sub(total_chunk_length)
                                    as isize) as *mut libc::c_uchar;
            i = 0 as libc::c_int as libc::c_uint;
            while i as libc::c_ulong != total_chunk_length {
                *chunk_start.offset(i as isize) = *chunk.offset(i as isize);
                i = i.wrapping_add(1);
            }
            return 0 as libc::c_int as libc::c_uint;
        }
