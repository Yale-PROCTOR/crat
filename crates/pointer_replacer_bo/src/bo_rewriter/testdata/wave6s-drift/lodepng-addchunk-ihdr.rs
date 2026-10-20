#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_uchar = u8; pub type c_uint = u32; pub type c_int = i32; pub type c_ulong = u64; pub type c_char = i8; pub type c_void = core::ffi::c_void; pub type size_t = u64; }
pub type size_t = libc::c_ulong;
pub type LodePNGColorType = libc::c_uint;
unsafe extern "C" { fn realloc(p: *mut libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; fn memcpy(d: *mut libc::c_void, s: *const libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; }
#[derive(Copy, Clone)]
#[repr(C)]
        pub struct ucvector {
            pub data: *mut libc::c_uchar,
            pub size: size_t,
            pub allocsize: size_t,
        }
static mut lodepng_crc32_table: [libc::c_uint; 256] = [0; 256];
        unsafe extern "C" fn lodepng_realloc(mut ptr: *mut libc::c_void,
            mut new_size: size_t) -> *mut libc::c_void {
            return realloc(ptr, new_size);
        }
        unsafe extern "C" fn lodepng_memcpy(mut dst: *mut libc::c_void,
            mut src: *const libc::c_void, mut size: size_t) {
            let mut i: size_t = 0;
            i = 0 as libc::c_int as size_t;
            while i < size {
                *(dst as *mut libc::c_char).offset(i as isize) =
                    *(src as *const libc::c_char).offset(i as isize);
                i = i.wrapping_add(1);
            }
        }
        unsafe extern "C" fn lodepng_addofl(mut a: size_t, mut b: size_t,
            mut result: *mut size_t) -> libc::c_int {
            *result = a.wrapping_add(b);
            return (*result < a) as libc::c_int;
        }
        unsafe extern "C" fn ucvector_reserve(mut p: *mut ucvector,
            mut size: size_t) -> libc::c_uint {
            if size > (*p).allocsize {
                let mut newsize =
                    size.wrapping_add((*p).allocsize >> 1 as libc::c_uint);
                let mut data =
                    lodepng_realloc((*p).data as *mut libc::c_void, newsize);
                if !data.is_null() {
                    (*p).allocsize = newsize;
                    (*p).data = data as *mut libc::c_uchar;
                } else { return 0 as libc::c_int as libc::c_uint }
            }
            return 1 as libc::c_int as libc::c_uint;
        }
        unsafe extern "C" fn ucvector_resize(mut p: *mut ucvector,
            mut size: size_t) -> libc::c_uint {
            (*p).size = size;
            return ucvector_reserve(p, size);
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
        unsafe extern "C" fn lodepng_set32bitInt(mut buffer:
                *mut libc::c_uchar, mut value: libc::c_uint) {
            *buffer.offset(0 as libc::c_int as isize) =
                (value >> 24 as libc::c_int &
                            0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
            *buffer.offset(1 as libc::c_int as isize) =
                (value >> 16 as libc::c_int &
                            0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
            *buffer.offset(2 as libc::c_int as isize) =
                (value >> 8 as libc::c_int &
                            0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
            *buffer.offset(3 as libc::c_int as isize) =
                (value & 0xff as libc::c_int as libc::c_uint) as
                    libc::c_uchar;
        }
        pub unsafe extern "C" fn lodepng_crc32(mut data: *const libc::c_uchar,
            mut length: size_t) -> libc::c_uint {
            let mut r = 0xffffffff as libc::c_uint;
            let mut i: size_t = 0;
            i = 0 as libc::c_int as size_t;
            while i < length {
                r =
                    lodepng_crc32_table[((r ^
                                                *data.offset(i as isize) as libc::c_uint) &
                                        0xff as libc::c_uint) as usize] ^ r >> 8 as libc::c_uint;
                i = i.wrapping_add(1);
            }
            return r ^ 0xffffffff as libc::c_uint;
        }
        pub unsafe extern "C" fn lodepng_chunk_length(mut chunk:
                *const libc::c_uchar) -> libc::c_uint {
            return lodepng_read32bitInt(chunk);
        }
        pub unsafe extern "C" fn lodepng_chunk_generate_crc(mut chunk:
                *mut libc::c_uchar) {
            let mut length = lodepng_chunk_length(chunk);
            let mut CRC =
                lodepng_crc32(&mut *chunk.offset(4 as libc::c_int as isize),
                    length.wrapping_add(4 as libc::c_int as libc::c_uint) as
                        size_t);
            lodepng_set32bitInt(chunk.offset((8 as libc::c_int as isize) +
                        (length as isize)), CRC);
        }
        unsafe extern "C" fn lodepng_chunk_init(mut chunk:
                *mut *mut libc::c_uchar, mut out: *mut ucvector,
            mut length: libc::c_uint, mut type_0: *const libc::c_char)
            -> libc::c_uint {
            let mut new_length = (*out).size;
            if lodepng_addofl(new_length, length as size_t, &mut new_length)
                    != 0 {
                return 77 as libc::c_int as libc::c_uint;
            }
            if lodepng_addofl(new_length, 12 as libc::c_int as size_t,
                        &mut new_length) != 0 {
                return 77 as libc::c_int as libc::c_uint;
            }
            if ucvector_resize(out, new_length) == 0 {
                return 83 as libc::c_int as libc::c_uint;
            }
            *chunk =
                ((*out).data).offset(((new_length as isize) +
                                (-(length as isize))) + (-(12 as libc::c_uint as isize)));
            lodepng_set32bitInt(*chunk, length);
            lodepng_memcpy((*chunk).offset(4 as libc::c_int as isize) as
                    *mut libc::c_void, type_0 as *const libc::c_void,
                4 as libc::c_int as size_t);
            return 0 as libc::c_int as libc::c_uint;
        }
        unsafe extern "C" fn addChunk_IHDR(mut out: *mut ucvector,
            mut w: libc::c_uint, mut h: libc::c_uint,
            mut colortype: LodePNGColorType, mut bitdepth: libc::c_uint,
            mut interlace_method: libc::c_uint) -> libc::c_uint {
            let mut chunk = 0 as *mut libc::c_uchar;
            let mut data = 0 as *mut libc::c_uchar;
            let mut error =
                lodepng_chunk_init(&mut chunk, out,
                    13 as libc::c_int as libc::c_uint,
                    b"IHDR\0" as *const u8 as *const libc::c_char);
            if error != 0 { return error; }
            data = chunk.offset(8 as libc::c_int as isize);
            lodepng_set32bitInt(data.offset(0 as libc::c_int as isize), w);
            lodepng_set32bitInt(data.offset(4 as libc::c_int as isize), h);
            *data.offset(8 as libc::c_int as isize) =
                bitdepth as libc::c_uchar;
            *data.offset(9 as libc::c_int as isize) =
                colortype as libc::c_uchar;
            *data.offset(10 as libc::c_int as isize) =
                0 as libc::c_int as libc::c_uchar;
            *data.offset(11 as libc::c_int as isize) =
                0 as libc::c_int as libc::c_uchar;
            *data.offset(12 as libc::c_int as isize) =
                interlace_method as libc::c_uchar;
            lodepng_chunk_generate_crc(chunk);
            return 0 as libc::c_int as libc::c_uint;
        }
