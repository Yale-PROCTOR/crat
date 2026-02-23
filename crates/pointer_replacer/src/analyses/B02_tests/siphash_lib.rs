use super::run_ownership_case_with_box_candidates;

const SOURCE: &str = r####"
#![warn(mutable_transmutes)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(c_variadic)]
#![feature(extern_types)]
#![feature(linkage)]
#![feature(rustc_private)]
#![feature(thread_local)]
#![feature(builtin_syntax)]
#![feature(core_intrinsics)]
#![feature(derive_clone_copy)]
#![feature(hint_must_use)]
#![feature(panic_internals)]
pub mod src {
    pub mod lib {
        extern "C" {
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        unsafe extern "C" fn stbds_siphash_bytes(
            p: *mut core::ffi::c_void,
            len: size_t,
            seed: size_t,
        ) -> size_t {
            let mut d: *mut core::ffi::c_uchar = p as *mut core::ffi::c_uchar;
            let mut i: size_t = 0;
            let mut j: size_t = 0;
            let mut v0: size_t = 0;
            let mut v1: size_t = 0;
            let mut v2: size_t = 0;
            let mut v3: size_t = 0;
            let mut data: size_t = 0;
            v0 = (((0x736f6d65 as core::ffi::c_int as size_t) << 16 as core::ffi::c_int)
                << 16 as core::ffi::c_int)
                .wrapping_add(0x70736575 as size_t)
                ^ seed;
            v1 = (((0x646f7261 as core::ffi::c_int as size_t) << 16 as core::ffi::c_int)
                << 16 as core::ffi::c_int)
                .wrapping_add(0x6e646f6d as size_t)
                ^ !seed;
            v2 = (((0x6c796765 as core::ffi::c_int as size_t) << 16 as core::ffi::c_int)
                << 16 as core::ffi::c_int)
                .wrapping_add(0x6e657261 as size_t)
                ^ seed;
            v3 = (((0x74656462 as core::ffi::c_int as size_t) << 16 as core::ffi::c_int)
                << 16 as core::ffi::c_int)
                .wrapping_add(0x79746573 as size_t)
                ^ !seed;
            v0 = (v0 as core::ffi::c_ulonglong
                ^ (0x706050403020100 as core::ffi::c_ulonglong ^ seed as core::ffi::c_ulonglong))
                as size_t;
            v1 = (v1 as core::ffi::c_ulonglong
                ^ (0xf0e0d0c0b0a0908 as core::ffi::c_ulonglong ^ !seed as core::ffi::c_ulonglong))
                as size_t;
            v2 = (v2 as core::ffi::c_ulonglong
                ^ (0x706050403020100 as core::ffi::c_ulonglong ^ seed as core::ffi::c_ulonglong))
                as size_t;
            v3 = (v3 as core::ffi::c_ulonglong
                ^ (0xf0e0d0c0b0a0908 as core::ffi::c_ulonglong ^ !seed as core::ffi::c_ulonglong))
                as size_t;
            i = 0 as size_t;
            while i.wrapping_add(::core::mem::size_of::<size_t>() as size_t) <= len {
                data = (*d.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    | (*d.offset(1 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 8 as core::ffi::c_int
                    | (*d.offset(2 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 16 as core::ffi::c_int
                    | (*d.offset(3 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 24 as core::ffi::c_int) as size_t;
                data = (data as core::ffi::c_ulong
                    | ((((*d.offset(4 as core::ffi::c_int as isize) as core::ffi::c_int
                        | (*d.offset(5 as core::ffi::c_int as isize) as core::ffi::c_int)
                            << 8 as core::ffi::c_int
                        | (*d.offset(6 as core::ffi::c_int as isize) as core::ffi::c_int)
                            << 16 as core::ffi::c_int
                        | (*d.offset(7 as core::ffi::c_int as isize) as core::ffi::c_int)
                            << 24 as core::ffi::c_int) as size_t)
                        << 16 as core::ffi::c_int)
                        << 16 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                v3 = (v3 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
                j = 0 as size_t;
                while j < 2 as size_t {
                    v0 = (v0 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v1 = v1 << 13 as core::ffi::c_int
                        | v1 >> ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_sub(13_usize);
                    v1 = (v1 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                    v0 = v0
                        << ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize)
                        | v0 >> ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_sub(
                                ::core::mem::size_of::<size_t>()
                                    .wrapping_mul(8_usize)
                                    .wrapping_div(2_usize),
                            );
                    v2 = (v2 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v3 = v3 << 16 as core::ffi::c_int
                        | v3 >> ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_sub(16_usize);
                    v3 = (v3 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                    v2 = (v2 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v1 = v1 << 17 as core::ffi::c_int
                        | v1 >> ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_sub(17_usize);
                    v1 = (v1 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                    v2 = v2
                        << ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize)
                        | v2 >> ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_sub(
                                ::core::mem::size_of::<size_t>()
                                    .wrapping_mul(8_usize)
                                    .wrapping_div(2_usize),
                            );
                    v0 = (v0 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v3 = v3 << 21 as core::ffi::c_int
                        | v3 >> ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_sub(21_usize);
                    v3 = (v3 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                    j = j.wrapping_add(1);
                }
                v0 = (v0 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
                i = (i as core::ffi::c_ulong)
                    .wrapping_add(::core::mem::size_of::<size_t>() as core::ffi::c_ulong)
                    as size_t as size_t;
                d = d.add(::core::mem::size_of::<size_t>());
            }
            data = len
                << ::core::mem::size_of::<size_t>()
                    .wrapping_mul(8_usize)
                    .wrapping_sub(8_usize);
            let mut current_block_40: u64;
            match len.wrapping_sub(i) {
                7 => {
                    data = (data as core::ffi::c_ulong
                        | (((*d.offset(6 as core::ffi::c_int as isize) as size_t)
                            << 24 as core::ffi::c_int)
                            << 24 as core::ffi::c_int)
                            as core::ffi::c_ulong) as size_t;
                    current_block_40 = 8692974689919092981;
                }
                6 => {
                    current_block_40 = 8692974689919092981;
                }
                5 => {
                    current_block_40 = 4357973157024227926;
                }
                4 => {
                    current_block_40 = 11664208733866486349;
                }
                3 => {
                    current_block_40 = 10904306681241078270;
                }
                2 => {
                    current_block_40 = 110281293587075479;
                }
                1 => {
                    current_block_40 = 2555238947937434026;
                }
                0 | _ => {
                    current_block_40 = 1538046216550696469;
                }
            }
            if current_block_40 == 8692974689919092981 {
                data = (data as core::ffi::c_ulong
                    | (((*d.offset(5 as core::ffi::c_int as isize) as size_t)
                        << 20 as core::ffi::c_int)
                        << 20 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 4357973157024227926;
            }
            if current_block_40 == 4357973157024227926 {
                data = (data as core::ffi::c_ulong
                    | (((*d.offset(4 as core::ffi::c_int as isize) as size_t)
                        << 16 as core::ffi::c_int)
                        << 16 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 11664208733866486349;
            }
            if current_block_40 == 11664208733866486349 {
                data = (data as core::ffi::c_ulong
                    | ((*d.offset(3 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 24 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 10904306681241078270;
            }
            if current_block_40 == 10904306681241078270 {
                data = (data as core::ffi::c_ulong
                    | ((*d.offset(2 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 16 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 110281293587075479;
            }
            if current_block_40 == 110281293587075479 {
                data = (data as core::ffi::c_ulong
                    | ((*d.offset(1 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 8 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 2555238947937434026;
            }
            if current_block_40 == 2555238947937434026 {
                data = (data as core::ffi::c_ulong
                    | *d.offset(0 as core::ffi::c_int as isize) as core::ffi::c_ulong)
                    as size_t;
            }
            v3 = (v3 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
            j = 0 as size_t;
            while j < 2 as size_t {
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 13 as core::ffi::c_int
                    | v1 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(13_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                v0 = v0
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v0 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(
                            ::core::mem::size_of::<size_t>()
                                .wrapping_mul(8_usize)
                                .wrapping_div(2_usize),
                        );
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 16 as core::ffi::c_int
                    | v3 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(16_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 17 as core::ffi::c_int
                    | v1 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(17_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = v2
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v2 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(
                            ::core::mem::size_of::<size_t>()
                                .wrapping_mul(8_usize)
                                .wrapping_div(2_usize),
                        );
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 21 as core::ffi::c_int
                    | v3 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(21_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                j = j.wrapping_add(1);
            }
            v0 = (v0 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
            v2 = (v2 as core::ffi::c_ulong ^ 0xff as core::ffi::c_ulong) as size_t;
            j = 0 as size_t;
            while j < 4 as size_t {
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 13 as core::ffi::c_int
                    | v1 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(13_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                v0 = v0
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v0 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(
                            ::core::mem::size_of::<size_t>()
                                .wrapping_mul(8_usize)
                                .wrapping_div(2_usize),
                        );
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 16 as core::ffi::c_int
                    | v3 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(16_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 17 as core::ffi::c_int
                    | v1 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(17_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = v2
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v2 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(
                            ::core::mem::size_of::<size_t>()
                                .wrapping_mul(8_usize)
                                .wrapping_div(2_usize),
                        );
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 21 as core::ffi::c_int
                    | v3 >> ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_sub(21_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                j = j.wrapping_add(1);
            }
            v0 ^ v1 ^ v2 ^ v3
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hash_bytes(
            p: *mut core::ffi::c_void,
            len: size_t,
            seed: size_t,
        ) -> size_t {
            stbds_siphash_bytes(p, len, seed)
        }
        #[no_mangle]
        pub unsafe extern "C" fn siphash(mut init: core::ffi::c_int) {
            let mut mem: [core::ffi::c_uchar; 64] = [0; 64];
            let mut i: core::ffi::c_int = 0;
            let mut j: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < 64 as core::ffi::c_int {
                mem[i as usize] = init as core::ffi::c_uchar;
                i += 1;
                init += 1;
            }
            i = 0 as core::ffi::c_int;
            while i < 64 as core::ffi::c_int {
                let hash: size_t = stbds_hash_bytes(
                    mem.as_mut_ptr() as *mut core::ffi::c_void,
                    i as size_t,
                    0 as size_t,
                );
                printf(b"  { \0" as *const u8 as *const core::ffi::c_char);
                j = 0 as core::ffi::c_int;
                while j < 8 as core::ffi::c_int {
                    printf(
                        b"0x%02x, \0" as *const u8 as *const core::ffi::c_char,
                        (hash >> (j * 8 as core::ffi::c_int) & 255 as size_t) as core::ffi::c_uchar
                            as core::ffi::c_int,
                    );
                    j += 1;
                }
                printf(b" },\n\0" as *const u8 as *const core::ffi::c_char);
                i += 1;
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("siphash_lib", SOURCE, &[], &[]);
}
