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
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn memmove(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn memcmp(
                __s1: *const core::ffi::c_void,
                __s2: *const core::ffi::c_void,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn __assert_fail(
                __assertion: *const core::ffi::c_char,
                __file: *const core::ffi::c_char,
                __line: core::ffi::c_uint,
                __function: *const core::ffi::c_char,
            ) -> !;
            fn sprintf(
                __s: *mut core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
        }
        #[repr(C)]
        pub struct stbds_array_header {
            pub length: size_t,
            pub capacity: size_t,
            pub hash_table: *mut core::ffi::c_void,
            pub temp: ptrdiff_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for stbds_array_header {}
        #[automatically_derived]
        impl ::core::clone::Clone for stbds_array_header {
            #[inline]
            fn clone(&self) -> stbds_array_header {
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<ptrdiff_t>;
                *self
            }
        }
        pub type ptrdiff_t = isize;
        pub type size_t = usize;
        #[repr(C)]
        pub struct stbds_string_arena {
            pub storage: *mut stbds_string_block,
            pub remaining: size_t,
            pub block: core::ffi::c_uchar,
            pub mode: core::ffi::c_uchar,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for stbds_string_arena {}
        #[automatically_derived]
        impl ::core::clone::Clone for stbds_string_arena {
            #[inline]
            fn clone(&self) -> stbds_string_arena {
                let _: ::core::clone::AssertParamIsClone<*mut stbds_string_block>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_uchar>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_uchar>;
                *self
            }
        }
        #[repr(C)]
        pub struct stbds_string_block {
            pub next: *mut stbds_string_block,
            pub storage: [core::ffi::c_char; 8],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for stbds_string_block {}
        #[automatically_derived]
        impl ::core::clone::Clone for stbds_string_block {
            #[inline]
            fn clone(&self) -> stbds_string_block {
                let _: ::core::clone::AssertParamIsClone<*mut stbds_string_block>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 8]>;
                *self
            }
        }
        #[repr(C)]
        pub struct stbds_hash_index {
            pub temp_key: *mut core::ffi::c_char,
            pub slot_count: size_t,
            pub used_count: size_t,
            pub used_count_threshold: size_t,
            pub used_count_shrink_threshold: size_t,
            pub tombstone_count: size_t,
            pub tombstone_count_threshold: size_t,
            pub seed: size_t,
            pub slot_count_log2: size_t,
            pub string: stbds_string_arena,
            pub storage: *mut stbds_hash_bucket,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for stbds_hash_index {}
        #[automatically_derived]
        impl ::core::clone::Clone for stbds_hash_index {
            #[inline]
            fn clone(&self) -> stbds_hash_index {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<stbds_string_arena>;
                let _: ::core::clone::AssertParamIsClone<*mut stbds_hash_bucket>;
                *self
            }
        }
        #[repr(C)]
        pub struct stbds_hash_bucket {
            pub hash: [size_t; 8],
            pub index: [ptrdiff_t; 8],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for stbds_hash_bucket {}
        #[automatically_derived]
        impl ::core::clone::Clone for stbds_hash_bucket {
            #[inline]
            fn clone(&self) -> stbds_hash_bucket {
                let _: ::core::clone::AssertParamIsClone<[size_t; 8]>;
                let _: ::core::clone::AssertParamIsClone<[ptrdiff_t; 8]>;
                *self
            }
        }
        pub const STBDS_SH_STRDUP: C2RustUnnamed = 2;
        pub const STBDS_SH_DEFAULT: C2RustUnnamed = 1;
        pub const STBDS_SH_ARENA: C2RustUnnamed = 3;
        pub type C2RustUnnamed = core::ffi::c_uint;
        pub const STBDS_SH_NONE: C2RustUnnamed = 0;
        pub const NULL_0: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const STBDS_HM_STRING: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const __ASSERT_FUNCTION: [core::ffi::c_char; 18] = [
            b'v' as i8,
            b'o' as i8,
            b'i' as i8,
            b'd' as i8,
            b' ' as i8,
            b'a' as i8,
            b'r' as i8,
            b'r' as i8,
            b'_' as i8,
            b'i' as i8,
            b'n' as i8,
            b's' as i8,
            b'(' as i8,
            b'i' as i8,
            b'n' as i8,
            b't' as i8,
            b')' as i8,
            b'\0' as i8,
        ];
        #[no_mangle]
        pub unsafe extern "C" fn stbds_arrgrowf(
            a: *mut core::ffi::c_void,
            elemsize: size_t,
            addlen: size_t,
            mut min_cap: size_t,
        ) -> *mut core::ffi::c_void {
            let temp: stbds_array_header = {
                stbds_array_header {
                    length: 0 as size_t,
                    capacity: 0,
                    hash_table: std::ptr::null_mut::<core::ffi::c_void>(),
                    temp: 0,
                }
            };
            let mut b: *mut core::ffi::c_void = std::ptr::null_mut::<core::ffi::c_void>();
            let min_len: size_t = ((if !a.is_null() {
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).length
                    as ptrdiff_t
            } else {
                0 as ptrdiff_t
            }) as size_t)
                .wrapping_add(addlen);
            if min_len > min_cap {
                min_cap = min_len;
            }
            if min_cap
                <= (if !a.is_null() {
                    (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                } else {
                    0 as size_t
                })
            {
                return a;
            }
            if min_cap
                < (2 as size_t).wrapping_mul(if !a.is_null() {
                    (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                } else {
                    0 as size_t
                })
            {
                min_cap = (2 as size_t).wrapping_mul(if !a.is_null() {
                    (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                } else {
                    0 as size_t
                });
            } else if min_cap < 4 as size_t {
                min_cap = 4 as size_t;
            }
            b = realloc(
                (if !a.is_null() {
                    (a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))
                } else {
                    std::ptr::null_mut::<stbds_array_header>()
                }) as *mut core::ffi::c_void,
                elemsize
                    .wrapping_mul(min_cap)
                    .wrapping_add(::core::mem::size_of::<stbds_array_header>() as size_t),
            );
            b = (b as *mut core::ffi::c_char).add(::core::mem::size_of::<stbds_array_header>())
                as *mut core::ffi::c_void;
            if a.is_null() {
                (*(b as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = 0 as size_t;
                (*(b as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .hash_table = std::ptr::null_mut::<core::ffi::c_void>();
                (*(b as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).temp =
                    0 as ptrdiff_t;
            }
            (*(b as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).capacity =
                min_cap;
            b
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_arrfreef(a: *mut core::ffi::c_void) {
            free(
                (a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))
                    as *mut core::ffi::c_void,
            );
        }
        pub const STBDS_BUCKET_LENGTH: core::ffi::c_int = 8 as core::ffi::c_int;
        pub const STBDS_BUCKET_MASK: core::ffi::c_int = STBDS_BUCKET_LENGTH - 1 as core::ffi::c_int;
        pub const STBDS_INDEX_EMPTY: core::ffi::c_int = -(1 as core::ffi::c_int);
        pub const STBDS_INDEX_DELETED: core::ffi::c_int = -(2 as core::ffi::c_int);
        pub const STBDS_HASH_EMPTY: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const STBDS_HASH_DELETED: core::ffi::c_int = 1 as core::ffi::c_int;
        static mut stbds_hash_seed: size_t = 0x31415926 as size_t;
        #[no_mangle]
        pub unsafe extern "C" fn stbds_rand_seed(seed: size_t) {
            stbds_hash_seed = seed;
        }
        pub const STBDS_SIZE_T_BITS: usize = ::core::mem::size_of::<size_t>().wrapping_mul(8_usize);
        unsafe extern "C" fn stbds_probe_position(
            hash: size_t,
            slot_count: size_t,
            slot_log2: size_t,
        ) -> size_t {
            let mut pos: size_t = 0;
            pos = hash & slot_count.wrapping_sub(1 as size_t);
            pos
        }
        unsafe extern "C" fn stbds_log2(mut slot_count: size_t) -> size_t {
            let mut n: size_t = 0 as size_t;
            while slot_count > 1 as size_t {
                slot_count >>= 1 as core::ffi::c_int;
                n = n.wrapping_add(1);
            }
            n
        }
        unsafe extern "C" fn stbds_make_hash_index(
            slot_count: size_t,
            ot: *mut stbds_hash_index,
        ) -> *mut stbds_hash_index {
            let mut t: *mut stbds_hash_index = std::ptr::null_mut::<stbds_hash_index>();
            t = realloc(
                std::ptr::null_mut::<core::ffi::c_void>(),
                (slot_count >> ({ 3 as core::ffi::c_int }))
                    .wrapping_mul(::core::mem::size_of::<stbds_hash_bucket>() as size_t)
                    .wrapping_add(::core::mem::size_of::<stbds_hash_index>() as size_t)
                    .wrapping_add(64 as size_t)
                    .wrapping_sub(1 as size_t),
            ) as *mut stbds_hash_index;
            (*t).storage = ((t.offset(1 as core::ffi::c_int as isize) as size_t)
                .wrapping_add(64 as size_t)
                .wrapping_sub(1 as size_t)
                & !(64 as core::ffi::c_int - 1 as core::ffi::c_int) as size_t)
                as *mut stbds_hash_bucket;
            (*t).slot_count = slot_count;
            (*t).slot_count_log2 = stbds_log2(slot_count);
            (*t).tombstone_count = 0 as size_t;
            (*t).used_count = 0 as size_t;
            (*t).used_count_threshold =
                slot_count.wrapping_sub(slot_count >> 2 as core::ffi::c_int);
            (*t).tombstone_count_threshold = (slot_count >> 3 as core::ffi::c_int)
                .wrapping_add(slot_count >> 4 as core::ffi::c_int);
            (*t).used_count_shrink_threshold = slot_count >> 2 as core::ffi::c_int;
            if slot_count <= STBDS_BUCKET_LENGTH as size_t {
                (*t).used_count_shrink_threshold = 0 as size_t;
            }
            if ((*t).used_count_threshold).wrapping_add((*t).tombstone_count_threshold)
                < (*t).slot_count
            {
            } else {
                __assert_fail(b"t->used_count_threshold + t->tombstone_count_threshold < t->slot_count\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    401 as core::ffi::c_uint,
                    ([b's' as i8, b't' as i8, b'b' as i8, b'd' as i8,
                                    b's' as i8, b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8,
                                    b'h' as i8, b'_' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'e' as i8, b'x' as i8, b' ' as i8, b'*' as i8, b's' as i8,
                                    b't' as i8, b'b' as i8, b'd' as i8, b's' as i8, b'_' as i8,
                                    b'm' as i8, b'a' as i8, b'k' as i8, b'e' as i8, b'_' as i8,
                                    b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8, b'_' as i8,
                                    b'i' as i8, b'n' as i8, b'd' as i8, b'e' as i8, b'x' as i8,
                                    b'(' as i8, b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8,
                                    b'_' as i8, b't' as i8, b',' as i8, b' ' as i8, b's' as i8,
                                    b't' as i8, b'b' as i8, b'd' as i8, b's' as i8, b'_' as i8,
                                    b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8, b'_' as i8,
                                    b'i' as i8, b'n' as i8, b'd' as i8, b'e' as i8, b'x' as i8,
                                    b' ' as i8, b'*' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6648: {};
            if !ot.is_null() {
                (*t).string = (*ot).string;
                (*t).seed = (*ot).seed;
            } else {
                let mut a: size_t = 0;
                let mut b: size_t = 0;
                let mut temp: size_t = 0;
                memset(
                    &mut (*t).string as *mut stbds_string_arena as *mut core::ffi::c_void,
                    0 as core::ffi::c_int,
                    ::core::mem::size_of::<stbds_string_arena>() as size_t,
                );
                (*t).seed = stbds_hash_seed;
                temp =
                    (0x87b0b0fd as core::ffi::c_uint ^ 2147001325 as core::ffi::c_uint) as size_t;
                temp <<= 16 as core::ffi::c_int;
                temp <<= 16 as core::ffi::c_int;
                temp >>= 16 as core::ffi::c_int;
                temp >>= 16 as core::ffi::c_int;
                a = 0x27bb2ee6 as size_t;
                a <<= 16 as core::ffi::c_int;
                a <<= 16 as core::ffi::c_int;
                a = (a as core::ffi::c_ulong ^ (temp ^ 2147001325 as size_t) as core::ffi::c_ulong)
                    as size_t;
                temp = (0xb504f32d as core::ffi::c_uint ^ 715136305 as core::ffi::c_uint) as size_t;
                temp <<= 16 as core::ffi::c_int;
                temp <<= 16 as core::ffi::c_int;
                temp >>= 16 as core::ffi::c_int;
                temp >>= 16 as core::ffi::c_int;
                b = 0 as size_t;
                b <<= 16 as core::ffi::c_int;
                b <<= 16 as core::ffi::c_int;
                b = (b as core::ffi::c_ulong ^ (temp ^ 715136305 as size_t) as core::ffi::c_ulong)
                    as size_t;
                stbds_hash_seed = stbds_hash_seed.wrapping_mul(a).wrapping_add(b);
            }
            let mut i: size_t = 0;
            let mut j: size_t = 0;
            i = 0 as size_t;
            while i < slot_count
                >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                    3 as core::ffi::c_int
                } else {
                    2 as core::ffi::c_int
                })
            {
                let b_0: *mut stbds_hash_bucket =
                    &mut *((*t).storage).add(i) as *mut stbds_hash_bucket;
                j = 0 as size_t;
                while j < STBDS_BUCKET_LENGTH as size_t {
                    (*b_0).hash[j as usize] = STBDS_HASH_EMPTY as size_t;
                    j = j.wrapping_add(1);
                }
                j = 0 as size_t;
                while j < STBDS_BUCKET_LENGTH as size_t {
                    (*b_0).index[j as usize] = STBDS_INDEX_EMPTY as ptrdiff_t;
                    j = j.wrapping_add(1);
                }
                i = i.wrapping_add(1);
            }
            if !ot.is_null() {
                let mut i_0: size_t = 0;
                let mut j_0: size_t = 0;
                (*t).used_count = (*ot).used_count;
                i_0 = 0 as size_t;
                while i_0
                    < (*ot).slot_count
                        >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                            3 as core::ffi::c_int
                        } else {
                            2 as core::ffi::c_int
                        })
                {
                    let ob: *mut stbds_hash_bucket =
                        &mut *((*ot).storage).add(i_0) as *mut stbds_hash_bucket;
                    j_0 = 0 as size_t;
                    while j_0 < STBDS_BUCKET_LENGTH as size_t {
                        if (*ob).index[j_0 as usize] >= 0 as ptrdiff_t {
                            let hash: size_t = (*ob).hash[j_0 as usize];
                            let mut pos: size_t =
                                stbds_probe_position(hash, (*t).slot_count, (*t).slot_count_log2);
                            let mut step: size_t = STBDS_BUCKET_LENGTH as size_t;
                            's_177: loop {
                                let mut limit: size_t = 0;
                                let mut z: size_t = 0;
                                let mut bucket: *mut stbds_hash_bucket =
                                    std::ptr::null_mut::<stbds_hash_bucket>();
                                bucket = &mut *((*t).storage).add(
                                    pos >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                                        3 as core::ffi::c_int
                                    } else {
                                        2 as core::ffi::c_int
                                    }),
                                )
                                    as *mut stbds_hash_bucket;
                                z = pos & STBDS_BUCKET_MASK as size_t;
                                while z < STBDS_BUCKET_LENGTH as size_t {
                                    if (*bucket).hash[z as usize] == 0 as size_t {
                                        (*bucket).hash[z as usize] = hash;
                                        (*bucket).index[z as usize] = (*ob).index[j_0 as usize];
                                        break 's_177;
                                    } else {
                                        z = z.wrapping_add(1);
                                    }
                                }
                                limit = pos & STBDS_BUCKET_MASK as size_t;
                                z = 0 as size_t;
                                while z < limit {
                                    if (*bucket).hash[z as usize] == 0 as size_t {
                                        (*bucket).hash[z as usize] = hash;
                                        (*bucket).index[z as usize] = (*ob).index[j_0 as usize];
                                        break 's_177;
                                    } else {
                                        z = z.wrapping_add(1);
                                    }
                                }
                                pos = (pos as core::ffi::c_ulong)
                                    .wrapping_add(step as core::ffi::c_ulong)
                                    as size_t as size_t;
                                step = (step as core::ffi::c_ulong)
                                    .wrapping_add(STBDS_BUCKET_LENGTH as core::ffi::c_ulong)
                                    as size_t as size_t;
                                pos = (pos as core::ffi::c_ulong
                                    & ((*t).slot_count).wrapping_sub(1 as size_t)
                                        as core::ffi::c_ulong)
                                    as size_t;
                            }
                        }
                        j_0 = j_0.wrapping_add(1);
                    }
                    i_0 = i_0.wrapping_add(1);
                }
            }
            t
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hash_string(
            mut str: *mut core::ffi::c_char,
            seed: size_t,
        ) -> size_t {
            let mut hash: size_t = seed;
            while *str != 0 {
                let fresh10 = *str;
                str = str.offset(1);
                hash = (hash << 9 as core::ffi::c_int
                    | hash >> STBDS_SIZE_T_BITS.wrapping_sub(9_usize))
                .wrapping_add(fresh10 as core::ffi::c_uchar as size_t);
            }
            hash = (hash as core::ffi::c_ulong ^ seed as core::ffi::c_ulong) as size_t;
            hash = (!hash).wrapping_add(hash << 18 as core::ffi::c_int);
            hash = (hash as core::ffi::c_ulong
                ^ (hash
                    ^ (hash >> 31 as core::ffi::c_int
                        | hash << STBDS_SIZE_T_BITS.wrapping_sub(31_usize)))
                    as core::ffi::c_ulong) as size_t;
            hash = hash.wrapping_mul(21 as size_t);
            hash = (hash as core::ffi::c_ulong
                ^ (hash
                    ^ (hash >> 11 as core::ffi::c_int
                        | hash << STBDS_SIZE_T_BITS.wrapping_sub(11_usize)))
                    as core::ffi::c_ulong) as size_t;
            hash = (hash as core::ffi::c_ulong)
                .wrapping_add((hash << 6 as core::ffi::c_int) as core::ffi::c_ulong)
                as size_t as size_t;
            hash = (hash as core::ffi::c_ulong
                ^ (hash >> 22 as core::ffi::c_int
                    | hash << STBDS_SIZE_T_BITS.wrapping_sub(22_usize))
                    as core::ffi::c_ulong) as size_t;
            hash.wrapping_add(seed)
        }
        pub const STBDS_SIPHASH_C_ROUNDS: core::ffi::c_int = 2 as core::ffi::c_int;
        pub const STBDS_SIPHASH_D_ROUNDS: core::ffi::c_int = 4 as core::ffi::c_int;
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
                while j < STBDS_SIPHASH_C_ROUNDS as size_t {
                    v0 = (v0 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v1 = v1 << 13 as core::ffi::c_int
                        | v1 >> STBDS_SIZE_T_BITS.wrapping_sub(13_usize);
                    v1 = (v1 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                    v0 = v0
                        << ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize)
                        | v0 >> STBDS_SIZE_T_BITS.wrapping_sub(
                            ::core::mem::size_of::<size_t>()
                                .wrapping_mul(8_usize)
                                .wrapping_div(2_usize),
                        );
                    v2 = (v2 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v3 = v3 << 16 as core::ffi::c_int
                        | v3 >> STBDS_SIZE_T_BITS.wrapping_sub(16_usize);
                    v3 = (v3 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                    v2 = (v2 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v1 = v1 << 17 as core::ffi::c_int
                        | v1 >> STBDS_SIZE_T_BITS.wrapping_sub(17_usize);
                    v1 = (v1 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                    v2 = v2
                        << ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize)
                        | v2 >> STBDS_SIZE_T_BITS.wrapping_sub(
                            ::core::mem::size_of::<size_t>()
                                .wrapping_mul(8_usize)
                                .wrapping_div(2_usize),
                        );
                    v0 = (v0 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                        as size_t;
                    v3 = v3 << 21 as core::ffi::c_int
                        | v3 >> STBDS_SIZE_T_BITS.wrapping_sub(21_usize);
                    v3 = (v3 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                    j = j.wrapping_add(1);
                }
                v0 = (v0 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
                i = (i as core::ffi::c_ulong)
                    .wrapping_add(::core::mem::size_of::<size_t>() as core::ffi::c_ulong)
                    as size_t as size_t;
                d = d.add(::core::mem::size_of::<size_t>());
            }
            data = len << STBDS_SIZE_T_BITS.wrapping_sub(8_usize);
            let mut current_block_40: u64;
            match len.wrapping_sub(i) {
                7 => {
                    data = (data as core::ffi::c_ulong
                        | (((*d.offset(6 as core::ffi::c_int as isize) as size_t)
                            << 24 as core::ffi::c_int)
                            << 24 as core::ffi::c_int)
                            as core::ffi::c_ulong) as size_t;
                    current_block_40 = 647119486518834161;
                }
                6 => {
                    current_block_40 = 647119486518834161;
                }
                5 => {
                    current_block_40 = 14633916157105357387;
                }
                4 => {
                    current_block_40 = 221011803393545056;
                }
                3 => {
                    current_block_40 = 16980036910974281513;
                }
                2 => {
                    current_block_40 = 4145577654460783414;
                }
                1 => {
                    current_block_40 = 9958072204267899983;
                }
                0 | _ => {
                    current_block_40 = 1538046216550696469;
                }
            }
            if current_block_40 == 647119486518834161 {
                data = (data as core::ffi::c_ulong
                    | (((*d.offset(5 as core::ffi::c_int as isize) as size_t)
                        << 20 as core::ffi::c_int)
                        << 20 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 14633916157105357387;
            }
            if current_block_40 == 14633916157105357387 {
                data = (data as core::ffi::c_ulong
                    | (((*d.offset(4 as core::ffi::c_int as isize) as size_t)
                        << 16 as core::ffi::c_int)
                        << 16 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 221011803393545056;
            }
            if current_block_40 == 221011803393545056 {
                data = (data as core::ffi::c_ulong
                    | ((*d.offset(3 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 24 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 16980036910974281513;
            }
            if current_block_40 == 16980036910974281513 {
                data = (data as core::ffi::c_ulong
                    | ((*d.offset(2 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 16 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 4145577654460783414;
            }
            if current_block_40 == 4145577654460783414 {
                data = (data as core::ffi::c_ulong
                    | ((*d.offset(1 as core::ffi::c_int as isize) as core::ffi::c_int)
                        << 8 as core::ffi::c_int) as core::ffi::c_ulong)
                    as size_t;
                current_block_40 = 9958072204267899983;
            }
            if current_block_40 == 9958072204267899983 {
                data = (data as core::ffi::c_ulong
                    | *d.offset(0 as core::ffi::c_int as isize) as core::ffi::c_ulong)
                    as size_t;
            }
            v3 = (v3 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
            j = 0 as size_t;
            while j < STBDS_SIPHASH_C_ROUNDS as size_t {
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 13 as core::ffi::c_int | v1 >> STBDS_SIZE_T_BITS.wrapping_sub(13_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                v0 = v0
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v0 >> STBDS_SIZE_T_BITS.wrapping_sub(
                        ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize),
                    );
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 16 as core::ffi::c_int | v3 >> STBDS_SIZE_T_BITS.wrapping_sub(16_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 17 as core::ffi::c_int | v1 >> STBDS_SIZE_T_BITS.wrapping_sub(17_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = v2
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v2 >> STBDS_SIZE_T_BITS.wrapping_sub(
                        ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize),
                    );
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 21 as core::ffi::c_int | v3 >> STBDS_SIZE_T_BITS.wrapping_sub(21_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                j = j.wrapping_add(1);
            }
            v0 = (v0 as core::ffi::c_ulong ^ data as core::ffi::c_ulong) as size_t;
            v2 = (v2 as core::ffi::c_ulong ^ 0xff as core::ffi::c_ulong) as size_t;
            j = 0 as size_t;
            while j < STBDS_SIPHASH_D_ROUNDS as size_t {
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 13 as core::ffi::c_int | v1 >> STBDS_SIZE_T_BITS.wrapping_sub(13_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v0 as core::ffi::c_ulong) as size_t;
                v0 = v0
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v0 >> STBDS_SIZE_T_BITS.wrapping_sub(
                        ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize),
                    );
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 16 as core::ffi::c_int | v3 >> STBDS_SIZE_T_BITS.wrapping_sub(16_usize);
                v3 = (v3 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = (v2 as core::ffi::c_ulong).wrapping_add(v1 as core::ffi::c_ulong) as size_t
                    as size_t;
                v1 = v1 << 17 as core::ffi::c_int | v1 >> STBDS_SIZE_T_BITS.wrapping_sub(17_usize);
                v1 = (v1 as core::ffi::c_ulong ^ v2 as core::ffi::c_ulong) as size_t;
                v2 = v2
                    << ::core::mem::size_of::<size_t>()
                        .wrapping_mul(8_usize)
                        .wrapping_div(2_usize)
                    | v2 >> STBDS_SIZE_T_BITS.wrapping_sub(
                        ::core::mem::size_of::<size_t>()
                            .wrapping_mul(8_usize)
                            .wrapping_div(2_usize),
                    );
                v0 = (v0 as core::ffi::c_ulong).wrapping_add(v3 as core::ffi::c_ulong) as size_t
                    as size_t;
                v3 = v3 << 21 as core::ffi::c_int | v3 >> STBDS_SIZE_T_BITS.wrapping_sub(21_usize);
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
        unsafe extern "C" fn stbds_is_key_equal(
            a: *mut core::ffi::c_void,
            elemsize: size_t,
            key: *mut core::ffi::c_void,
            keysize: size_t,
            keyoffset: size_t,
            mode: core::ffi::c_int,
            i: size_t,
        ) -> core::ffi::c_int {
            if mode >= STBDS_HM_STRING {
                (0 as core::ffi::c_int
                    == strcmp(
                        key as *mut core::ffi::c_char,
                        *((a as *mut core::ffi::c_char)
                            .add(elemsize.wrapping_mul(i))
                            .add(keyoffset)
                            as *mut *mut core::ffi::c_char),
                    )) as core::ffi::c_int
            } else {
                (0 as core::ffi::c_int
                    == memcmp(
                        key,
                        (a as *mut core::ffi::c_char)
                            .add(elemsize.wrapping_mul(i))
                            .add(keyoffset) as *const core::ffi::c_void,
                        keysize,
                    )) as core::ffi::c_int
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hmfree_func(a: *mut core::ffi::c_void, elemsize: size_t) {
            if a.is_null() {
                return;
            }
            if !((*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                .hash_table as *mut stbds_hash_index)
                .is_null()
            {
                if (*((*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .hash_table as *mut stbds_hash_index))
                    .string
                    .mode as core::ffi::c_int
                    == STBDS_SH_STRDUP as core::ffi::c_int
                {
                    let mut i: size_t = 0;
                    i = 1 as size_t;
                    while i
                        < (*(a as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .length
                    {
                        free(
                            *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i))
                                as *mut *mut core::ffi::c_char)
                                as *mut core::ffi::c_void,
                        );
                        i = i.wrapping_add(1);
                    }
                }
                stbds_strreset(
                    &mut (*((*(a as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .hash_table as *mut stbds_hash_index))
                        .string,
                );
            }
            free(
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .hash_table,
            );
            free(
                (a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))
                    as *mut core::ffi::c_void,
            );
        }
        unsafe extern "C" fn stbds_hm_find_slot(
            a: *mut core::ffi::c_void,
            elemsize: size_t,
            key: *mut core::ffi::c_void,
            keysize: size_t,
            keyoffset: size_t,
            mode: core::ffi::c_int,
        ) -> ptrdiff_t {
            let raw_a: *mut core::ffi::c_void = (a as *mut core::ffi::c_char)
                .offset(-(elemsize as isize))
                as *mut core::ffi::c_void;
            let table: *mut stbds_hash_index = (*(raw_a as *mut stbds_array_header)
                .offset(-(1 as core::ffi::c_int as isize)))
            .hash_table as *mut stbds_hash_index;
            let mut hash: size_t = if mode >= STBDS_HM_STRING {
                stbds_hash_string(key as *mut core::ffi::c_char, (*table).seed)
            } else {
                stbds_hash_bytes(key, keysize, (*table).seed)
            };
            let mut step: size_t = STBDS_BUCKET_LENGTH as size_t;
            let mut limit: size_t = 0;
            let mut i: size_t = 0;
            let mut pos: size_t = 0;
            let mut bucket: *mut stbds_hash_bucket = std::ptr::null_mut::<stbds_hash_bucket>();
            if hash < 2 as size_t {
                hash = (hash as core::ffi::c_ulong).wrapping_add(2 as core::ffi::c_ulong) as size_t
                    as size_t;
            }
            pos = stbds_probe_position(hash, (*table).slot_count, (*table).slot_count_log2);
            loop {
                bucket = &mut *((*table).storage).add(
                    pos >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                        3 as core::ffi::c_int
                    } else {
                        2 as core::ffi::c_int
                    }),
                ) as *mut stbds_hash_bucket;
                i = pos & STBDS_BUCKET_MASK as size_t;
                while i < STBDS_BUCKET_LENGTH as size_t {
                    if (*bucket).hash[i as usize] == hash {
                        if stbds_is_key_equal(
                            a,
                            elemsize,
                            key,
                            keysize,
                            keyoffset,
                            mode,
                            (*bucket).index[i as usize] as size_t,
                        ) != 0
                        {
                            return (pos & !STBDS_BUCKET_MASK as size_t).wrapping_add(i)
                                as ptrdiff_t;
                        }
                    } else if (*bucket).hash[i as usize] == STBDS_HASH_EMPTY as size_t {
                        return -(1 as core::ffi::c_int) as ptrdiff_t;
                    }
                    i = i.wrapping_add(1);
                }
                limit = pos & STBDS_BUCKET_MASK as size_t;
                i = 0 as size_t;
                while i < limit {
                    if (*bucket).hash[i as usize] == hash {
                        if stbds_is_key_equal(
                            a,
                            elemsize,
                            key,
                            keysize,
                            keyoffset,
                            mode,
                            (*bucket).index[i as usize] as size_t,
                        ) != 0
                        {
                            return (pos & !STBDS_BUCKET_MASK as size_t).wrapping_add(i)
                                as ptrdiff_t;
                        }
                    } else if (*bucket).hash[i as usize] == STBDS_HASH_EMPTY as size_t {
                        return -(1 as core::ffi::c_int) as ptrdiff_t;
                    }
                    i = i.wrapping_add(1);
                }
                pos = (pos as core::ffi::c_ulong).wrapping_add(step as core::ffi::c_ulong) as size_t
                    as size_t;
                step = (step as core::ffi::c_ulong)
                    .wrapping_add(STBDS_BUCKET_LENGTH as core::ffi::c_ulong)
                    as size_t as size_t;
                pos = (pos as core::ffi::c_ulong
                    & ((*table).slot_count).wrapping_sub(1 as size_t) as core::ffi::c_ulong)
                    as size_t;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hmget_key_ts(
            mut a: *mut core::ffi::c_void,
            elemsize: size_t,
            key: *mut core::ffi::c_void,
            keysize: size_t,
            temp: *mut ptrdiff_t,
            mode: core::ffi::c_int,
        ) -> *mut core::ffi::c_void {
            let keyoffset: size_t = 0 as size_t;
            if a.is_null() {
                a = stbds_arrgrowf(
                    std::ptr::null_mut::<core::ffi::c_void>(),
                    elemsize,
                    0 as size_t,
                    1 as size_t,
                );
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(a as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length as core::ffi::c_ulong)
                    .wrapping_add(1 as core::ffi::c_ulong) as size_t
                    as size_t;
                memset(a, 0 as core::ffi::c_int, elemsize);
                *temp = STBDS_INDEX_EMPTY as ptrdiff_t;
                (a as *mut core::ffi::c_char).add(elemsize) as *mut core::ffi::c_void
            } else {
                let mut table: *mut stbds_hash_index = std::ptr::null_mut::<stbds_hash_index>();
                let raw_a: *mut core::ffi::c_void = (a as *mut core::ffi::c_char)
                    .offset(-(elemsize as isize))
                    as *mut core::ffi::c_void;
                table = (*(raw_a as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .hash_table as *mut stbds_hash_index;
                if table.is_null() {
                    *temp = -(1 as core::ffi::c_int) as ptrdiff_t;
                } else {
                    let slot: ptrdiff_t =
                        stbds_hm_find_slot(a, elemsize, key, keysize, keyoffset, mode);
                    if slot < 0 as ptrdiff_t {
                        *temp = STBDS_INDEX_EMPTY as ptrdiff_t;
                    } else {
                        let b: *mut stbds_hash_bucket = &mut *((*table).storage).offset(
                            (slot
                                >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                                    3 as core::ffi::c_int
                                } else {
                                    2 as core::ffi::c_int
                                })) as isize,
                        )
                            as *mut stbds_hash_bucket;
                        *temp = (*b).index[(slot & STBDS_BUCKET_MASK as ptrdiff_t) as usize];
                    }
                }
                a
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hmget_key(
            a: *mut core::ffi::c_void,
            elemsize: size_t,
            key: *mut core::ffi::c_void,
            keysize: size_t,
            mode: core::ffi::c_int,
        ) -> *mut core::ffi::c_void {
            let mut temp: ptrdiff_t = 0;
            let p: *mut core::ffi::c_void =
                stbds_hmget_key_ts(a, elemsize, key, keysize, &mut temp, mode);
            (*((p as *mut core::ffi::c_char).offset(-(elemsize as isize))
                as *mut stbds_array_header)
                .offset(-(1 as core::ffi::c_int as isize)))
            .temp = temp;
            p
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hmput_default(
            mut a: *mut core::ffi::c_void,
            elemsize: size_t,
        ) -> *mut core::ffi::c_void {
            if a.is_null()
                || (*((a as *mut core::ffi::c_char).offset(-(elemsize as isize))
                    as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length
                    == 0 as size_t
            {
                a = stbds_arrgrowf(
                    (if !a.is_null() {
                        (a as *mut core::ffi::c_char).offset(-(elemsize as isize))
                    } else {
                        std::ptr::null_mut::<core::ffi::c_char>()
                    }) as *mut core::ffi::c_void,
                    elemsize,
                    0 as size_t,
                    1 as size_t,
                );
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(a as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length as core::ffi::c_ulong)
                    .wrapping_add(1 as core::ffi::c_ulong) as size_t
                    as size_t;
                memset(a, 0 as core::ffi::c_int, elemsize);
                a = (a as *mut core::ffi::c_char).add(elemsize) as *mut core::ffi::c_void;
            }
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hmput_key(
            mut a: *mut core::ffi::c_void,
            elemsize: size_t,
            key: *mut core::ffi::c_void,
            keysize: size_t,
            mode: core::ffi::c_int,
        ) -> *mut core::ffi::c_void {
            let keyoffset: size_t = 0 as size_t;
            let mut raw_a: *mut core::ffi::c_void = std::ptr::null_mut::<core::ffi::c_void>();
            let mut table: *mut stbds_hash_index = std::ptr::null_mut::<stbds_hash_index>();
            if a.is_null() {
                a = stbds_arrgrowf(
                    std::ptr::null_mut::<core::ffi::c_void>(),
                    elemsize,
                    0 as size_t,
                    1 as size_t,
                );
                memset(a, 0 as core::ffi::c_int, elemsize);
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(a as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length as core::ffi::c_ulong)
                    .wrapping_add(1 as core::ffi::c_ulong) as size_t
                    as size_t;
                a = (a as *mut core::ffi::c_char).add(elemsize) as *mut core::ffi::c_void;
            }
            raw_a = a;
            a = (a as *mut core::ffi::c_char).offset(-(elemsize as isize))
                as *mut core::ffi::c_void;
            table = (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                .hash_table as *mut stbds_hash_index;
            if table.is_null() || (*table).used_count >= (*table).used_count_threshold {
                let mut nt: *mut stbds_hash_index = std::ptr::null_mut::<stbds_hash_index>();
                let mut slot_count: size_t = 0;
                slot_count = if table.is_null() {
                    STBDS_BUCKET_LENGTH as size_t
                } else {
                    ((*table).slot_count).wrapping_mul(2 as size_t)
                };
                nt = stbds_make_hash_index(slot_count, table);
                if !table.is_null() {
                    free(table as *mut core::ffi::c_void);
                } else {
                    (*nt).string.mode = (if mode >= STBDS_HM_STRING {
                        STBDS_SH_DEFAULT as core::ffi::c_int
                    } else {
                        0 as core::ffi::c_int
                    }) as core::ffi::c_uchar;
                }
                table = nt;
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .hash_table = table as *mut core::ffi::c_void;
            }
            let mut hash: size_t = if mode >= STBDS_HM_STRING {
                stbds_hash_string(key as *mut core::ffi::c_char, (*table).seed)
            } else {
                stbds_hash_bytes(key, keysize, (*table).seed)
            };
            let mut step: size_t = STBDS_BUCKET_LENGTH as size_t;
            let mut pos: size_t = 0;
            let mut tombstone: ptrdiff_t = -(1 as core::ffi::c_int) as ptrdiff_t;
            let mut bucket: *mut stbds_hash_bucket = std::ptr::null_mut::<stbds_hash_bucket>();
            if hash < 2 as size_t {
                hash = (hash as core::ffi::c_ulong).wrapping_add(2 as core::ffi::c_ulong) as size_t
                    as size_t;
            }
            pos = stbds_probe_position(hash, (*table).slot_count, (*table).slot_count_log2);
            's_101: loop {
                let mut limit: size_t = 0;
                let mut i: size_t = 0;
                bucket = &mut *((*table).storage).add(
                    pos >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                        3 as core::ffi::c_int
                    } else {
                        2 as core::ffi::c_int
                    }),
                ) as *mut stbds_hash_bucket;
                i = pos & STBDS_BUCKET_MASK as size_t;
                while i < STBDS_BUCKET_LENGTH as size_t {
                    if (*bucket).hash[i as usize] == hash {
                        if stbds_is_key_equal(
                            raw_a,
                            elemsize,
                            key,
                            keysize,
                            keyoffset,
                            mode,
                            (*bucket).index[i as usize] as size_t,
                        ) != 0
                        {
                            (*(a as *mut stbds_array_header)
                                .offset(-(1 as core::ffi::c_int as isize)))
                            .temp = (*bucket).index[i as usize];
                            if mode >= STBDS_HM_STRING {
                                *((*(a as *mut stbds_array_header)
                                    .offset(-(1 as core::ffi::c_int as isize)))
                                .hash_table
                                    as *mut *mut core::ffi::c_char) = *((raw_a
                                    as *mut core::ffi::c_char)
                                    .add(
                                        elemsize
                                            .wrapping_mul((*bucket).index[i as usize] as size_t),
                                    )
                                    .add(keyoffset)
                                    as *mut *mut core::ffi::c_char);
                            }
                            return (a as *mut core::ffi::c_char).add(elemsize)
                                as *mut core::ffi::c_void;
                        }
                    } else if (*bucket).hash[i as usize] == 0 as size_t {
                        pos = (pos & !STBDS_BUCKET_MASK as size_t).wrapping_add(i);
                        break 's_101;
                    } else if tombstone < 0 as ptrdiff_t
                        && (*bucket).index[i as usize] == STBDS_INDEX_DELETED as ptrdiff_t
                    {
                        tombstone =
                            (pos & !STBDS_BUCKET_MASK as size_t).wrapping_add(i) as ptrdiff_t;
                    }
                    i = i.wrapping_add(1);
                }
                limit = pos & STBDS_BUCKET_MASK as size_t;
                i = 0 as size_t;
                while i < limit {
                    if (*bucket).hash[i as usize] == hash {
                        if stbds_is_key_equal(
                            raw_a,
                            elemsize,
                            key,
                            keysize,
                            keyoffset,
                            mode,
                            (*bucket).index[i as usize] as size_t,
                        ) != 0
                        {
                            (*(a as *mut stbds_array_header)
                                .offset(-(1 as core::ffi::c_int as isize)))
                            .temp = (*bucket).index[i as usize];
                            return (a as *mut core::ffi::c_char).add(elemsize)
                                as *mut core::ffi::c_void;
                        }
                    } else if (*bucket).hash[i as usize] == 0 as size_t {
                        pos = (pos & !STBDS_BUCKET_MASK as size_t).wrapping_add(i);
                        break 's_101;
                    } else if tombstone < 0 as ptrdiff_t
                        && (*bucket).index[i as usize] == STBDS_INDEX_DELETED as ptrdiff_t
                    {
                        tombstone =
                            (pos & !STBDS_BUCKET_MASK as size_t).wrapping_add(i) as ptrdiff_t;
                    }
                    i = i.wrapping_add(1);
                }
                pos = (pos as core::ffi::c_ulong).wrapping_add(step as core::ffi::c_ulong) as size_t
                    as size_t;
                step = (step as core::ffi::c_ulong)
                    .wrapping_add(STBDS_BUCKET_LENGTH as core::ffi::c_ulong)
                    as size_t as size_t;
                pos = (pos as core::ffi::c_ulong
                    & ((*table).slot_count).wrapping_sub(1 as size_t) as core::ffi::c_ulong)
                    as size_t;
            }
            if tombstone >= 0 as ptrdiff_t {
                pos = tombstone as size_t;
                (*table).tombstone_count = ((*table).tombstone_count).wrapping_sub(1);
            }
            (*table).used_count = ((*table).used_count).wrapping_add(1);
            let i_0: ptrdiff_t = if !a.is_null() {
                (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).length
                    as ptrdiff_t
            } else {
                0 as ptrdiff_t
            };
            if (i_0 as size_t).wrapping_add(1 as size_t)
                > (if !a.is_null() {
                    (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                } else {
                    0 as size_t
                })
            {
                *(&mut a as *mut *mut core::ffi::c_void) =
                    stbds_arrgrowf(a, elemsize, 1 as size_t, 0 as size_t);
            }
            raw_a = (a as *mut core::ffi::c_char).add(elemsize) as *mut core::ffi::c_void;
            if (i_0 as size_t).wrapping_add(1 as size_t)
                <= (if !a.is_null() {
                    (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                } else {
                    0 as size_t
                })
            {
            } else {
                __assert_fail(b"(size_t) i+1 <= stbds_arrcap(a)\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    778 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b'*' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                    b'd' as i8, b's' as i8, b'_' as i8, b'h' as i8, b'm' as i8,
                                    b'p' as i8, b'u' as i8, b't' as i8, b'_' as i8, b'k' as i8,
                                    b'e' as i8, b'y' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                    b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8,
                                    b'_' as i8, b't' as i8, b',' as i8, b' ' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8,
                                    b',' as i8, b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8,
                                    b'e' as i8, b'_' as i8, b't' as i8, b',' as i8, b' ' as i8,
                                    b'i' as i8, b'n' as i8, b't' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_5452: {};
            (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).length =
                (i_0 + 1 as ptrdiff_t) as size_t;
            bucket = &mut *((*table).storage).add(
                pos >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                    3 as core::ffi::c_int
                } else {
                    2 as core::ffi::c_int
                }),
            ) as *mut stbds_hash_bucket;
            (*bucket).hash[(pos & STBDS_BUCKET_MASK as size_t) as usize] = hash;
            (*bucket).index[(pos & STBDS_BUCKET_MASK as size_t) as usize] = i_0 - 1 as ptrdiff_t;
            (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).temp =
                i_0 - 1 as ptrdiff_t;
            match (*table).string.mode as core::ffi::c_int {
                2 => {
                    *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                        as *mut *mut core::ffi::c_char) =
                        stbds_strdup(key as *mut core::ffi::c_char);
                    *((*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .hash_table as *mut *mut core::ffi::c_char) =
                        *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                            as *mut *mut core::ffi::c_char);
                }
                3 => {
                    *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                        as *mut *mut core::ffi::c_char) =
                        stbds_stralloc(&mut (*table).string, key as *mut core::ffi::c_char);
                    *((*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .hash_table as *mut *mut core::ffi::c_char) =
                        *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                            as *mut *mut core::ffi::c_char);
                }
                1 => {
                    *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                        as *mut *mut core::ffi::c_char) = key as *mut core::ffi::c_char;
                    *((*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .hash_table as *mut *mut core::ffi::c_char) =
                        *((a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                            as *mut *mut core::ffi::c_char);
                }
                _ => {
                    memcpy(
                        (a as *mut core::ffi::c_char).add(elemsize.wrapping_mul(i_0 as size_t))
                            as *mut core::ffi::c_void,
                        key,
                        keysize,
                    );
                }
            }
            (a as *mut core::ffi::c_char).add(elemsize) as *mut core::ffi::c_void
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_shmode_func(
            elemsize: size_t,
            mode: core::ffi::c_int,
        ) -> *mut core::ffi::c_void {
            let a: *mut core::ffi::c_void = stbds_arrgrowf(
                std::ptr::null_mut::<core::ffi::c_void>(),
                elemsize,
                0 as size_t,
                1 as size_t,
            );
            let mut h: *mut stbds_hash_index = std::ptr::null_mut::<stbds_hash_index>();
            memset(a, 0 as core::ffi::c_int, elemsize);
            (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))).length =
                1 as size_t;
            h = stbds_make_hash_index(
                STBDS_BUCKET_LENGTH as size_t,
                std::ptr::null_mut::<stbds_hash_index>(),
            );
            (*(a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                .hash_table = h as *mut core::ffi::c_void;
            (*h).string.mode = mode as core::ffi::c_uchar;
            (a as *mut core::ffi::c_char).add(elemsize) as *mut core::ffi::c_void
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_hmdel_key(
            a: *mut core::ffi::c_void,
            elemsize: size_t,
            key: *mut core::ffi::c_void,
            keysize: size_t,
            keyoffset: size_t,
            mode: core::ffi::c_int,
        ) -> *mut core::ffi::c_void {
            if a.is_null() {
                std::ptr::null_mut::<core::ffi::c_void>()
            } else {
                let mut table: *mut stbds_hash_index = std::ptr::null_mut::<stbds_hash_index>();
                let raw_a: *mut core::ffi::c_void = (a as *mut core::ffi::c_char)
                    .offset(-(elemsize as isize))
                    as *mut core::ffi::c_void;
                table = (*(raw_a as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .hash_table as *mut stbds_hash_index;
                (*(raw_a as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .temp = 0 as ptrdiff_t;
                if table.is_null() {
                    a
                } else {
                    let mut slot: ptrdiff_t = 0;
                    slot = stbds_hm_find_slot(a, elemsize, key, keysize, keyoffset, mode);
                    if slot < 0 as ptrdiff_t {
                        a
                    } else {
                        let mut b: *mut stbds_hash_bucket = &mut *((*table).storage).offset(
                            (slot
                                >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                                    3 as core::ffi::c_int
                                } else {
                                    2 as core::ffi::c_int
                                })) as isize,
                        )
                            as *mut stbds_hash_bucket;
                        let mut i: core::ffi::c_int =
                            (slot & STBDS_BUCKET_MASK as ptrdiff_t) as core::ffi::c_int;
                        let old_index: ptrdiff_t = (*b).index[i as usize];
                        let final_index: ptrdiff_t = (if !raw_a.is_null() {
                            (*(raw_a as *mut stbds_array_header)
                                .offset(-(1 as core::ffi::c_int as isize)))
                            .length as ptrdiff_t
                        } else {
                            0 as ptrdiff_t
                        }) - 1 as ptrdiff_t
                            - 1 as ptrdiff_t;
                        if slot < (*table).slot_count as ptrdiff_t {
                        } else {
                            __assert_fail(b"slot < (ptrdiff_t) table->slot_count\0" as
                                        *const u8 as *const core::ffi::c_char,
                                b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                                        as *const u8 as *const core::ffi::c_char,
                                828 as core::ffi::c_uint,
                                ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                                b' ' as i8, b'*' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                                b'd' as i8, b's' as i8, b'_' as i8, b'h' as i8, b'm' as i8,
                                                b'd' as i8, b'e' as i8, b'l' as i8, b'_' as i8, b'k' as i8,
                                                b'e' as i8, b'y' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                                b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                                b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8,
                                                b'_' as i8, b't' as i8, b',' as i8, b' ' as i8, b'v' as i8,
                                                b'o' as i8, b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8,
                                                b',' as i8, b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8,
                                                b'e' as i8, b'_' as i8, b't' as i8, b',' as i8, b' ' as i8,
                                                b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8, b'_' as i8,
                                                b't' as i8, b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8,
                                                b't' as i8, b')' as i8, b'\0' as i8]).as_ptr());
                        }
                        'c_7556: {};
                        (*table).used_count = ((*table).used_count).wrapping_sub(1);
                        (*table).tombstone_count = ((*table).tombstone_count).wrapping_add(1);
                        (*(raw_a as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .temp = 1 as ptrdiff_t;
                        if (*table).used_count >= 0 as size_t {
                        } else {
                            __assert_fail(b"table->used_count >= 0\0" as *const u8 as
                                    *const core::ffi::c_char,
                                b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                                        as *const u8 as *const core::ffi::c_char,
                                832 as core::ffi::c_uint,
                                ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                                b' ' as i8, b'*' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                                b'd' as i8, b's' as i8, b'_' as i8, b'h' as i8, b'm' as i8,
                                                b'd' as i8, b'e' as i8, b'l' as i8, b'_' as i8, b'k' as i8,
                                                b'e' as i8, b'y' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                                b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                                b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8,
                                                b'_' as i8, b't' as i8, b',' as i8, b' ' as i8, b'v' as i8,
                                                b'o' as i8, b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8,
                                                b',' as i8, b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8,
                                                b'e' as i8, b'_' as i8, b't' as i8, b',' as i8, b' ' as i8,
                                                b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8, b'_' as i8,
                                                b't' as i8, b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8,
                                                b't' as i8, b')' as i8, b'\0' as i8]).as_ptr());
                        }
                        'c_7494: {};
                        (*b).hash[i as usize] = STBDS_HASH_DELETED as size_t;
                        (*b).index[i as usize] = STBDS_INDEX_DELETED as ptrdiff_t;
                        if mode == STBDS_HM_STRING
                            && (*table).string.mode as core::ffi::c_int
                                == STBDS_SH_STRDUP as core::ffi::c_int
                        {
                            free(
                                *((a as *mut core::ffi::c_char)
                                    .add(elemsize.wrapping_mul(old_index as size_t))
                                    as *mut *mut core::ffi::c_char)
                                    as *mut core::ffi::c_void,
                            );
                        }
                        if old_index != final_index {
                            memmove(
                                (a as *mut core::ffi::c_char)
                                    .add(elemsize.wrapping_mul(old_index as size_t))
                                    as *mut core::ffi::c_void,
                                (a as *mut core::ffi::c_char)
                                    .add(elemsize.wrapping_mul(final_index as size_t))
                                    as *const core::ffi::c_void,
                                elemsize,
                            );
                            if mode == STBDS_HM_STRING {
                                slot = stbds_hm_find_slot(
                                    a,
                                    elemsize,
                                    *((a as *mut core::ffi::c_char)
                                        .add(elemsize.wrapping_mul(old_index as size_t))
                                        .add(keyoffset)
                                        as *mut *mut core::ffi::c_char)
                                        as *mut core::ffi::c_void,
                                    keysize,
                                    keyoffset,
                                    mode,
                                );
                            } else {
                                slot = stbds_hm_find_slot(
                                    a,
                                    elemsize,
                                    (a as *mut core::ffi::c_char)
                                        .add(elemsize.wrapping_mul(old_index as size_t))
                                        .add(keyoffset)
                                        as *mut core::ffi::c_void,
                                    keysize,
                                    keyoffset,
                                    mode,
                                );
                            }
                            if slot >= 0 as ptrdiff_t {
                            } else {
                                __assert_fail(b"slot >= 0\0" as *const u8 as
                                        *const core::ffi::c_char,
                                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                                            as *const u8 as *const core::ffi::c_char,
                                    846 as core::ffi::c_uint,
                                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                                    b' ' as i8, b'*' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                                    b'd' as i8, b's' as i8, b'_' as i8, b'h' as i8, b'm' as i8,
                                                    b'd' as i8, b'e' as i8, b'l' as i8, b'_' as i8, b'k' as i8,
                                                    b'e' as i8, b'y' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                                    b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                                    b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8,
                                                    b'_' as i8, b't' as i8, b',' as i8, b' ' as i8, b'v' as i8,
                                                    b'o' as i8, b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8,
                                                    b',' as i8, b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8,
                                                    b'e' as i8, b'_' as i8, b't' as i8, b',' as i8, b' ' as i8,
                                                    b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8, b'_' as i8,
                                                    b't' as i8, b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8,
                                                    b't' as i8, b')' as i8, b'\0' as i8]).as_ptr());
                            }
                            'c_7302: {};
                            b = &mut *((*table).storage).offset(
                                (slot
                                    >> (if STBDS_BUCKET_LENGTH == 8 as core::ffi::c_int {
                                        3 as core::ffi::c_int
                                    } else {
                                        2 as core::ffi::c_int
                                    })) as isize,
                            ) as *mut stbds_hash_bucket;
                            i = (slot & STBDS_BUCKET_MASK as ptrdiff_t) as core::ffi::c_int;
                            if (*b).index[i as usize] == final_index {
                            } else {
                                __assert_fail(b"b->index[i] == final_index\0" as *const u8
                                        as *const core::ffi::c_char,
                                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                                            as *const u8 as *const core::ffi::c_char,
                                    849 as core::ffi::c_uint,
                                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                                    b' ' as i8, b'*' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                                    b'd' as i8, b's' as i8, b'_' as i8, b'h' as i8, b'm' as i8,
                                                    b'd' as i8, b'e' as i8, b'l' as i8, b'_' as i8, b'k' as i8,
                                                    b'e' as i8, b'y' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                                    b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                                    b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8,
                                                    b'_' as i8, b't' as i8, b',' as i8, b' ' as i8, b'v' as i8,
                                                    b'o' as i8, b'i' as i8, b'd' as i8, b' ' as i8, b'*' as i8,
                                                    b',' as i8, b' ' as i8, b's' as i8, b'i' as i8, b'z' as i8,
                                                    b'e' as i8, b'_' as i8, b't' as i8, b',' as i8, b' ' as i8,
                                                    b's' as i8, b'i' as i8, b'z' as i8, b'e' as i8, b'_' as i8,
                                                    b't' as i8, b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8,
                                                    b't' as i8, b')' as i8, b'\0' as i8]).as_ptr());
                            }
                            'c_7196: {};
                            (*b).index[i as usize] = old_index;
                        }
                        (*(raw_a as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .length = ((*(raw_a as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .length as core::ffi::c_ulong)
                            .wrapping_sub(1 as core::ffi::c_ulong)
                            as size_t as size_t;
                        if (*table).used_count < (*table).used_count_shrink_threshold
                            && (*table).slot_count > STBDS_BUCKET_LENGTH as size_t
                        {
                            (*(raw_a as *mut stbds_array_header)
                                .offset(-(1 as core::ffi::c_int as isize)))
                            .hash_table = stbds_make_hash_index(
                                (*table).slot_count >> 1 as core::ffi::c_int,
                                table,
                            ) as *mut core::ffi::c_void;
                            free(table as *mut core::ffi::c_void);
                        } else if (*table).tombstone_count > (*table).tombstone_count_threshold {
                            (*(raw_a as *mut stbds_array_header)
                                .offset(-(1 as core::ffi::c_int as isize)))
                            .hash_table = stbds_make_hash_index((*table).slot_count, table)
                                as *mut core::ffi::c_void;
                            free(table as *mut core::ffi::c_void);
                        }
                        a
                    }
                }
            }
        }
        unsafe extern "C" fn stbds_strdup(str: *mut core::ffi::c_char) -> *mut core::ffi::c_char {
            let len: size_t = (strlen(str)).wrapping_add(1 as size_t);
            let p: *mut core::ffi::c_char =
                realloc(std::ptr::null_mut::<core::ffi::c_void>(), len) as *mut core::ffi::c_char;
            memmove(
                p as *mut core::ffi::c_void,
                str as *const core::ffi::c_void,
                len,
            );
            p
        }
        pub const STBDS_STRING_ARENA_BLOCKSIZE_MIN: core::ffi::c_uint = 512 as core::ffi::c_uint;
        pub const STBDS_STRING_ARENA_BLOCKSIZE_MAX: core::ffi::c_uint =
            (1 as core::ffi::c_uint) << 20 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn stbds_stralloc(
            a: *mut stbds_string_arena,
            str: *mut core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let mut p: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let len: size_t = (strlen(str)).wrapping_add(1 as size_t);
            if len > (*a).remaining {
                let mut blocksize: size_t = (*a).block as size_t;
                blocksize =
                    (512 as core::ffi::c_uint as size_t) << (blocksize >> 1 as core::ffi::c_int);
                if blocksize < ((1 as core::ffi::c_uint) << 20 as core::ffi::c_int) as size_t {
                    (*a).block = ((*a).block).wrapping_add(1);
                }
                if len > blocksize {
                    let sb: *mut stbds_string_block = realloc(
                        std::ptr::null_mut::<core::ffi::c_void>(),
                        (::core::mem::size_of::<stbds_string_block>() as size_t)
                            .wrapping_sub(8 as size_t)
                            .wrapping_add(len),
                    )
                        as *mut stbds_string_block;
                    memmove(
                        ((*sb).storage).as_mut_ptr() as *mut core::ffi::c_void,
                        str as *const core::ffi::c_void,
                        len,
                    );
                    if !((*a).storage).is_null() {
                        (*sb).next = (*(*a).storage).next;
                        (*(*a).storage).next = sb as *mut stbds_string_block;
                    } else {
                        (*sb).next = std::ptr::null_mut::<stbds_string_block>();
                        (*a).storage = sb;
                        (*a).remaining = 0 as size_t;
                    }
                    return ((*sb).storage).as_mut_ptr();
                } else {
                    let sb_0: *mut stbds_string_block = realloc(
                        std::ptr::null_mut::<core::ffi::c_void>(),
                        (::core::mem::size_of::<stbds_string_block>() as size_t)
                            .wrapping_sub(8 as size_t)
                            .wrapping_add(blocksize),
                    )
                        as *mut stbds_string_block;
                    (*sb_0).next = (*a).storage as *mut stbds_string_block;
                    (*a).storage = sb_0;
                    (*a).remaining = blocksize;
                }
            }
            if len <= (*a).remaining {
            } else {
                __assert_fail(b"len <= a->remaining\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    913 as core::ffi::c_uint,
                    ([b'c' as i8, b'h' as i8, b'a' as i8, b'r' as i8,
                                    b' ' as i8, b'*' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                    b'd' as i8, b's' as i8, b'_' as i8, b's' as i8, b't' as i8,
                                    b'r' as i8, b'a' as i8, b'l' as i8, b'l' as i8, b'o' as i8,
                                    b'c' as i8, b'(' as i8, b's' as i8, b't' as i8, b'b' as i8,
                                    b'd' as i8, b's' as i8, b'_' as i8, b's' as i8, b't' as i8,
                                    b'r' as i8, b'i' as i8, b'n' as i8, b'g' as i8, b'_' as i8,
                                    b'a' as i8, b'r' as i8, b'e' as i8, b'n' as i8, b'a' as i8,
                                    b' ' as i8, b'*' as i8, b',' as i8, b' ' as i8, b'c' as i8,
                                    b'h' as i8, b'a' as i8, b'r' as i8, b' ' as i8, b'*' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_3843: {};
            p = ((*(*a).storage).storage)
                .as_mut_ptr()
                .add((*a).remaining)
                .offset(-(len as isize));
            (*a).remaining = ((*a).remaining as core::ffi::c_ulong)
                .wrapping_sub(len as core::ffi::c_ulong) as size_t
                as size_t;
            memmove(
                p as *mut core::ffi::c_void,
                str as *const core::ffi::c_void,
                len,
            );
            p
        }
        #[no_mangle]
        pub unsafe extern "C" fn stbds_strreset(a: *mut stbds_string_arena) {
            let mut x: *mut stbds_string_block = std::ptr::null_mut::<stbds_string_block>();
            let mut y: *mut stbds_string_block = std::ptr::null_mut::<stbds_string_block>();
            x = (*a).storage;
            while !x.is_null() {
                y = (*x).next as *mut stbds_string_block;
                free(x as *mut core::ffi::c_void);
                x = y;
            }
            memset(
                a as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<stbds_string_arena>() as size_t,
            );
        }
        static mut buffer: [core::ffi::c_char; 256] = [0; 256];
        #[no_mangle]
        pub unsafe extern "C" fn strkey(n: core::ffi::c_int) -> *mut core::ffi::c_char {
            sprintf(
                buffer.as_mut_ptr(),
                b"test_%d\0" as *const u8 as *const core::ffi::c_char,
                n,
            );
            buffer.as_mut_ptr()
        }
        #[no_mangle]
        pub unsafe extern "C" fn arr_ins(num: core::ffi::c_int) {
            let mut arr: *mut core::ffi::c_int = std::ptr::null_mut::<core::ffi::c_int>();
            let mut i: core::ffi::c_int = 0;
            let j: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < 5 as core::ffi::c_int {
                if arr.is_null()
                    || ((*(arr as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .length)
                        .wrapping_add(1 as size_t)
                        > (*(arr as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                {
                    arr = stbds_arrgrowf(
                        arr as *mut core::ffi::c_void,
                        ::core::mem::size_of::<core::ffi::c_int>() as size_t,
                        1 as size_t,
                        0 as size_t,
                    ) as *mut core::ffi::c_int;
                };
                let fresh1 = (*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length;
                (*(arr as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length)
                    .wrapping_add(1);
                *arr.add(fresh1) = 1 as core::ffi::c_int;
                if arr.is_null()
                    || ((*(arr as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .length)
                        .wrapping_add(1 as size_t)
                        > (*(arr as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                {
                    arr = stbds_arrgrowf(
                        arr as *mut core::ffi::c_void,
                        ::core::mem::size_of::<core::ffi::c_int>() as size_t,
                        1 as size_t,
                        0 as size_t,
                    ) as *mut core::ffi::c_int;
                };
                let fresh3 = (*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length;
                (*(arr as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length)
                    .wrapping_add(1);
                *arr.add(fresh3) = 2 as core::ffi::c_int;
                if arr.is_null()
                    || ((*(arr as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .length)
                        .wrapping_add(1 as size_t)
                        > (*(arr as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                {
                    arr = stbds_arrgrowf(
                        arr as *mut core::ffi::c_void,
                        ::core::mem::size_of::<core::ffi::c_int>() as size_t,
                        1 as size_t,
                        0 as size_t,
                    ) as *mut core::ffi::c_int;
                };
                let fresh5 = (*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length;
                (*(arr as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length)
                    .wrapping_add(1);
                *arr.add(fresh5) = 3 as core::ffi::c_int;
                if arr.is_null()
                    || ((*(arr as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .length)
                        .wrapping_add(1 as size_t)
                        > (*(arr as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                {
                    arr = stbds_arrgrowf(
                        arr as *mut core::ffi::c_void,
                        ::core::mem::size_of::<core::ffi::c_int>() as size_t,
                        1 as size_t,
                        0 as size_t,
                    ) as *mut core::ffi::c_int;
                };
                let fresh7 = (*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length;
                (*(arr as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                    .length = ((*(arr as *mut stbds_array_header)
                    .offset(-(1 as core::ffi::c_int as isize)))
                .length)
                    .wrapping_add(1);
                *arr.add(fresh7) = 4 as core::ffi::c_int;
                if arr.is_null()
                    || ((*(arr as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .length)
                        .wrapping_add(1 as size_t)
                        > (*(arr as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .capacity
                {
                    arr = stbds_arrgrowf(
                        arr as *mut core::ffi::c_void,
                        ::core::mem::size_of::<core::ffi::c_int>() as size_t,
                        1 as size_t,
                        0 as size_t,
                    ) as *mut core::ffi::c_int;
                };
                {
                    (*(arr as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize)))
                        .length = ((*(arr as *mut stbds_array_header)
                        .offset(-(1 as core::ffi::c_int as isize)))
                    .length as core::ffi::c_ulong)
                        .wrapping_add(1 as core::ffi::c_ulong)
                        as size_t as size_t;
                };
                memmove(
                    &mut *arr.offset((i + 1 as core::ffi::c_int) as isize) as *mut core::ffi::c_int
                        as *mut core::ffi::c_void,
                    &mut *arr.offset(i as isize) as *mut core::ffi::c_int
                        as *const core::ffi::c_void,
                    (::core::mem::size_of::<core::ffi::c_int>() as size_t).wrapping_mul(
                        ((*(arr as *mut stbds_array_header)
                            .offset(-(1 as core::ffi::c_int as isize)))
                        .length)
                            .wrapping_sub(1 as size_t)
                            .wrapping_sub(i as size_t),
                    ),
                );
                *arr.offset(i as isize) = num;
                if *arr.offset(i as isize) == num {
                } else {
                    __assert_fail(b"arr[i] == num\0" as *const u8 as
                            *const core::ffi::c_char,
                        b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                                as *const u8 as *const core::ffi::c_char,
                        953 as core::ffi::c_uint, __ASSERT_FUNCTION.as_ptr());
                }
                'c_186: {};
                if i < 4 as core::ffi::c_int {
                    if *arr.offset(4 as core::ffi::c_int as isize) == 4 as core::ffi::c_int {
                    } else {
                        __assert_fail(b"arr[4] == 4\0" as *const u8 as
                                *const core::ffi::c_char,
                            b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/arr_ins_lib/src/arr_ins_lib/test_case/src/lib.c\0"
                                    as *const u8 as *const core::ffi::c_char,
                            955 as core::ffi::c_uint, __ASSERT_FUNCTION.as_ptr());
                    }
                    'c_128: {};
                }
                if !arr.is_null() {
                    free(
                        (arr as *mut stbds_array_header).offset(-(1 as core::ffi::c_int as isize))
                            as *mut core::ffi::c_void,
                    );
                };
                arr = std::ptr::null_mut::<core::ffi::c_int>();
                i += 1;
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("arr_ins_lib", SOURCE, &[], &[]);
}
