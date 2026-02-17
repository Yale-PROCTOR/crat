use super::run_ownership_case;

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
    pub mod hashmap {
        extern "C" {
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
        }
        pub type size_t = usize;
        pub type __uint8_t = u8;
        pub type __uint64_t = u64;
        pub type uint8_t = __uint8_t;
        pub type uint64_t = __uint64_t;
        pub type tree_id_t = uint64_t;
        #[repr(C)]
        pub struct hashmap_entry {
            pub key: tree_id_t,
            pub value: *mut core::ffi::c_void,
            pub occupied: core::ffi::c_int,
            pub deleted: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for hashmap_entry {}
        #[automatically_derived]
        impl ::core::clone::Clone for hashmap_entry {
            #[inline]
            fn clone(&self) -> hashmap_entry {
                let _: ::core::clone::AssertParamIsClone<tree_id_t>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub type hashmap_entry_t = hashmap_entry;
        #[repr(C)]
        pub struct hashmap_t {
            pub entries: *mut hashmap_entry_t,
            pub capacity: size_t,
            pub size: size_t,
            pub deleted_count: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for hashmap_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for hashmap_t {
            #[inline]
            fn clone(&self) -> hashmap_t {
                let _: ::core::clone::AssertParamIsClone<*mut hashmap_entry_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const HASHMAP_INITIAL_CAPACITY: core::ffi::c_int = 16 as core::ffi::c_int;
        pub const HASHMAP_LOAD_FACTOR: core::ffi::c_double = 0.75f64;
        unsafe extern "C" fn hash_function(mut key: tree_id_t) -> uint64_t {
            let mut hash: uint64_t = 14695981039346656037 as uint64_t;
            let bytes: *mut uint8_t = &mut key as *mut tree_id_t as *mut uint8_t;
            let mut i: size_t = 0 as size_t;
            while i < ::core::mem::size_of::<tree_id_t>() {
                hash =
                    (hash as core::ffi::c_ulong ^ *bytes.add(i) as core::ffi::c_ulong) as uint64_t;
                hash = (hash as core::ffi::c_ulonglong)
                    .wrapping_mul(1099511628211 as core::ffi::c_ulonglong)
                    as uint64_t as uint64_t;
                i = i.wrapping_add(1);
            }
            hash
        }
        unsafe extern "C" fn should_resize(map: *mut hashmap_t) -> core::ffi::c_int {
            let load: core::ffi::c_double = ((*map).size).wrapping_add((*map).deleted_count)
                as core::ffi::c_double
                / (*map).capacity as core::ffi::c_double;
            (load > HASHMAP_LOAD_FACTOR) as core::ffi::c_int
        }
        unsafe extern "C" fn hashmap_resize(map: *mut hashmap_t) -> core::ffi::c_int {
            let old_capacity: size_t = (*map).capacity;
            let old_entries: *mut hashmap_entry_t = (*map).entries;
            (*map).capacity = ((*map).capacity as core::ffi::c_ulong)
                .wrapping_mul(2 as core::ffi::c_ulong) as size_t
                as size_t;
            (*map).entries = calloc(
                (*map).capacity,
                ::core::mem::size_of::<hashmap_entry_t>() as size_t,
            ) as *mut hashmap_entry_t;
            if ((*map).entries).is_null() {
                (*map).entries = old_entries;
                (*map).capacity = old_capacity;
                return -(1 as core::ffi::c_int);
            }
            (*map).size = 0 as size_t;
            (*map).deleted_count = 0 as size_t;
            let mut i: size_t = 0 as size_t;
            while i < old_capacity {
                if (*old_entries.add(i)).occupied != 0 && (*old_entries.add(i)).deleted == 0 {
                    hashmap_put(map, (*old_entries.add(i)).key, (*old_entries.add(i)).value);
                }
                i = i.wrapping_add(1);
            }
            free(old_entries as *mut core::ffi::c_void);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_create() -> *mut hashmap_t {
            let map: *mut hashmap_t =
                malloc(::core::mem::size_of::<hashmap_t>() as size_t) as *mut hashmap_t;
            if map.is_null() {
                return std::ptr::null_mut::<hashmap_t>();
            }
            (*map).capacity = HASHMAP_INITIAL_CAPACITY as size_t;
            (*map).size = 0 as size_t;
            (*map).deleted_count = 0 as size_t;
            (*map).entries = calloc(
                (*map).capacity,
                ::core::mem::size_of::<hashmap_entry_t>() as size_t,
            ) as *mut hashmap_entry_t;
            if ((*map).entries).is_null() {
                free(map as *mut core::ffi::c_void);
                return std::ptr::null_mut::<hashmap_t>();
            }
            map
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_destroy(map: *mut hashmap_t) {
            if !map.is_null() {
                free((*map).entries as *mut core::ffi::c_void);
                free(map as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_put(
            map: *mut hashmap_t,
            key: tree_id_t,
            value: *mut core::ffi::c_void,
        ) -> core::ffi::c_int {
            if map.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if should_resize(map) != 0 && hashmap_resize(map) != 0 as core::ffi::c_int {
                return -(1 as core::ffi::c_int);
            }
            let hash: uint64_t = hash_function(key);
            let index: size_t = (hash as size_t).wrapping_rem((*map).capacity);
            let mut probe: size_t = 0 as size_t;
            while probe < (*map).capacity {
                let current: size_t = index.wrapping_add(probe).wrapping_rem((*map).capacity);
                if (*((*map).entries).add(current)).occupied == 0 {
                    (*((*map).entries).add(current)).key = key;
                    (*((*map).entries).add(current)).value = value;
                    (*((*map).entries).add(current)).occupied = 1 as core::ffi::c_int;
                    (*((*map).entries).add(current)).deleted = 0 as core::ffi::c_int;
                    (*map).size = ((*map).size).wrapping_add(1);
                    return 0 as core::ffi::c_int;
                } else if (*((*map).entries).add(current)).deleted != 0 {
                    (*((*map).entries).add(current)).key = key;
                    (*((*map).entries).add(current)).value = value;
                    (*((*map).entries).add(current)).deleted = 0 as core::ffi::c_int;
                    (*map).size = ((*map).size).wrapping_add(1);
                    (*map).deleted_count = ((*map).deleted_count).wrapping_sub(1);
                    return 0 as core::ffi::c_int;
                } else if (*((*map).entries).add(current)).key == key {
                    (*((*map).entries).add(current)).value = value;
                    return 0 as core::ffi::c_int;
                }
                probe = probe.wrapping_add(1);
            }
            -(1 as core::ffi::c_int)
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_get(
            map: *mut hashmap_t,
            key: tree_id_t,
        ) -> *mut core::ffi::c_void {
            if map.is_null() {
                return NULL;
            }
            let hash: uint64_t = hash_function(key);
            let index: size_t = (hash as size_t).wrapping_rem((*map).capacity);
            let mut probe: size_t = 0 as size_t;
            while probe < (*map).capacity {
                let current: size_t = index.wrapping_add(probe).wrapping_rem((*map).capacity);
                if (*((*map).entries).add(current)).occupied == 0 {
                    return NULL;
                }
                if (*((*map).entries).add(current)).deleted == 0
                    && (*((*map).entries).add(current)).key == key
                {
                    return (*((*map).entries).add(current)).value;
                }
                probe = probe.wrapping_add(1);
            }
            NULL
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_remove(
            map: *mut hashmap_t,
            key: tree_id_t,
        ) -> *mut core::ffi::c_void {
            if map.is_null() {
                return NULL;
            }
            let hash: uint64_t = hash_function(key);
            let index: size_t = (hash as size_t).wrapping_rem((*map).capacity);
            let mut probe: size_t = 0 as size_t;
            while probe < (*map).capacity {
                let current: size_t = index.wrapping_add(probe).wrapping_rem((*map).capacity);
                if (*((*map).entries).add(current)).occupied == 0 {
                    return NULL;
                }
                if (*((*map).entries).add(current)).deleted == 0
                    && (*((*map).entries).add(current)).key == key
                {
                    let value: *mut core::ffi::c_void = (*((*map).entries).add(current)).value;
                    (*((*map).entries).add(current)).deleted = 1 as core::ffi::c_int;
                    (*map).size = ((*map).size).wrapping_sub(1);
                    (*map).deleted_count = ((*map).deleted_count).wrapping_add(1);
                    return value;
                }
                probe = probe.wrapping_add(1);
            }
            NULL
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_contains(
            map: *mut hashmap_t,
            key: tree_id_t,
        ) -> core::ffi::c_int {
            (hashmap_get(map, key) != NULL) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_size(map: *mut hashmap_t) -> size_t {
            if !map.is_null() {
                (*map).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn hashmap_clear(map: *mut hashmap_t) {
            if map.is_null() {
                return;
            }
            let mut i: size_t = 0 as size_t;
            while i < (*map).capacity {
                (*((*map).entries).add(i)).occupied = 0 as core::ffi::c_int;
                (*((*map).entries).add(i)).deleted = 0 as core::ffi::c_int;
                i = i.wrapping_add(1);
            }
            (*map).size = 0 as size_t;
            (*map).deleted_count = 0 as size_t;
        }
    }
    pub mod main {
        use crate::src::hashmap::hashmap_contains;
        use crate::src::hashmap::hashmap_create;
        use crate::src::hashmap::hashmap_destroy;
        use crate::src::hashmap::hashmap_get;
        use crate::src::hashmap::hashmap_put;
        use crate::src::hashmap::hashmap_remove;
        use crate::src::hashmap::hashmap_size;
        use crate::src::hashmap::hashmap_t;
        use crate::src::hashmap::size_t;
        use crate::src::hashmap::tree_id_t;
        use crate::src::tree::tree_add_node;
        use crate::src::tree::tree_contains;
        use crate::src::tree::tree_count_descendants;
        use crate::src::tree::tree_create;
        use crate::src::tree::tree_delete;
        use crate::src::tree::tree_find_path;
        use crate::src::tree::tree_get_depth;
        use crate::src::tree::tree_get_height;
        use crate::src::tree::tree_get_node;
        use crate::src::tree::tree_print;
        use crate::src::tree::tree_remove_node;
        use crate::src::tree::tree_size;
        extern "C" {
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn __assert_fail(
                __assertion: *const core::ffi::c_char,
                __file: *const core::ffi::c_char,
                __line: core::ffi::c_uint,
                __function: *const core::ffi::c_char,
            ) -> !;
        }
        #[repr(C)]
        pub struct tree_node {
            pub id: tree_id_t,
            pub parent_id: tree_id_t,
            pub child_ids: [tree_id_t; 32],
            pub child_count: core::ffi::c_int,
            pub data: [core::ffi::c_char; 256],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for tree_node {}
        #[automatically_derived]
        impl ::core::clone::Clone for tree_node {
            #[inline]
            fn clone(&self) -> tree_node {
                let _: ::core::clone::AssertParamIsClone<tree_id_t>;
                let _: ::core::clone::AssertParamIsClone<[tree_id_t; 32]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 256]>;
                *self
            }
        }
        pub type tree_node_t = tree_node;
        #[repr(C)]
        pub struct tree_t {
            pub node_map: *mut hashmap_t,
            pub root_id: tree_id_t,
            pub has_root: core::ffi::c_int,
            pub node_count: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for tree_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for tree_t {
            #[inline]
            fn clone(&self) -> tree_t {
                let _: ::core::clone::AssertParamIsClone<*mut hashmap_t>;
                let _: ::core::clone::AssertParamIsClone<tree_id_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        pub const MAX_CHILDREN: core::ffi::c_int = 32 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn test_hashmap_basic() {
            printf(
                b"\n=== Testing Hashmap Basic Operations ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let map: *mut hashmap_t = hashmap_create();
            if !map.is_null() {
            } else {
                __assert_fail(b"map != NULL\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    39 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2964: {};
            if hashmap_size(map) == 0 as size_t {
            } else {
                __assert_fail(b"hashmap_size(map) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    40 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2920: {};
            let mut val1: core::ffi::c_int = 42 as core::ffi::c_int;
            let mut val2: core::ffi::c_int = 100 as core::ffi::c_int;
            let mut val3: core::ffi::c_int = 200 as core::ffi::c_int;
            if hashmap_put(
                map,
                1 as tree_id_t,
                &mut val1 as *mut core::ffi::c_int as *mut core::ffi::c_void,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"hashmap_put(map, 1, &val1) == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    44 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2866: {};
            if hashmap_put(
                map,
                2 as tree_id_t,
                &mut val2 as *mut core::ffi::c_int as *mut core::ffi::c_void,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"hashmap_put(map, 2, &val2) == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    45 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2814: {};
            if hashmap_put(
                map,
                3 as tree_id_t,
                &mut val3 as *mut core::ffi::c_int as *mut core::ffi::c_void,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"hashmap_put(map, 3, &val3) == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    46 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2760: {};
            if hashmap_size(map) == 3 as size_t {
            } else {
                __assert_fail(b"hashmap_size(map) == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    47 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2716: {};
            if *(hashmap_get(map, 1 as tree_id_t) as *mut core::ffi::c_int)
                == 42 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"*(int *)hashmap_get(map, 1) == 42\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    49 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2663: {};
            if *(hashmap_get(map, 2 as tree_id_t) as *mut core::ffi::c_int)
                == 100 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"*(int *)hashmap_get(map, 2) == 100\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    50 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2611: {};
            if *(hashmap_get(map, 3 as tree_id_t) as *mut core::ffi::c_int)
                == 200 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"*(int *)hashmap_get(map, 3) == 200\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    51 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2559: {};
            let mut val4: core::ffi::c_int = 500 as core::ffi::c_int;
            if hashmap_put(
                map,
                1 as tree_id_t,
                &mut val4 as *mut core::ffi::c_int as *mut core::ffi::c_void,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"hashmap_put(map, 1, &val4) == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    55 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2503: {};
            if hashmap_size(map) == 3 as size_t {
            } else {
                __assert_fail(b"hashmap_size(map) == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    56 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2459: {};
            if *(hashmap_get(map, 1 as tree_id_t) as *mut core::ffi::c_int)
                == 500 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"*(int *)hashmap_get(map, 1) == 500\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    57 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2406: {};
            let removed: *mut core::ffi::c_void = hashmap_remove(map, 2 as tree_id_t);
            if removed == &mut val2 as *mut core::ffi::c_int as *mut core::ffi::c_void {
            } else {
                __assert_fail(b"removed == &val2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    61 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2355: {};
            if hashmap_size(map) == 2 as size_t {
            } else {
                __assert_fail(b"hashmap_size(map) == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    62 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2309: {};
            if (hashmap_get(map, 2 as tree_id_t)).is_null() {
            } else {
                __assert_fail(b"hashmap_get(map, 2) == NULL\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    63 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2257: {};
            if hashmap_contains(map, 1 as tree_id_t) == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"hashmap_contains(map, 1) == 1\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    66 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2211: {};
            if hashmap_contains(map, 2 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"hashmap_contains(map, 2) == 0\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    67 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2165: {};
            if hashmap_contains(map, 3 as tree_id_t) == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"hashmap_contains(map, 3) == 1\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    68 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'b' as i8,
                                    b'a' as i8, b's' as i8, b'i' as i8, b'c' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2114: {};
            hashmap_destroy(map);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b'h' as i8,
                    b'a' as i8,
                    b's' as i8,
                    b'h' as i8,
                    b'm' as i8,
                    b'a' as i8,
                    b'p' as i8,
                    b'_' as i8,
                    b'b' as i8,
                    b'a' as i8,
                    b's' as i8,
                    b'i' as i8,
                    b'c' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_hashmap_collisions() {
            printf(
                b"\n=== Testing Hashmap Collisions ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let map: *mut hashmap_t = hashmap_create();
            let mut values: [core::ffi::c_int; 100] = [0; 100];
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < 100 as core::ffi::c_int {
                values[i as usize] = i * 10 as core::ffi::c_int;
                if hashmap_put(
                    map,
                    i as tree_id_t,
                    &mut *values.as_mut_ptr().offset(i as isize) as *mut core::ffi::c_int
                        as *mut core::ffi::c_void,
                ) == 0 as core::ffi::c_int
                {
                } else {
                    __assert_fail(b"hashmap_put(map, i, &values[i]) == 0\0" as
                                *const u8 as *const core::ffi::c_char,
                        b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                                as *const u8 as *const core::ffi::c_char,
                        83 as core::ffi::c_uint,
                        ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                        b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                        b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                        b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'c' as i8,
                                        b'o' as i8, b'l' as i8, b'l' as i8, b'i' as i8, b's' as i8,
                                        b'i' as i8, b'o' as i8, b'n' as i8, b's' as i8, b'(' as i8,
                                        b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                        b'\0' as i8]).as_ptr());
                }
                'c_3204: {};
                i += 1;
            }
            if hashmap_size(map) == 100 as size_t {
            } else {
                __assert_fail(b"hashmap_size(map) == 100\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    86 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                    b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'c' as i8,
                                    b'o' as i8, b'l' as i8, b'l' as i8, b'i' as i8, b's' as i8,
                                    b'i' as i8, b'o' as i8, b'n' as i8, b's' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3153: {};
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < 100 as core::ffi::c_int {
                let val: *mut core::ffi::c_int =
                    hashmap_get(map, i_0 as tree_id_t) as *mut core::ffi::c_int;
                if !val.is_null() {
                } else {
                    __assert_fail(b"val != NULL\0" as *const u8 as
                            *const core::ffi::c_char,
                        b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                                as *const u8 as *const core::ffi::c_char,
                        91 as core::ffi::c_uint,
                        ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                        b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                        b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                        b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'c' as i8,
                                        b'o' as i8, b'l' as i8, b'l' as i8, b'i' as i8, b's' as i8,
                                        b'i' as i8, b'o' as i8, b'n' as i8, b's' as i8, b'(' as i8,
                                        b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                        b'\0' as i8]).as_ptr());
                }
                'c_3107: {};
                if *val == i_0 * 10 as core::ffi::c_int {
                } else {
                    __assert_fail(b"*val == i * 10\0" as *const u8 as
                            *const core::ffi::c_char,
                        b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                                as *const u8 as *const core::ffi::c_char,
                        92 as core::ffi::c_uint,
                        ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                        b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                        b'_' as i8, b'h' as i8, b'a' as i8, b's' as i8, b'h' as i8,
                                        b'm' as i8, b'a' as i8, b'p' as i8, b'_' as i8, b'c' as i8,
                                        b'o' as i8, b'l' as i8, b'l' as i8, b'i' as i8, b's' as i8,
                                        b'i' as i8, b'o' as i8, b'n' as i8, b's' as i8, b'(' as i8,
                                        b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                        b'\0' as i8]).as_ptr());
                }
                'c_3048: {};
                i_0 += 1;
            }
            hashmap_destroy(map);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b'h' as i8,
                    b'a' as i8,
                    b's' as i8,
                    b'h' as i8,
                    b'm' as i8,
                    b'a' as i8,
                    b'p' as i8,
                    b'_' as i8,
                    b'c' as i8,
                    b'o' as i8,
                    b'l' as i8,
                    b'l' as i8,
                    b'i' as i8,
                    b's' as i8,
                    b'i' as i8,
                    b'o' as i8,
                    b'n' as i8,
                    b's' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_creation() {
            printf(b"\n=== Testing Tree Creation ===\n\0" as *const u8 as *const core::ffi::c_char);
            let tree: *mut tree_t = tree_create();
            if !tree.is_null() {
            } else {
                __assert_fail(b"tree != NULL\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    103 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'r' as i8, b'e' as i8, b'a' as i8,
                                    b't' as i8, b'i' as i8, b'o' as i8, b'n' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3405: {};
            if tree_size(tree) == 0 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    104 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'r' as i8, b'e' as i8, b'a' as i8,
                                    b't' as i8, b'i' as i8, b'o' as i8, b'n' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3359: {};
            if (*tree).has_root == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree->has_root == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    105 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'r' as i8, b'e' as i8, b'a' as i8,
                                    b't' as i8, b'i' as i8, b'o' as i8, b'n' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3318: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'c' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'a' as i8,
                    b't' as i8,
                    b'i' as i8,
                    b'o' as i8,
                    b'n' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_add_root() {
            printf(b"\n=== Testing Tree Add Root ===\n\0" as *const u8 as *const core::ffi::c_char);
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    117 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3798: {};
            if tree_size(tree) == 1 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    118 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3754: {};
            if (*tree).has_root == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree->has_root == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    119 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3714: {};
            if (*tree).root_id == 1 as tree_id_t {
            } else {
                __assert_fail(b"tree->root_id == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    120 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3672: {};
            let root: *mut tree_node_t = tree_get_node(tree, 1 as tree_id_t);
            if !root.is_null() {
            } else {
                __assert_fail(b"root != NULL\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    123 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3630: {};
            if (*root).id == 1 as tree_id_t {
            } else {
                __assert_fail(b"root->id == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    124 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3588: {};
            if strcmp(
                ((*root).data).as_ptr(),
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"strcmp(root->data, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    125 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3534: {};
            if (*root).child_count == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"root->child_count == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    126 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'r' as i8, b'o' as i8, b'o' as i8, b't' as i8, b'(' as i8,
                                    b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3485: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'a' as i8,
                    b'd' as i8,
                    b'd' as i8,
                    b'_' as i8,
                    b'r' as i8,
                    b'o' as i8,
                    b'o' as i8,
                    b't' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_add_children() {
            printf(
                b"\n=== Testing Tree Add Children ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    138 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_4292: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    139 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_4238: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                1 as tree_id_t,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 1, \"child2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    140 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_4184: {};
            if tree_add_node(
                tree,
                4 as tree_id_t,
                1 as tree_id_t,
                b"child3\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 4, 1, \"child3\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    141 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_4128: {};
            if tree_size(tree) == 4 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 4\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    143 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_4084: {};
            let root: *mut tree_node_t = tree_get_node(tree, 1 as tree_id_t);
            if (*root).child_count == 3 as core::ffi::c_int {
            } else {
                __assert_fail(b"root->child_count == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    146 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_4044: {};
            if (*root).child_ids[0 as core::ffi::c_int as usize] == 2 as tree_id_t {
            } else {
                __assert_fail(b"root->child_ids[0] == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    147 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3996: {};
            if (*root).child_ids[1 as core::ffi::c_int as usize] == 3 as tree_id_t {
            } else {
                __assert_fail(b"root->child_ids[1] == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    148 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3948: {};
            if (*root).child_ids[2 as core::ffi::c_int as usize] == 4 as tree_id_t {
            } else {
                __assert_fail(b"root->child_ids[2] == 4\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    149 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'a' as i8, b'd' as i8, b'd' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_3892: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'a' as i8,
                    b'd' as i8,
                    b'd' as i8,
                    b'_' as i8,
                    b'c' as i8,
                    b'h' as i8,
                    b'i' as i8,
                    b'l' as i8,
                    b'd' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'n' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_deep_hierarchy() {
            printf(
                b"\n=== Testing Tree Deep Hierarchy ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"level0\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"level0\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    161 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5019: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"level1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"level1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    162 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4965: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                2 as tree_id_t,
                b"level2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 2, \"level2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    163 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4911: {};
            if tree_add_node(
                tree,
                4 as tree_id_t,
                3 as tree_id_t,
                b"level3\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 4, 3, \"level3\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    164 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4857: {};
            if tree_add_node(
                tree,
                5 as tree_id_t,
                4 as tree_id_t,
                b"level4\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 5, 4, \"level4\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    165 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4803: {};
            if tree_size(tree) == 5 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 5\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    167 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4759: {};
            if tree_get_depth(tree, 1 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_depth(tree, 1) == 0\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    169 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4713: {};
            if tree_get_depth(tree, 2 as tree_id_t) == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_depth(tree, 2) == 1\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    170 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4667: {};
            if tree_get_depth(tree, 3 as tree_id_t) == 2 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_depth(tree, 3) == 2\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    171 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4621: {};
            if tree_get_depth(tree, 4 as tree_id_t) == 3 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_depth(tree, 4) == 3\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    172 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4575: {};
            if tree_get_depth(tree, 5 as tree_id_t) == 4 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_depth(tree, 5) == 4\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    173 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4528: {};
            if tree_get_height(tree, 1 as tree_id_t) == 4 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_height(tree, 1) == 4\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    175 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4482: {};
            if tree_get_height(tree, 2 as tree_id_t) == 3 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_height(tree, 2) == 3\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    176 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4436: {};
            if tree_get_height(tree, 5 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_height(tree, 5) == 0\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    177 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'e' as i8, b'e' as i8, b'p' as i8,
                                    b'_' as i8, b'h' as i8, b'i' as i8, b'e' as i8, b'r' as i8,
                                    b'a' as i8, b'r' as i8, b'c' as i8, b'h' as i8, b'y' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4389: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'd' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'p' as i8,
                    b'_' as i8,
                    b'h' as i8,
                    b'i' as i8,
                    b'e' as i8,
                    b'r' as i8,
                    b'a' as i8,
                    b'r' as i8,
                    b'c' as i8,
                    b'h' as i8,
                    b'y' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_remove_leaf() {
            printf(
                b"\n=== Testing Tree Remove Leaf ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    188 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5499: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    189 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5445: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                1 as tree_id_t,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 1, \"child2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    190 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5391: {};
            if tree_size(tree) == 3 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    192 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5347: {};
            if tree_remove_node(tree, 3 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_remove_node(tree, 3) == 0\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    195 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5300: {};
            if tree_size(tree) == 2 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    196 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5256: {};
            if tree_contains(tree, 3 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_contains(tree, 3) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    197 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5210: {};
            let root: *mut tree_node_t = tree_get_node(tree, 1 as tree_id_t);
            if (*root).child_count == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"root->child_count == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    200 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5170: {};
            if (*root).child_ids[0 as core::ffi::c_int as usize] == 2 as tree_id_t {
            } else {
                __assert_fail(b"root->child_ids[0] == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    201 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'l' as i8, b'e' as i8,
                                    b'a' as i8, b'f' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5113: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'm' as i8,
                    b'o' as i8,
                    b'v' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'l' as i8,
                    b'e' as i8,
                    b'a' as i8,
                    b'f' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_remove_subtree() {
            printf(
                b"\n=== Testing Tree Remove Subtree ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    213 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6175: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    214 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6121: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                2 as tree_id_t,
                b"grandchild1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 2, \"grandchild1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    215 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6067: {};
            if tree_add_node(
                tree,
                4 as tree_id_t,
                2 as tree_id_t,
                b"grandchild2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 4, 2, \"grandchild2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    216 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6012: {};
            if tree_add_node(
                tree,
                5 as tree_id_t,
                1 as tree_id_t,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 5, 1, \"child2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    217 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5958: {};
            if tree_size(tree) == 5 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 5\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    219 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5914: {};
            if tree_remove_node(tree, 2 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_remove_node(tree, 2) == 0\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    222 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5868: {};
            if tree_size(tree) == 2 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    223 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5824: {};
            if tree_contains(tree, 2 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_contains(tree, 2) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    224 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5778: {};
            if tree_contains(tree, 3 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_contains(tree, 3) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    225 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5732: {};
            if tree_contains(tree, 4 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_contains(tree, 4) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    226 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5686: {};
            if tree_contains(tree, 1 as tree_id_t) == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_contains(tree, 1) == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    227 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5640: {};
            if tree_contains(tree, 5 as tree_id_t) == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_contains(tree, 5) == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    228 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b's' as i8, b'u' as i8,
                                    b'b' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_5594: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'm' as i8,
                    b'o' as i8,
                    b'v' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b's' as i8,
                    b'u' as i8,
                    b'b' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_remove_root() {
            printf(
                b"\n=== Testing Tree Remove Root ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    239 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6546: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    240 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6492: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                1 as tree_id_t,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 1, \"child2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    241 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6438: {};
            if tree_size(tree) == 3 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    243 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6394: {};
            if tree_remove_node(tree, 1 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_remove_node(tree, 1) == 0\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    246 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6348: {};
            if tree_size(tree) == 0 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    247 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6304: {};
            if (*tree).has_root == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree->has_root == 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    248 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'r' as i8, b'e' as i8, b'm' as i8, b'o' as i8,
                                    b'v' as i8, b'e' as i8, b'_' as i8, b'r' as i8, b'o' as i8,
                                    b'o' as i8, b't' as i8, b'(' as i8, b'v' as i8, b'o' as i8,
                                    b'i' as i8, b'd' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_6264: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'm' as i8,
                    b'o' as i8,
                    b'v' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'r' as i8,
                    b'o' as i8,
                    b'o' as i8,
                    b't' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_count_descendants() {
            printf(
                b"\n=== Testing Tree Count Descendants ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    267 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7037: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    268 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6983: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                2 as tree_id_t,
                b"grandchild1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 2, \"grandchild1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    269 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6929: {};
            if tree_add_node(
                tree,
                4 as tree_id_t,
                2 as tree_id_t,
                b"grandchild2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 4, 2, \"grandchild2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    270 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6875: {};
            if tree_add_node(
                tree,
                5 as tree_id_t,
                1 as tree_id_t,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 5, 1, \"child2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    271 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6821: {};
            if tree_count_descendants(tree, 1 as tree_id_t) == 4 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 1) == 4\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    273 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6775: {};
            if tree_count_descendants(tree, 2 as tree_id_t) == 2 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 2) == 2\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    274 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6729: {};
            if tree_count_descendants(tree, 3 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 3) == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    275 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6683: {};
            if tree_count_descendants(tree, 5 as tree_id_t) == 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 5) == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    276 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b't' as i8, b'_' as i8, b'd' as i8, b'e' as i8, b's' as i8,
                                    b'c' as i8, b'e' as i8, b'n' as i8, b'd' as i8, b'a' as i8,
                                    b'n' as i8, b't' as i8, b's' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_6637: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'c' as i8,
                    b'o' as i8,
                    b'u' as i8,
                    b'n' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b'd' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b'c' as i8,
                    b'e' as i8,
                    b'n' as i8,
                    b'd' as i8,
                    b'a' as i8,
                    b'n' as i8,
                    b't' as i8,
                    b's' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_find_path() {
            printf(
                b"\n=== Testing Tree Find Path ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    287 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7520: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    288 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7464: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                2 as tree_id_t,
                b"grandchild\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 2, \"grandchild\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    289 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7408: {};
            let mut path: [tree_id_t; 10] = [0; 10];
            let mut length: core::ffi::c_int = 0;
            length = tree_find_path(
                tree,
                3 as tree_id_t,
                path.as_mut_ptr(),
                10 as core::ffi::c_int,
            );
            if length == 3 as core::ffi::c_int {
            } else {
                __assert_fail(b"length == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    295 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7360: {};
            if path[0 as core::ffi::c_int as usize] == 1 as tree_id_t {
            } else {
                __assert_fail(b"path[0] == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    296 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7316: {};
            if path[1 as core::ffi::c_int as usize] == 2 as tree_id_t {
            } else {
                __assert_fail(b"path[1] == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    297 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7272: {};
            if path[2 as core::ffi::c_int as usize] == 3 as tree_id_t {
            } else {
                __assert_fail(b"path[2] == 3\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    298 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7228: {};
            length = tree_find_path(
                tree,
                1 as tree_id_t,
                path.as_mut_ptr(),
                10 as core::ffi::c_int,
            );
            if length == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"length == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    301 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7178: {};
            if path[0 as core::ffi::c_int as usize] == 1 as tree_id_t {
            } else {
                __assert_fail(b"path[0] == 1\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    302 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'f' as i8, b'i' as i8, b'n' as i8, b'd' as i8,
                                    b'_' as i8, b'p' as i8, b'a' as i8, b't' as i8, b'h' as i8,
                                    b'(' as i8, b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_7132: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'f' as i8,
                    b'i' as i8,
                    b'n' as i8,
                    b'd' as i8,
                    b'_' as i8,
                    b'p' as i8,
                    b'a' as i8,
                    b't' as i8,
                    b'h' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_duplicate_id() {
            printf(
                b"\n=== Testing Tree Duplicate ID ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    313 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'u' as i8, b'p' as i8, b'l' as i8,
                                    b'i' as i8, b'c' as i8, b'a' as i8, b't' as i8, b'e' as i8,
                                    b'_' as i8, b'i' as i8, b'd' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7760: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    314 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'u' as i8, b'p' as i8, b'l' as i8,
                                    b'i' as i8, b'c' as i8, b'a' as i8, b't' as i8, b'e' as i8,
                                    b'_' as i8, b'i' as i8, b'd' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7706: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"duplicate\0" as *const u8 as *const core::ffi::c_char,
            ) != 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"duplicate\") != 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    317 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'u' as i8, b'p' as i8, b'l' as i8,
                                    b'i' as i8, b'c' as i8, b'a' as i8, b't' as i8, b'e' as i8,
                                    b'_' as i8, b'i' as i8, b'd' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7650: {};
            if tree_size(tree) == 2 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 2\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    318 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'd' as i8, b'u' as i8, b'p' as i8, b'l' as i8,
                                    b'i' as i8, b'c' as i8, b'a' as i8, b't' as i8, b'e' as i8,
                                    b'_' as i8, b'i' as i8, b'd' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7606: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'd' as i8,
                    b'u' as i8,
                    b'p' as i8,
                    b'l' as i8,
                    b'i' as i8,
                    b'c' as i8,
                    b'a' as i8,
                    b't' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'i' as i8,
                    b'd' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_max_children() {
            printf(
                b"\n=== Testing Tree Max Children ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    329 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'm' as i8, b'a' as i8, b'x' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8026: {};
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < MAX_CHILDREN {
                if tree_add_node(
                    tree,
                    (i + 2 as core::ffi::c_int) as tree_id_t,
                    1 as tree_id_t,
                    b"child\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
                {
                } else {
                    __assert_fail(b"tree_add_node(tree, i + 2, 1, \"child\") == 0\0"
                                as *const u8 as *const core::ffi::c_char,
                        b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                                as *const u8 as *const core::ffi::c_char,
                        333 as core::ffi::c_uint,
                        ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                        b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                        b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                        b'_' as i8, b'm' as i8, b'a' as i8, b'x' as i8, b'_' as i8,
                                        b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                        b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                        b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                        b'\0' as i8]).as_ptr());
                }
                'c_7959: {};
                i += 1;
            }
            if tree_add_node(
                tree,
                (32 as core::ffi::c_int + 2 as core::ffi::c_int) as tree_id_t,
                1 as tree_id_t,
                b"overflow\0" as *const u8 as *const core::ffi::c_char,
            ) != 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, MAX_CHILDREN + 2, 1, \"overflow\") != 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    337 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'm' as i8, b'a' as i8, b'x' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7894: {};
            if tree_size(tree) == (32 as core::ffi::c_int + 1 as core::ffi::c_int) as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == MAX_CHILDREN + 1\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    338 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'm' as i8, b'a' as i8, b'x' as i8, b'_' as i8,
                                    b'c' as i8, b'h' as i8, b'i' as i8, b'l' as i8, b'd' as i8,
                                    b'r' as i8, b'e' as i8, b'n' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_7846: {};
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'm' as i8,
                    b'a' as i8,
                    b'x' as i8,
                    b'_' as i8,
                    b'c' as i8,
                    b'h' as i8,
                    b'i' as i8,
                    b'l' as i8,
                    b'd' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'n' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn test_tree_complex_structure() {
            printf(
                b"\n=== Testing Tree Complex Structure ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let tree: *mut tree_t = tree_create();
            if tree_add_node(
                tree,
                1 as tree_id_t,
                0 as tree_id_t,
                b"root\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 1, 0, \"root\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    359 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8844: {};
            if tree_add_node(
                tree,
                2 as tree_id_t,
                1 as tree_id_t,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 2, 1, \"child1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    360 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8790: {};
            if tree_add_node(
                tree,
                3 as tree_id_t,
                1 as tree_id_t,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 3, 1, \"child2\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    361 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8736: {};
            if tree_add_node(
                tree,
                4 as tree_id_t,
                1 as tree_id_t,
                b"child3\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 4, 1, \"child3\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    362 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8682: {};
            if tree_add_node(
                tree,
                5 as tree_id_t,
                2 as tree_id_t,
                b"gc1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 5, 2, \"gc1\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    363 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8628: {};
            if tree_add_node(
                tree,
                6 as tree_id_t,
                2 as tree_id_t,
                b"gc2\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 6, 2, \"gc2\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    364 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8574: {};
            if tree_add_node(
                tree,
                7 as tree_id_t,
                3 as tree_id_t,
                b"gc3\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 7, 3, \"gc3\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    365 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8520: {};
            if tree_add_node(
                tree,
                8 as tree_id_t,
                4 as tree_id_t,
                b"gc4\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 8, 4, \"gc4\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    366 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8466: {};
            if tree_add_node(
                tree,
                9 as tree_id_t,
                4 as tree_id_t,
                b"gc5\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 9, 4, \"gc5\") == 0\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    367 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8411: {};
            if tree_add_node(
                tree,
                10 as tree_id_t,
                7 as tree_id_t,
                b"ggc1\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
            } else {
                __assert_fail(b"tree_add_node(tree, 10, 7, \"ggc1\") == 0\0"
                            as *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    368 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8357: {};
            if tree_size(tree) == 10 as size_t {
            } else {
                __assert_fail(b"tree_size(tree) == 10\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    370 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8313: {};
            if tree_get_height(tree, 1 as tree_id_t) == 3 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_get_height(tree, 1) == 3\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    371 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8267: {};
            if tree_count_descendants(tree, 1 as tree_id_t) == 9 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 1) == 9\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    372 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8221: {};
            if tree_count_descendants(tree, 2 as tree_id_t) == 2 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 2) == 2\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    373 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8175: {};
            if tree_count_descendants(tree, 7 as tree_id_t) == 1 as core::ffi::c_int {
            } else {
                __assert_fail(b"tree_count_descendants(tree, 7) == 1\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_synthetic/hashmap-tree/src/hashmap-tree/test_case/src/main.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    374 as core::ffi::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'_' as i8, b'c' as i8, b'o' as i8, b'm' as i8, b'p' as i8,
                                    b'l' as i8, b'e' as i8, b'x' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'r' as i8, b'u' as i8, b'c' as i8, b't' as i8,
                                    b'u' as i8, b'r' as i8, b'e' as i8, b'(' as i8, b'v' as i8,
                                    b'o' as i8, b'i' as i8, b'd' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_8129: {};
            tree_print(tree);
            tree_delete(tree);
            printf(
                b"\xE2\x9C\x93 PASS: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ([
                    b't' as i8,
                    b'e' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'_' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'e' as i8,
                    b'_' as i8,
                    b'c' as i8,
                    b'o' as i8,
                    b'm' as i8,
                    b'p' as i8,
                    b'l' as i8,
                    b'e' as i8,
                    b'x' as i8,
                    b'_' as i8,
                    b's' as i8,
                    b't' as i8,
                    b'r' as i8,
                    b'u' as i8,
                    b'c' as i8,
                    b't' as i8,
                    b'u' as i8,
                    b'r' as i8,
                    b'e' as i8,
                    b'\0' as i8,
                ])
                .as_ptr(),
            );
        }
        unsafe fn main_0() -> core::ffi::c_int {
            printf(b"\xE2\x95\x94\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x97\n\0"
                        as *const u8 as *const core::ffi::c_char);
            printf(
                b"\xE2\x95\x91  TREE WITH HASHMAP ID MAPPING TESTS   \xE2\x95\x91\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\xE2\x95\x9A\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x9D\n\0"
                        as *const u8 as *const core::ffi::c_char);
            test_hashmap_basic();
            test_hashmap_collisions();
            test_tree_creation();
            test_tree_add_root();
            test_tree_add_children();
            test_tree_deep_hierarchy();
            test_tree_complex_structure();
            test_tree_remove_leaf();
            test_tree_remove_subtree();
            test_tree_remove_root();
            test_tree_count_descendants();
            test_tree_find_path();
            test_tree_duplicate_id();
            test_tree_max_children();
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  All tests passed successfully!\n\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
    pub mod tree {
        use crate::src::hashmap::hashmap_create;
        use crate::src::hashmap::hashmap_destroy;
        use crate::src::hashmap::hashmap_get;
        use crate::src::hashmap::hashmap_put;
        use crate::src::hashmap::hashmap_remove;
        use crate::src::hashmap::size_t;
        use crate::src::hashmap::tree_id_t;
        use crate::src::main::tree_node_t;
        use crate::src::main::tree_t;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
        }
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        pub type FILE = _IO_FILE;
        #[repr(C)]
        pub struct _IO_FILE {
            pub _flags: core::ffi::c_int,
            pub _IO_read_ptr: *mut core::ffi::c_char,
            pub _IO_read_end: *mut core::ffi::c_char,
            pub _IO_read_base: *mut core::ffi::c_char,
            pub _IO_write_base: *mut core::ffi::c_char,
            pub _IO_write_ptr: *mut core::ffi::c_char,
            pub _IO_write_end: *mut core::ffi::c_char,
            pub _IO_buf_base: *mut core::ffi::c_char,
            pub _IO_buf_end: *mut core::ffi::c_char,
            pub _IO_save_base: *mut core::ffi::c_char,
            pub _IO_backup_base: *mut core::ffi::c_char,
            pub _IO_save_end: *mut core::ffi::c_char,
            pub _markers: *mut _IO_marker,
            pub _chain: *mut _IO_FILE,
            pub _fileno: core::ffi::c_int,
            pub _flags2: core::ffi::c_int,
            pub _old_offset: __off_t,
            pub _cur_column: core::ffi::c_ushort,
            pub _vtable_offset: core::ffi::c_schar,
            pub _shortbuf: [core::ffi::c_char; 1],
            pub _lock: *mut core::ffi::c_void,
            pub _offset: __off64_t,
            pub _codecvt: *mut _IO_codecvt,
            pub _wide_data: *mut _IO_wide_data,
            pub _freeres_list: *mut _IO_FILE,
            pub _freeres_buf: *mut core::ffi::c_void,
            pub __pad5: size_t,
            pub _mode: core::ffi::c_int,
            pub _unused2: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for _IO_FILE {}
        #[automatically_derived]
        impl ::core::clone::Clone for _IO_FILE {
            #[inline]
            fn clone(&self) -> _IO_FILE {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_marker>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_ushort>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_schar>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 1]>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<__off64_t>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_codecvt>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_wide_data>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        pub type _IO_lock_t = ();
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_CHILDREN: core::ffi::c_int = 32 as core::ffi::c_int;
        pub const MAX_DATA_LENGTH: core::ffi::c_int = 256 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn tree_create() -> *mut tree_t {
            let tree: *mut tree_t =
                malloc(::core::mem::size_of::<tree_t>() as size_t) as *mut tree_t;
            if tree.is_null() {
                return std::ptr::null_mut::<tree_t>();
            }
            (*tree).node_map = hashmap_create();
            if ((*tree).node_map).is_null() {
                free(tree as *mut core::ffi::c_void);
                return std::ptr::null_mut::<tree_t>();
            }
            (*tree).root_id = 0 as tree_id_t;
            (*tree).has_root = 0 as core::ffi::c_int;
            (*tree).node_count = 0 as size_t;
            tree
        }
        unsafe extern "C" fn tree_free_node(node: *mut tree_node_t) {
            if !node.is_null() {
                free(node as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_delete(tree: *mut tree_t) {
            if tree.is_null() {
                return;
            }
            let mut i: size_t = 0 as size_t;
            while i < (*(*tree).node_map).capacity {
                if (*((*(*tree).node_map).entries).add(i)).occupied != 0
                    && (*((*(*tree).node_map).entries).add(i)).deleted == 0
                {
                    tree_free_node(
                        (*((*(*tree).node_map).entries).add(i)).value as *mut tree_node_t,
                    );
                }
                i = i.wrapping_add(1);
            }
            hashmap_destroy((*tree).node_map);
            free(tree as *mut core::ffi::c_void);
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_add_node(
            tree: *mut tree_t,
            id: tree_id_t,
            parent_id: tree_id_t,
            data: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if tree.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if tree_contains(tree, id) != 0 {
                fprintf(
                    stderr,
                    b"Error: Node with ID %lu already exists\n\0" as *const u8
                        as *const core::ffi::c_char,
                    id,
                );
                return -(1 as core::ffi::c_int);
            }
            let node: *mut tree_node_t =
                malloc(::core::mem::size_of::<tree_node_t>() as size_t) as *mut tree_node_t;
            if node.is_null() {
                fprintf(
                    stderr,
                    b"Error: Failed to allocate node\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            (*node).id = id;
            (*node).parent_id = parent_id;
            (*node).child_count = 0 as core::ffi::c_int;
            if !data.is_null() {
                strncpy(
                    ((*node).data).as_mut_ptr(),
                    data,
                    (MAX_DATA_LENGTH - 1 as core::ffi::c_int) as size_t,
                );
                (*node).data[(MAX_DATA_LENGTH - 1 as core::ffi::c_int) as usize] =
                    '\0' as i32 as core::ffi::c_char;
            } else {
                (*node).data[0 as core::ffi::c_int as usize] = '\0' as i32 as core::ffi::c_char;
            }
            if (*tree).has_root == 0 {
                (*tree).root_id = id;
                (*tree).has_root = 1 as core::ffi::c_int;
                (*node).parent_id = 0 as tree_id_t;
            } else {
                let parent: *mut tree_node_t = tree_get_node(tree, parent_id);
                if parent.is_null() {
                    fprintf(
                        stderr,
                        b"Error: Parent node %lu not found\n\0" as *const u8
                            as *const core::ffi::c_char,
                        parent_id,
                    );
                    free(node as *mut core::ffi::c_void);
                    return -(1 as core::ffi::c_int);
                }
                if (*parent).child_count >= MAX_CHILDREN {
                    fprintf(
                        stderr,
                        b"Error: Parent has maximum children\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    free(node as *mut core::ffi::c_void);
                    return -(1 as core::ffi::c_int);
                }
                let fresh0 = (*parent).child_count;
                (*parent).child_count += 1;
                (*parent).child_ids[fresh0 as usize] = id;
            }
            if hashmap_put((*tree).node_map, id, node as *mut core::ffi::c_void)
                != 0 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error: Failed to add node to hashmap\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                free(node as *mut core::ffi::c_void);
                return -(1 as core::ffi::c_int);
            }
            (*tree).node_count = ((*tree).node_count).wrapping_add(1);
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn tree_remove_subtree(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> core::ffi::c_int {
            let node: *mut tree_node_t = tree_get_node(tree, id);
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*node).child_count {
                tree_remove_subtree(tree, (*node).child_ids[i as usize]);
                i += 1;
            }
            let removed: *mut tree_node_t =
                hashmap_remove((*tree).node_map, id) as *mut tree_node_t;
            if !removed.is_null() {
                tree_free_node(removed);
                (*tree).node_count = ((*tree).node_count).wrapping_sub(1);
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_remove_node(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> core::ffi::c_int {
            if tree.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut tree_node_t = tree_get_node(tree, id);
            if node.is_null() {
                fprintf(
                    stderr,
                    b"Error: Node %lu not found\n\0" as *const u8 as *const core::ffi::c_char,
                    id,
                );
                return -(1 as core::ffi::c_int);
            }
            if id == (*tree).root_id {
                tree_remove_subtree(tree, id);
                (*tree).has_root = 0 as core::ffi::c_int;
                (*tree).root_id = 0 as tree_id_t;
                return 0 as core::ffi::c_int;
            }
            let parent: *mut tree_node_t = tree_get_node(tree, (*node).parent_id);
            if !parent.is_null() {
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < (*parent).child_count {
                    if (*parent).child_ids[i as usize] == id {
                        let mut j: core::ffi::c_int = i;
                        while j < (*parent).child_count - 1 as core::ffi::c_int {
                            (*parent).child_ids[j as usize] =
                                (*parent).child_ids[(j + 1 as core::ffi::c_int) as usize];
                            j += 1;
                        }
                        (*parent).child_count -= 1;
                        break;
                    } else {
                        i += 1;
                    }
                }
            }
            tree_remove_subtree(tree, id);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_get_node(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> *mut tree_node_t {
            if tree.is_null() {
                return std::ptr::null_mut::<tree_node_t>();
            }
            hashmap_get((*tree).node_map, id) as *mut tree_node_t
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_contains(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> core::ffi::c_int {
            (tree_get_node(tree, id) != NULL as *mut tree_node_t) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_size(tree: *mut tree_t) -> size_t {
            if !tree.is_null() {
                (*tree).node_count
            } else {
                0 as size_t
            }
        }
        unsafe extern "C" fn tree_print_helper(
            tree: *mut tree_t,
            id: tree_id_t,
            depth: core::ffi::c_int,
        ) {
            let node: *mut tree_node_t = tree_get_node(tree, id);
            if node.is_null() {
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < depth {
                printf(b"  \0" as *const u8 as *const core::ffi::c_char);
                i += 1;
            }
            printf(
                b"[%lu] %s\n\0" as *const u8 as *const core::ffi::c_char,
                (*node).id,
                ((*node).data).as_ptr(),
            );
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < (*node).child_count {
                tree_print_helper(
                    tree,
                    (*node).child_ids[i_0 as usize],
                    depth + 1 as core::ffi::c_int,
                );
                i_0 += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_print(tree: *mut tree_t) {
            if tree.is_null() || (*tree).has_root == 0 {
                printf(b"(empty tree)\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            tree_print_helper(tree, (*tree).root_id, 0 as core::ffi::c_int);
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_get_depth(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> core::ffi::c_int {
            if tree.is_null() || tree_contains(tree, id) == 0 {
                return -(1 as core::ffi::c_int);
            }
            let mut depth: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut current_id: tree_id_t = id;
            while current_id != (*tree).root_id {
                let node: *mut tree_node_t = tree_get_node(tree, current_id);
                if node.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                current_id = (*node).parent_id;
                depth += 1;
            }
            depth
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_get_height(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> core::ffi::c_int {
            let node: *mut tree_node_t = tree_get_node(tree, id);
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if (*node).child_count == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            let mut max_height: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*node).child_count {
                let child_height: core::ffi::c_int =
                    tree_get_height(tree, (*node).child_ids[i as usize]);
                if child_height > max_height {
                    max_height = child_height;
                }
                i += 1;
            }
            max_height + 1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_count_descendants(
            tree: *mut tree_t,
            id: tree_id_t,
        ) -> core::ffi::c_int {
            let node: *mut tree_node_t = tree_get_node(tree, id);
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*node).child_count {
                count += 1;
                count += tree_count_descendants(tree, (*node).child_ids[i as usize]);
                i += 1;
            }
            count
        }
        #[no_mangle]
        pub unsafe extern "C" fn tree_find_path(
            tree: *mut tree_t,
            id: tree_id_t,
            path: *mut tree_id_t,
            max_length: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if tree.is_null() || path.is_null() || tree_contains(tree, id) == 0 {
                return -(1 as core::ffi::c_int);
            }
            let mut temp_path: [tree_id_t; 1000] = [0; 1000];
            let mut length: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut current_id: tree_id_t = id;
            while length < 1000 as core::ffi::c_int {
                let fresh1 = length;
                length += 1;
                temp_path[fresh1 as usize] = current_id;
                if current_id == (*tree).root_id {
                    break;
                }
                let node: *mut tree_node_t = tree_get_node(tree, current_id);
                if node.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                current_id = (*node).parent_id;
            }
            if length > max_length {
                length = max_length;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < length {
                *path.offset(i as isize) = temp_path[(length - 1 as core::ffi::c_int - i) as usize];
                i += 1;
            }
            length
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("hashmap-tree", SOURCE);
}
