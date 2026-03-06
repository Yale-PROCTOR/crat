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
    pub mod inventory {
        extern "C" {
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct item_t {
            pub id: core::ffi::c_int,
            pub name: [core::ffi::c_char; 64],
            pub category: [core::ffi::c_char; 32],
            pub price: core::ffi::c_double,
            pub quantity: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for item_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for item_t {
            #[inline]
            fn clone(&self) -> item_t {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 64]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct order_t {
            pub customer_id: core::ffi::c_int,
            pub customer_name: [core::ffi::c_char; 64],
            pub total_amount: core::ffi::c_double,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for order_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for order_t {
            #[inline]
            fn clone(&self) -> order_t {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 64]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                *self
            }
        }
        #[repr(C)]
        pub struct array_int_t {
            pub data: *mut core::ffi::c_int,
            pub size: size_t,
            pub capacity: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for array_int_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for array_int_t {
            #[inline]
            fn clone(&self) -> array_int_t {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct array_double_t {
            pub data: *mut core::ffi::c_double,
            pub size: size_t,
            pub capacity: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for array_double_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for array_double_t {
            #[inline]
            fn clone(&self) -> array_double_t {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct array_item_t_t {
            pub data: *mut item_t,
            pub size: size_t,
            pub capacity: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for array_item_t_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for array_item_t_t {
            #[inline]
            fn clone(&self) -> array_item_t_t {
                let _: ::core::clone::AssertParamIsClone<*mut item_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct array_order_t_t {
            pub data: *mut order_t,
            pub size: size_t,
            pub capacity: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for array_order_t_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for array_order_t_t {
            #[inline]
            fn clone(&self) -> array_order_t_t {
                let _: ::core::clone::AssertParamIsClone<*mut order_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct list_node_int {
            pub data: core::ffi::c_int,
            pub next: *mut list_node_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_node_int {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_node_int {
            #[inline]
            fn clone(&self) -> list_node_int {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_int>;
                *self
            }
        }
        pub type list_node_int_t = list_node_int;
        #[repr(C)]
        pub struct list_int_t {
            pub head: *mut list_node_int_t,
            pub tail: *mut list_node_int_t,
            pub size: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_int_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_int_t {
            #[inline]
            fn clone(&self) -> list_int_t {
                let _: ::core::clone::AssertParamIsClone<*mut list_node_int_t>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_int_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct list_node_double {
            pub data: core::ffi::c_double,
            pub next: *mut list_node_double,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_node_double {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_node_double {
            #[inline]
            fn clone(&self) -> list_node_double {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_double>;
                *self
            }
        }
        pub type list_node_double_t = list_node_double;
        #[repr(C)]
        pub struct list_double_t {
            pub head: *mut list_node_double_t,
            pub tail: *mut list_node_double_t,
            pub size: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_double_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_double_t {
            #[inline]
            fn clone(&self) -> list_double_t {
                let _: ::core::clone::AssertParamIsClone<*mut list_node_double_t>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_double_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct list_node_item_t {
            pub data: item_t,
            pub next: *mut list_node_item_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_node_item_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_node_item_t {
            #[inline]
            fn clone(&self) -> list_node_item_t {
                let _: ::core::clone::AssertParamIsClone<item_t>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_item_t>;
                *self
            }
        }
        pub type list_node_item_t_t = list_node_item_t;
        #[repr(C)]
        pub struct list_item_t_t {
            pub head: *mut list_node_item_t_t,
            pub tail: *mut list_node_item_t_t,
            pub size: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_item_t_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_item_t_t {
            #[inline]
            fn clone(&self) -> list_item_t_t {
                let _: ::core::clone::AssertParamIsClone<*mut list_node_item_t_t>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_item_t_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct list_node_order_t {
            pub data: order_t,
            pub next: *mut list_node_order_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_node_order_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_node_order_t {
            #[inline]
            fn clone(&self) -> list_node_order_t {
                let _: ::core::clone::AssertParamIsClone<order_t>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_order_t>;
                *self
            }
        }
        pub type list_node_order_t_t = list_node_order_t;
        #[repr(C)]
        pub struct list_order_t_t {
            pub head: *mut list_node_order_t_t,
            pub tail: *mut list_node_order_t_t,
            pub size: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for list_order_t_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for list_order_t_t {
            #[inline]
            fn clone(&self) -> list_order_t_t {
                let _: ::core::clone::AssertParamIsClone<*mut list_node_order_t_t>;
                let _: ::core::clone::AssertParamIsClone<*mut list_node_order_t_t>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_NAME_LENGTH: core::ffi::c_int = 64 as core::ffi::c_int;
        pub const MAX_CATEGORY_LENGTH: core::ffi::c_int = 32 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn array_int_create(initial_capacity: size_t) -> *mut array_int_t {
            let arr: *mut array_int_t =
                malloc(::core::mem::size_of::<array_int_t>() as size_t) as *mut array_int_t;
            if arr.is_null() {
                return std::ptr::null_mut::<array_int_t>();
            }
            (*arr).capacity = if initial_capacity > 0 as size_t {
                initial_capacity
            } else {
                16 as size_t
            };
            (*arr).size = 0 as size_t;
            (*arr).data = malloc(
                (::core::mem::size_of::<core::ffi::c_int>() as size_t)
                    .wrapping_mul((*arr).capacity),
            ) as *mut core::ffi::c_int;
            if ((*arr).data).is_null() {
                free(arr as *mut core::ffi::c_void);
                return std::ptr::null_mut::<array_int_t>();
            }
            arr
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_int_destroy(arr: *mut array_int_t) {
            if !arr.is_null() {
                free((*arr).data as *mut core::ffi::c_void);
                free(arr as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_int_size(arr: *mut array_int_t) -> size_t {
            if !arr.is_null() {
                (*arr).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_int_clear(arr: *mut array_int_t) {
            if !arr.is_null() {
                (*arr).size = 0 as size_t;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_int_push(
            arr: *mut array_int_t,
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if arr.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if (*arr).size >= (*arr).capacity {
                let new_capacity: size_t = ((*arr).capacity).wrapping_mul(2 as size_t);
                let new_data: *mut core::ffi::c_int = realloc(
                    (*arr).data as *mut core::ffi::c_void,
                    (::core::mem::size_of::<core::ffi::c_int>() as size_t)
                        .wrapping_mul(new_capacity),
                ) as *mut core::ffi::c_int;
                if new_data.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                (*arr).data = new_data;
                (*arr).capacity = new_capacity;
            }
            let fresh0 = (*arr).size;
            (*arr).size = ((*arr).size).wrapping_add(1);
            *((*arr).data).add(fresh0) = value;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_int_get(
            arr: *mut array_int_t,
            index: size_t,
        ) -> core::ffi::c_int {
            *((*arr).data).add(index)
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_double_destroy(arr: *mut array_double_t) {
            if !arr.is_null() {
                free((*arr).data as *mut core::ffi::c_void);
                free(arr as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_double_size(arr: *mut array_double_t) -> size_t {
            if !arr.is_null() {
                (*arr).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_double_clear(arr: *mut array_double_t) {
            if !arr.is_null() {
                (*arr).size = 0 as size_t;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_double_create(
            initial_capacity: size_t,
        ) -> *mut array_double_t {
            let arr: *mut array_double_t =
                malloc(::core::mem::size_of::<array_double_t>() as size_t) as *mut array_double_t;
            if arr.is_null() {
                return std::ptr::null_mut::<array_double_t>();
            }
            (*arr).capacity = if initial_capacity > 0 as size_t {
                initial_capacity
            } else {
                16 as size_t
            };
            (*arr).size = 0 as size_t;
            (*arr).data = malloc(
                (::core::mem::size_of::<core::ffi::c_double>() as size_t)
                    .wrapping_mul((*arr).capacity),
            ) as *mut core::ffi::c_double;
            if ((*arr).data).is_null() {
                free(arr as *mut core::ffi::c_void);
                return std::ptr::null_mut::<array_double_t>();
            }
            arr
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_double_push(
            arr: *mut array_double_t,
            value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            if arr.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if (*arr).size >= (*arr).capacity {
                let new_capacity: size_t = ((*arr).capacity).wrapping_mul(2 as size_t);
                let new_data: *mut core::ffi::c_double = realloc(
                    (*arr).data as *mut core::ffi::c_void,
                    (::core::mem::size_of::<core::ffi::c_double>() as size_t)
                        .wrapping_mul(new_capacity),
                )
                    as *mut core::ffi::c_double;
                if new_data.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                (*arr).data = new_data;
                (*arr).capacity = new_capacity;
            }
            let fresh1 = (*arr).size;
            (*arr).size = ((*arr).size).wrapping_add(1);
            *((*arr).data).add(fresh1) = value;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_double_get(
            arr: *mut array_double_t,
            index: size_t,
        ) -> core::ffi::c_double {
            *((*arr).data).add(index)
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_item_t_size(arr: *mut array_item_t_t) -> size_t {
            if !arr.is_null() {
                (*arr).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_item_t_create(
            initial_capacity: size_t,
        ) -> *mut array_item_t_t {
            let arr: *mut array_item_t_t =
                malloc(::core::mem::size_of::<array_item_t_t>() as size_t) as *mut array_item_t_t;
            if arr.is_null() {
                return std::ptr::null_mut::<array_item_t_t>();
            }
            (*arr).capacity = if initial_capacity > 0 as size_t {
                initial_capacity
            } else {
                16 as size_t
            };
            (*arr).size = 0 as size_t;
            (*arr).data =
                malloc((::core::mem::size_of::<item_t>() as size_t).wrapping_mul((*arr).capacity))
                    as *mut item_t;
            if ((*arr).data).is_null() {
                free(arr as *mut core::ffi::c_void);
                return std::ptr::null_mut::<array_item_t_t>();
            }
            arr
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_item_t_destroy(arr: *mut array_item_t_t) {
            if !arr.is_null() {
                free((*arr).data as *mut core::ffi::c_void);
                free(arr as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_item_t_push(
            arr: *mut array_item_t_t,
            value: item_t,
        ) -> core::ffi::c_int {
            if arr.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if (*arr).size >= (*arr).capacity {
                let new_capacity: size_t = ((*arr).capacity).wrapping_mul(2 as size_t);
                let new_data: *mut item_t = realloc(
                    (*arr).data as *mut core::ffi::c_void,
                    (::core::mem::size_of::<item_t>() as size_t).wrapping_mul(new_capacity),
                ) as *mut item_t;
                if new_data.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                (*arr).data = new_data;
                (*arr).capacity = new_capacity;
            }
            let fresh2 = (*arr).size;
            (*arr).size = ((*arr).size).wrapping_add(1);
            *((*arr).data).add(fresh2) = value;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_item_t_clear(arr: *mut array_item_t_t) {
            if !arr.is_null() {
                (*arr).size = 0 as size_t;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_item_t_get(
            arr: *mut array_item_t_t,
            index: size_t,
        ) -> item_t {
            *((*arr).data).add(index)
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_order_t_size(arr: *mut array_order_t_t) -> size_t {
            if !arr.is_null() {
                (*arr).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_order_t_clear(arr: *mut array_order_t_t) {
            if !arr.is_null() {
                (*arr).size = 0 as size_t;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_order_t_push(
            arr: *mut array_order_t_t,
            value: order_t,
        ) -> core::ffi::c_int {
            if arr.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if (*arr).size >= (*arr).capacity {
                let new_capacity: size_t = ((*arr).capacity).wrapping_mul(2 as size_t);
                let new_data: *mut order_t = realloc(
                    (*arr).data as *mut core::ffi::c_void,
                    (::core::mem::size_of::<order_t>() as size_t).wrapping_mul(new_capacity),
                ) as *mut order_t;
                if new_data.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                (*arr).data = new_data;
                (*arr).capacity = new_capacity;
            }
            let fresh3 = (*arr).size;
            (*arr).size = ((*arr).size).wrapping_add(1);
            *((*arr).data).add(fresh3) = value;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_order_t_destroy(arr: *mut array_order_t_t) {
            if !arr.is_null() {
                free((*arr).data as *mut core::ffi::c_void);
                free(arr as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_order_t_create(
            initial_capacity: size_t,
        ) -> *mut array_order_t_t {
            let arr: *mut array_order_t_t =
                malloc(::core::mem::size_of::<array_order_t_t>() as size_t) as *mut array_order_t_t;
            if arr.is_null() {
                return std::ptr::null_mut::<array_order_t_t>();
            }
            (*arr).capacity = if initial_capacity > 0 as size_t {
                initial_capacity
            } else {
                16 as size_t
            };
            (*arr).size = 0 as size_t;
            (*arr).data =
                malloc((::core::mem::size_of::<order_t>() as size_t).wrapping_mul((*arr).capacity))
                    as *mut order_t;
            if ((*arr).data).is_null() {
                free(arr as *mut core::ffi::c_void);
                return std::ptr::null_mut::<array_order_t_t>();
            }
            arr
        }
        #[no_mangle]
        pub unsafe extern "C" fn array_order_t_get(
            arr: *mut array_order_t_t,
            index: size_t,
        ) -> order_t {
            *((*arr).data).add(index)
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_int_prepend(
            list: *mut list_int_t,
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_int_t =
                malloc(::core::mem::size_of::<list_node_int_t>() as size_t) as *mut list_node_int_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = (*list).head as *mut list_node_int;
            (*list).head = node;
            if ((*list).tail).is_null() {
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_int_create() -> *mut list_int_t {
            let list: *mut list_int_t =
                malloc(::core::mem::size_of::<list_int_t>() as size_t) as *mut list_int_t;
            if list.is_null() {
                return std::ptr::null_mut::<list_int_t>();
            }
            (*list).head = std::ptr::null_mut::<list_node_int_t>();
            (*list).tail = std::ptr::null_mut::<list_node_int_t>();
            (*list).size = 0 as size_t;
            list
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_int_clear(list: *mut list_int_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_int_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_int_t = (*current).next as *mut list_node_int_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            (*list).tail = std::ptr::null_mut::<list_node_int_t>();
            (*list).head = (*list).tail;
            (*list).size = 0 as size_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_int_size(list: *mut list_int_t) -> size_t {
            if !list.is_null() {
                (*list).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_int_append(
            list: *mut list_int_t,
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_int_t =
                malloc(::core::mem::size_of::<list_node_int_t>() as size_t) as *mut list_node_int_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = std::ptr::null_mut::<list_node_int>();
            if ((*list).head).is_null() {
                (*list).tail = node;
                (*list).head = (*list).tail;
            } else {
                (*(*list).tail).next = node as *mut list_node_int;
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_int_destroy(list: *mut list_int_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_int_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_int_t = (*current).next as *mut list_node_int_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            free(list as *mut core::ffi::c_void);
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_double_clear(list: *mut list_double_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_double_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_double_t = (*current).next as *mut list_node_double_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            (*list).tail = std::ptr::null_mut::<list_node_double_t>();
            (*list).head = (*list).tail;
            (*list).size = 0 as size_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_double_prepend(
            list: *mut list_double_t,
            value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_double_t =
                malloc(::core::mem::size_of::<list_node_double_t>() as size_t)
                    as *mut list_node_double_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = (*list).head as *mut list_node_double;
            (*list).head = node;
            if ((*list).tail).is_null() {
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_double_size(list: *mut list_double_t) -> size_t {
            if !list.is_null() {
                (*list).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_double_append(
            list: *mut list_double_t,
            value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_double_t =
                malloc(::core::mem::size_of::<list_node_double_t>() as size_t)
                    as *mut list_node_double_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = std::ptr::null_mut::<list_node_double>();
            if ((*list).head).is_null() {
                (*list).tail = node;
                (*list).head = (*list).tail;
            } else {
                (*(*list).tail).next = node as *mut list_node_double;
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_double_destroy(list: *mut list_double_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_double_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_double_t = (*current).next as *mut list_node_double_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            free(list as *mut core::ffi::c_void);
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_double_create() -> *mut list_double_t {
            let list: *mut list_double_t =
                malloc(::core::mem::size_of::<list_double_t>() as size_t) as *mut list_double_t;
            if list.is_null() {
                return std::ptr::null_mut::<list_double_t>();
            }
            (*list).head = std::ptr::null_mut::<list_node_double_t>();
            (*list).tail = std::ptr::null_mut::<list_node_double_t>();
            (*list).size = 0 as size_t;
            list
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_item_t_destroy(list: *mut list_item_t_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_item_t_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_item_t_t = (*current).next as *mut list_node_item_t_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            free(list as *mut core::ffi::c_void);
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_item_t_prepend(
            list: *mut list_item_t_t,
            value: item_t,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_item_t_t =
                malloc(::core::mem::size_of::<list_node_item_t_t>() as size_t)
                    as *mut list_node_item_t_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = (*list).head as *mut list_node_item_t;
            (*list).head = node;
            if ((*list).tail).is_null() {
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_item_t_size(list: *mut list_item_t_t) -> size_t {
            if !list.is_null() {
                (*list).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_item_t_clear(list: *mut list_item_t_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_item_t_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_item_t_t = (*current).next as *mut list_node_item_t_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            (*list).tail = std::ptr::null_mut::<list_node_item_t_t>();
            (*list).head = (*list).tail;
            (*list).size = 0 as size_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_item_t_create() -> *mut list_item_t_t {
            let list: *mut list_item_t_t =
                malloc(::core::mem::size_of::<list_item_t_t>() as size_t) as *mut list_item_t_t;
            if list.is_null() {
                return std::ptr::null_mut::<list_item_t_t>();
            }
            (*list).head = std::ptr::null_mut::<list_node_item_t_t>();
            (*list).tail = std::ptr::null_mut::<list_node_item_t_t>();
            (*list).size = 0 as size_t;
            list
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_item_t_append(
            list: *mut list_item_t_t,
            value: item_t,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_item_t_t =
                malloc(::core::mem::size_of::<list_node_item_t_t>() as size_t)
                    as *mut list_node_item_t_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = std::ptr::null_mut::<list_node_item_t>();
            if ((*list).head).is_null() {
                (*list).tail = node;
                (*list).head = (*list).tail;
            } else {
                (*(*list).tail).next = node as *mut list_node_item_t;
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_order_t_create() -> *mut list_order_t_t {
            let list: *mut list_order_t_t =
                malloc(::core::mem::size_of::<list_order_t_t>() as size_t) as *mut list_order_t_t;
            if list.is_null() {
                return std::ptr::null_mut::<list_order_t_t>();
            }
            (*list).head = std::ptr::null_mut::<list_node_order_t_t>();
            (*list).tail = std::ptr::null_mut::<list_node_order_t_t>();
            (*list).size = 0 as size_t;
            list
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_order_t_destroy(list: *mut list_order_t_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_order_t_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_order_t_t = (*current).next as *mut list_node_order_t_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            free(list as *mut core::ffi::c_void);
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_order_t_append(
            list: *mut list_order_t_t,
            value: order_t,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_order_t_t =
                malloc(::core::mem::size_of::<list_node_order_t_t>() as size_t)
                    as *mut list_node_order_t_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = std::ptr::null_mut::<list_node_order_t>();
            if ((*list).head).is_null() {
                (*list).tail = node;
                (*list).head = (*list).tail;
            } else {
                (*(*list).tail).next = node as *mut list_node_order_t;
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_order_t_prepend(
            list: *mut list_order_t_t,
            value: order_t,
        ) -> core::ffi::c_int {
            if list.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut list_node_order_t_t =
                malloc(::core::mem::size_of::<list_node_order_t_t>() as size_t)
                    as *mut list_node_order_t_t;
            if node.is_null() {
                return -(1 as core::ffi::c_int);
            }
            (*node).data = value;
            (*node).next = (*list).head as *mut list_node_order_t;
            (*list).head = node;
            if ((*list).tail).is_null() {
                (*list).tail = node;
            }
            (*list).size = ((*list).size).wrapping_add(1);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_order_t_size(list: *mut list_order_t_t) -> size_t {
            if !list.is_null() {
                (*list).size
            } else {
                0 as size_t
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_order_t_clear(list: *mut list_order_t_t) {
            if list.is_null() {
                return;
            }
            let mut current: *mut list_node_order_t_t = (*list).head;
            while !current.is_null() {
                let next: *mut list_node_order_t_t = (*current).next as *mut list_node_order_t_t;
                free(current as *mut core::ffi::c_void);
                current = next;
            }
            (*list).tail = std::ptr::null_mut::<list_node_order_t_t>();
            (*list).head = (*list).tail;
            (*list).size = 0 as size_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_item(item: item_t) {
            printf(
                b"  [%d] %s\n\0" as *const u8 as *const core::ffi::c_char,
                item.id,
                (item.name).as_ptr(),
            );
            printf(
                b"      Category: %s\n\0" as *const u8 as *const core::ffi::c_char,
                (item.category).as_ptr(),
            );
            printf(
                b"      Price: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                item.price,
            );
            printf(
                b"      Quantity: %d\n\0" as *const u8 as *const core::ffi::c_char,
                item.quantity,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_order(order: order_t) {
            printf(
                b"  Order - Customer ID: %d, Name: %s\n\0" as *const u8 as *const core::ffi::c_char,
                order.customer_id,
                (order.customer_name).as_ptr(),
            );
            printf(
                b"          Total: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                order.total_amount,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn create_item(
            id: core::ffi::c_int,
            name: *const core::ffi::c_char,
            category: *const core::ffi::c_char,
            price: core::ffi::c_double,
            quantity: core::ffi::c_int,
        ) -> item_t {
            let mut item: item_t = item_t {
                id: 0,
                name: [0; 64],
                category: [0; 32],
                price: 0.,
                quantity: 0,
            };
            item.id = id;
            strncpy(
                (item.name).as_mut_ptr(),
                name,
                (MAX_NAME_LENGTH - 1 as core::ffi::c_int) as size_t,
            );
            item.name[(MAX_NAME_LENGTH - 1 as core::ffi::c_int) as usize] =
                '\0' as i32 as core::ffi::c_char;
            strncpy(
                (item.category).as_mut_ptr(),
                category,
                (MAX_CATEGORY_LENGTH - 1 as core::ffi::c_int) as size_t,
            );
            item.category[(MAX_CATEGORY_LENGTH - 1 as core::ffi::c_int) as usize] =
                '\0' as i32 as core::ffi::c_char;
            item.price = price;
            item.quantity = quantity;
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn create_order(
            customer_id: core::ffi::c_int,
            customer_name: *const core::ffi::c_char,
            total_amount: core::ffi::c_double,
        ) -> order_t {
            let mut order: order_t = order_t {
                customer_id: 0,
                customer_name: [0; 64],
                total_amount: 0.,
            };
            order.customer_id = customer_id;
            strncpy(
                (order.customer_name).as_mut_ptr(),
                customer_name,
                (MAX_NAME_LENGTH - 1 as core::ffi::c_int) as size_t,
            );
            order.customer_name[(MAX_NAME_LENGTH - 1 as core::ffi::c_int) as usize] =
                '\0' as i32 as core::ffi::c_char;
            order.total_amount = total_amount;
            order
        }
        #[no_mangle]
        pub unsafe extern "C" fn calculate_inventory_stats(items: *mut array_item_t_t) {
            if items.is_null() || (*items).size == 0 as size_t {
                printf(b"No items in inventory\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"\n=== Inventory Statistics (Array) ===\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let mut total_value: core::ffi::c_double = 0.0f64;
            let mut total_items: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut max_price: core::ffi::c_double = 0.0f64;
            let mut min_price: core::ffi::c_double =
                (*((*items).data).offset(0 as core::ffi::c_int as isize)).price;
            let mut item: item_t = item_t {
                id: 0,
                name: [0; 64],
                category: [0; 32],
                price: 0.,
                quantity: 0,
            };
            let mut _i: size_t = 0 as size_t;
            while _i < (*items).size && {
                item = *((*items).data).add(_i);
                1 as core::ffi::c_int != 0
            } {
                total_value += item.price * item.quantity as core::ffi::c_double;
                total_items += item.quantity;
                if item.price > max_price {
                    max_price = item.price;
                }
                if item.price < min_price {
                    min_price = item.price;
                }
                _i = _i.wrapping_add(1);
            }
            printf(
                b"Total unique items: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                (*items).size,
            );
            printf(
                b"Total item count: %d\n\0" as *const u8 as *const core::ffi::c_char,
                total_items,
            );
            printf(
                b"Total inventory value: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                total_value,
            );
            printf(
                b"Average item price: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                total_value / total_items as core::ffi::c_double,
            );
            printf(
                b"Most expensive item: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                max_price,
            );
            printf(
                b"Least expensive item: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                min_price,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn calculate_order_stats(orders: *mut list_order_t_t) {
            if orders.is_null() || (*orders).size == 0 as size_t {
                printf(b"No orders to analyze\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"\n=== Order Statistics (List) ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let mut total_revenue: core::ffi::c_double = 0.0f64;
            let mut max_order: core::ffi::c_double = 0.0f64;
            let mut min_order: core::ffi::c_double = -1.0f64;
            let mut order: order_t = order_t {
                customer_id: 0,
                customer_name: [0; 64],
                total_amount: 0.,
            };
            let mut _node: *mut list_node_order_t_t = (*orders).head;
            while !_node.is_null() && {
                order = (*_node).data;
                1 as core::ffi::c_int != 0
            } {
                total_revenue += order.total_amount;
                if order.total_amount > max_order {
                    max_order = order.total_amount;
                }
                if min_order < 0 as core::ffi::c_int as core::ffi::c_double
                    || order.total_amount < min_order
                {
                    min_order = order.total_amount;
                }
                _node = (*_node).next as *mut list_node_order_t_t;
            }
            printf(
                b"Total orders: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                (*orders).size,
            );
            printf(
                b"Total revenue: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                total_revenue,
            );
            printf(
                b"Average order value: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                total_revenue / (*orders).size as core::ffi::c_double,
            );
            printf(
                b"Largest order: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                max_order,
            );
            printf(
                b"Smallest order: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                min_order,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_items_by_category(
            items: *mut array_item_t_t,
            category: *const core::ffi::c_char,
        ) {
            if items.is_null() || category.is_null() {
                return;
            }
            printf(
                b"\n=== Items in category '%s' ===\n\0" as *const u8 as *const core::ffi::c_char,
                category,
            );
            let mut found: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut item: item_t = item_t {
                id: 0,
                name: [0; 64],
                category: [0; 32],
                price: 0.,
                quantity: 0,
            };
            let mut _i: size_t = 0 as size_t;
            while _i < (*items).size && {
                item = *((*items).data).add(_i);
                1 as core::ffi::c_int != 0
            } {
                if strcmp((item.category).as_ptr(), category) == 0 as core::ffi::c_int {
                    print_item(item);
                    found += 1;
                }
                _i = _i.wrapping_add(1);
            }
            if found == 0 as core::ffi::c_int {
                printf(
                    b"No items found in this category\n\0" as *const u8 as *const core::ffi::c_char,
                );
            } else {
                printf(
                    b"Found %d items\n\0" as *const u8 as *const core::ffi::c_char,
                    found,
                );
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_expensive_items(
            items: *mut list_item_t_t,
            min_price: core::ffi::c_double,
        ) {
            if items.is_null() {
                return;
            }
            printf(
                b"\n=== Items priced above $%.2f ===\n\0" as *const u8 as *const core::ffi::c_char,
                min_price,
            );
            let mut found: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut item: item_t = item_t {
                id: 0,
                name: [0; 64],
                category: [0; 32],
                price: 0.,
                quantity: 0,
            };
            let mut _node: *mut list_node_item_t_t = (*items).head;
            while !_node.is_null() && {
                item = (*_node).data;
                1 as core::ffi::c_int != 0
            } {
                if item.price >= min_price {
                    print_item(item);
                    found += 1;
                }
                _node = (*_node).next as *mut list_node_item_t_t;
            }
            if found == 0 as core::ffi::c_int {
                printf(
                    b"No items found above this price\n\0" as *const u8 as *const core::ffi::c_char,
                );
            } else {
                printf(
                    b"Found %d items\n\0" as *const u8 as *const core::ffi::c_char,
                    found,
                );
            };
        }
    }
    pub mod main {
        use crate::src::inventory::array_double_create;
        use crate::src::inventory::array_double_destroy;
        use crate::src::inventory::array_double_push;
        use crate::src::inventory::array_double_t;
        use crate::src::inventory::array_int_create;
        use crate::src::inventory::array_int_destroy;
        use crate::src::inventory::array_int_push;
        use crate::src::inventory::array_int_t;
        use crate::src::inventory::array_item_t_create;
        use crate::src::inventory::array_item_t_destroy;
        use crate::src::inventory::array_item_t_push;
        use crate::src::inventory::array_item_t_t;
        use crate::src::inventory::calculate_inventory_stats;
        use crate::src::inventory::calculate_order_stats;
        use crate::src::inventory::create_item;
        use crate::src::inventory::create_order;
        use crate::src::inventory::find_items_by_category;
        use crate::src::inventory::item_t;
        use crate::src::inventory::list_double_append;
        use crate::src::inventory::list_double_create;
        use crate::src::inventory::list_double_destroy;
        use crate::src::inventory::list_double_t;
        use crate::src::inventory::list_int_append;
        use crate::src::inventory::list_int_create;
        use crate::src::inventory::list_int_destroy;
        use crate::src::inventory::list_int_t;
        use crate::src::inventory::list_item_t_append;
        use crate::src::inventory::list_item_t_create;
        use crate::src::inventory::list_item_t_destroy;
        use crate::src::inventory::list_item_t_t;
        use crate::src::inventory::list_node_double_t;
        use crate::src::inventory::list_node_int_t;
        use crate::src::inventory::list_node_item_t_t;
        use crate::src::inventory::list_node_order_t_t;
        use crate::src::inventory::list_order_t_append;
        use crate::src::inventory::list_order_t_create;
        use crate::src::inventory::list_order_t_destroy;
        use crate::src::inventory::list_order_t_t;
        use crate::src::inventory::order_t;
        use crate::src::inventory::print_item;
        use crate::src::inventory::print_order;
        use crate::src::inventory::size_t;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stdin: *mut FILE;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn sscanf(
                __s: *const core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
        }
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
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
        pub type FILE = _IO_FILE;
        #[no_mangle]
        pub unsafe extern "C" fn print_menu() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"  GENERIC FOR_EACH MACRO DEMO\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"1. Demo: Integer Containers\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"2. Demo: Double Containers\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"3. Demo: Inventory Array\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"4. Demo: Order List\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"5. Demo: Mixed Operations\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"6. Run All Demos\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"7. Exit\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"Choice: \0" as *const u8 as *const core::ffi::c_char);
        }
        #[no_mangle]
        pub unsafe extern "C" fn demo_integer_containers() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"  DEMO 1: Integer Containers\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let int_array: *mut array_int_t = array_int_create(10 as size_t);
            printf(b"\n--- Integer Array ---\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"Adding integers: 10, 20, 30, 40, 50\n\0" as *const u8 as *const core::ffi::c_char,
            );
            array_int_push(int_array, 10 as core::ffi::c_int);
            array_int_push(int_array, 20 as core::ffi::c_int);
            array_int_push(int_array, 30 as core::ffi::c_int);
            array_int_push(int_array, 40 as core::ffi::c_int);
            array_int_push(int_array, 50 as core::ffi::c_int);
            printf(b"Array contents: \0" as *const u8 as *const core::ffi::c_char);
            let mut val: core::ffi::c_int = 0;
            let mut _i: size_t = 0 as size_t;
            while _i < (*int_array).size && {
                val = *((*int_array).data).add(_i);
                1 as core::ffi::c_int != 0
            } {
                printf(b"%d \0" as *const u8 as *const core::ffi::c_char, val);
                _i = _i.wrapping_add(1);
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            let mut sum: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut _i_0: size_t = 0 as size_t;
            while _i_0 < (*int_array).size && {
                val = *((*int_array).data).add(_i_0);
                1 as core::ffi::c_int != 0
            } {
                sum += val;
                _i_0 = _i_0.wrapping_add(1);
            }
            printf(b"Sum: %d\n\0" as *const u8 as *const core::ffi::c_char, sum);
            printf(
                b"Average: %.2f\n\0" as *const u8 as *const core::ffi::c_char,
                sum as core::ffi::c_double / (*int_array).size as core::ffi::c_double,
            );
            let int_list: *mut list_int_t = list_int_create();
            printf(b"\n--- Integer List ---\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"Adding integers: 100, 200, 300, 400, 500\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            list_int_append(int_list, 100 as core::ffi::c_int);
            list_int_append(int_list, 200 as core::ffi::c_int);
            list_int_append(int_list, 300 as core::ffi::c_int);
            list_int_append(int_list, 400 as core::ffi::c_int);
            list_int_append(int_list, 500 as core::ffi::c_int);
            printf(b"List contents: \0" as *const u8 as *const core::ffi::c_char);
            let mut _node: *mut list_node_int_t = (*int_list).head;
            while !_node.is_null() && {
                val = (*_node).data;
                1 as core::ffi::c_int != 0
            } {
                printf(b"%d \0" as *const u8 as *const core::ffi::c_char, val);
                _node = (*_node).next as *mut list_node_int_t;
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            let mut product: core::ffi::c_longlong = 1 as core::ffi::c_longlong;
            let mut _node_0: *mut list_node_int_t = (*int_list).head;
            while !_node_0.is_null() && {
                val = (*_node_0).data;
                1 as core::ffi::c_int != 0
            } {
                product *= val as core::ffi::c_longlong;
                _node_0 = (*_node_0).next as *mut list_node_int_t;
            }
            printf(
                b"Product: %lld\n\0" as *const u8 as *const core::ffi::c_char,
                product,
            );
            array_int_destroy(int_array);
            list_int_destroy(int_list);
        }
        #[no_mangle]
        pub unsafe extern "C" fn demo_double_containers() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"  DEMO 2: Double Containers\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let double_array: *mut array_double_t = array_double_create(5 as size_t);
            printf(
                b"\n--- Double Array (Temperatures in Celsius) ---\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let temps: [core::ffi::c_double; 7] = [
                23.5f64, 25.0f64, 22.8f64, 26.3f64, 24.1f64, 21.9f64, 27.5f64,
            ];
            let num_temps: core::ffi::c_int = ::core::mem::size_of::<[core::ffi::c_double; 7]>()
                .wrapping_div(::core::mem::size_of::<core::ffi::c_double>())
                as core::ffi::c_int;
            printf(b"Adding temperatures: \0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < num_temps {
                array_double_push(double_array, temps[i as usize]);
                printf(
                    b"%.1f \0" as *const u8 as *const core::ffi::c_char,
                    temps[i as usize],
                );
                i += 1;
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            let mut min_temp: core::ffi::c_double = temps[0 as core::ffi::c_int as usize];
            let mut max_temp: core::ffi::c_double = temps[0 as core::ffi::c_int as usize];
            let mut sum_temp: core::ffi::c_double = 0.0f64;
            let mut temp: core::ffi::c_double = 0.;
            let mut _i: size_t = 0 as size_t;
            while _i < (*double_array).size && {
                temp = *((*double_array).data).add(_i);
                1 as core::ffi::c_int != 0
            } {
                if temp < min_temp {
                    min_temp = temp;
                }
                if temp > max_temp {
                    max_temp = temp;
                }
                sum_temp += temp;
                _i = _i.wrapping_add(1);
            }
            printf(
                b"Minimum: %.1f\xC2\xB0C\n\0" as *const u8 as *const core::ffi::c_char,
                min_temp,
            );
            printf(
                b"Maximum: %.1f\xC2\xB0C\n\0" as *const u8 as *const core::ffi::c_char,
                max_temp,
            );
            printf(
                b"Average: %.1f\xC2\xB0C\n\0" as *const u8 as *const core::ffi::c_char,
                sum_temp / (*double_array).size as core::ffi::c_double,
            );
            let price_list: *mut list_double_t = list_double_create();
            printf(
                b"\n--- Double List (Product Prices) ---\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let prices: [core::ffi::c_double; 6] =
                [9.99f64, 14.50f64, 7.25f64, 22.00f64, 5.99f64, 18.75f64];
            let num_prices: core::ffi::c_int = ::core::mem::size_of::<[core::ffi::c_double; 6]>()
                .wrapping_div(::core::mem::size_of::<core::ffi::c_double>())
                as core::ffi::c_int;
            printf(b"Adding prices: \0" as *const u8 as *const core::ffi::c_char);
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < num_prices {
                list_double_append(price_list, prices[i_0 as usize]);
                printf(
                    b"$%.2f \0" as *const u8 as *const core::ffi::c_char,
                    prices[i_0 as usize],
                );
                i_0 += 1;
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            let mut total: core::ffi::c_double = 0.0f64;
            let mut count_under_10: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut _node: *mut list_node_double_t = (*price_list).head;
            while !_node.is_null() && {
                temp = (*_node).data;
                1 as core::ffi::c_int != 0
            } {
                total += temp;
                if temp < 10.0f64 {
                    count_under_10 += 1;
                }
                _node = (*_node).next as *mut list_node_double_t;
            }
            printf(
                b"Total cost: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                total,
            );
            printf(
                b"Items under $10: %d\n\0" as *const u8 as *const core::ffi::c_char,
                count_under_10,
            );
            array_double_destroy(double_array);
            list_double_destroy(price_list);
        }
        #[no_mangle]
        pub unsafe extern "C" fn demo_inventory_array() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  DEMO 3: Inventory Array (Items)\n\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let inventory: *mut array_item_t_t = array_item_t_create(20 as size_t);
            printf(
                b"\n--- Adding Items to Inventory ---\n\0" as *const u8 as *const core::ffi::c_char,
            );
            array_item_t_push(
                inventory,
                create_item(
                    1 as core::ffi::c_int,
                    b"Laptop\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    899.99f64,
                    15 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    2 as core::ffi::c_int,
                    b"Mouse\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    24.99f64,
                    50 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    3 as core::ffi::c_int,
                    b"Keyboard\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    79.99f64,
                    30 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    4 as core::ffi::c_int,
                    b"Monitor\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    299.99f64,
                    20 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    5 as core::ffi::c_int,
                    b"Desk Chair\0" as *const u8 as *const core::ffi::c_char,
                    b"Furniture\0" as *const u8 as *const core::ffi::c_char,
                    199.99f64,
                    10 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    6 as core::ffi::c_int,
                    b"Desk\0" as *const u8 as *const core::ffi::c_char,
                    b"Furniture\0" as *const u8 as *const core::ffi::c_char,
                    349.99f64,
                    8 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    7 as core::ffi::c_int,
                    b"Notebook\0" as *const u8 as *const core::ffi::c_char,
                    b"Office\0" as *const u8 as *const core::ffi::c_char,
                    4.99f64,
                    100 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    8 as core::ffi::c_int,
                    b"Pen Set\0" as *const u8 as *const core::ffi::c_char,
                    b"Office\0" as *const u8 as *const core::ffi::c_char,
                    12.99f64,
                    75 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    9 as core::ffi::c_int,
                    b"USB Cable\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    9.99f64,
                    60 as core::ffi::c_int,
                ),
            );
            array_item_t_push(
                inventory,
                create_item(
                    10 as core::ffi::c_int,
                    b"Bookshelf\0" as *const u8 as *const core::ffi::c_char,
                    b"Furniture\0" as *const u8 as *const core::ffi::c_char,
                    149.99f64,
                    12 as core::ffi::c_int,
                ),
            );
            printf(
                b"Added %zu items to inventory\n\0" as *const u8 as *const core::ffi::c_char,
                (*inventory).size,
            );
            printf(b"\n--- All Inventory Items ---\n\0" as *const u8 as *const core::ffi::c_char);
            let mut item: item_t = item_t {
                id: 0,
                name: [0; 64],
                category: [0; 32],
                price: 0.,
                quantity: 0,
            };
            let mut _i: size_t = 0 as size_t;
            while _i < (*inventory).size && {
                item = *((*inventory).data).add(_i);
                1 as core::ffi::c_int != 0
            } {
                print_item(item);
                printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
                _i = _i.wrapping_add(1);
            }
            calculate_inventory_stats(inventory);
            find_items_by_category(
                inventory,
                b"Electronics\0" as *const u8 as *const core::ffi::c_char,
            );
            find_items_by_category(
                inventory,
                b"Furniture\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(
                b"\n--- Low Stock Items (< 20) ---\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let mut low_stock_count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut _i_0: size_t = 0 as size_t;
            while _i_0 < (*inventory).size && {
                item = *((*inventory).data).add(_i_0);
                1 as core::ffi::c_int != 0
            } {
                if item.quantity < 20 as core::ffi::c_int {
                    print_item(item);
                    low_stock_count += 1;
                }
                _i_0 = _i_0.wrapping_add(1);
            }
            printf(
                b"Total low stock items: %d\n\0" as *const u8 as *const core::ffi::c_char,
                low_stock_count,
            );
            array_item_t_destroy(inventory);
        }
        #[no_mangle]
        pub unsafe extern "C" fn demo_order_list() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"  DEMO 4: Order List (Orders)\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let orders: *mut list_order_t_t = list_order_t_create();
            printf(b"\n--- Adding Orders ---\n\0" as *const u8 as *const core::ffi::c_char);
            list_order_t_append(
                orders,
                create_order(
                    1001 as core::ffi::c_int,
                    b"Alice Johnson\0" as *const u8 as *const core::ffi::c_char,
                    1249.95f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1002 as core::ffi::c_int,
                    b"Bob Smith\0" as *const u8 as *const core::ffi::c_char,
                    89.99f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1003 as core::ffi::c_int,
                    b"Carol White\0" as *const u8 as *const core::ffi::c_char,
                    549.98f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1004 as core::ffi::c_int,
                    b"David Brown\0" as *const u8 as *const core::ffi::c_char,
                    24.99f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1005 as core::ffi::c_int,
                    b"Eve Davis\0" as *const u8 as *const core::ffi::c_char,
                    899.99f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1006 as core::ffi::c_int,
                    b"Frank Miller\0" as *const u8 as *const core::ffi::c_char,
                    374.97f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1007 as core::ffi::c_int,
                    b"Grace Lee\0" as *const u8 as *const core::ffi::c_char,
                    159.98f64,
                ),
            );
            list_order_t_append(
                orders,
                create_order(
                    1008 as core::ffi::c_int,
                    b"Henry Wilson\0" as *const u8 as *const core::ffi::c_char,
                    1099.99f64,
                ),
            );
            printf(
                b"Added %zu orders\n\0" as *const u8 as *const core::ffi::c_char,
                (*orders).size,
            );
            printf(b"\n--- All Orders ---\n\0" as *const u8 as *const core::ffi::c_char);
            let mut order: order_t = order_t {
                customer_id: 0,
                customer_name: [0; 64],
                total_amount: 0.,
            };
            let mut _node: *mut list_node_order_t_t = (*orders).head;
            while !_node.is_null() && {
                order = (*_node).data;
                1 as core::ffi::c_int != 0
            } {
                print_order(order);
                _node = (*_node).next as *mut list_node_order_t_t;
            }
            calculate_order_stats(orders);
            printf(b"\n--- Large Orders (> $500) ---\n\0" as *const u8 as *const core::ffi::c_char);
            let mut large_order_count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut large_order_total: core::ffi::c_double = 0.0f64;
            let mut _node_0: *mut list_node_order_t_t = (*orders).head;
            while !_node_0.is_null() && {
                order = (*_node_0).data;
                1 as core::ffi::c_int != 0
            } {
                if order.total_amount > 500.0f64 {
                    print_order(order);
                    large_order_count += 1;
                    large_order_total += order.total_amount;
                }
                _node_0 = (*_node_0).next as *mut list_node_order_t_t;
            }
            printf(
                b"Total large orders: %d\n\0" as *const u8 as *const core::ffi::c_char,
                large_order_count,
            );
            printf(
                b"Revenue from large orders: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                large_order_total,
            );
            list_order_t_destroy(orders);
        }
        #[no_mangle]
        pub unsafe extern "C" fn demo_mixed_operations() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"  DEMO 5: Mixed Operations\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let array_inventory: *mut array_item_t_t = array_item_t_create(10 as size_t);
            let list_inventory: *mut list_item_t_t = list_item_t_create();
            printf(
                b"\n--- Populating both Array and List ---\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let items: [item_t; 5] = [
                create_item(
                    1 as core::ffi::c_int,
                    b"Smartphone\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    699.99f64,
                    25 as core::ffi::c_int,
                ),
                create_item(
                    2 as core::ffi::c_int,
                    b"Tablet\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    449.99f64,
                    18 as core::ffi::c_int,
                ),
                create_item(
                    3 as core::ffi::c_int,
                    b"Headphones\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    149.99f64,
                    40 as core::ffi::c_int,
                ),
                create_item(
                    4 as core::ffi::c_int,
                    b"Smart Watch\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    299.99f64,
                    22 as core::ffi::c_int,
                ),
                create_item(
                    5 as core::ffi::c_int,
                    b"Power Bank\0" as *const u8 as *const core::ffi::c_char,
                    b"Electronics\0" as *const u8 as *const core::ffi::c_char,
                    39.99f64,
                    55 as core::ffi::c_int,
                ),
            ];
            let num_items: core::ffi::c_int = ::core::mem::size_of::<[item_t; 5]>()
                .wrapping_div(::core::mem::size_of::<item_t>())
                as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < num_items {
                array_item_t_push(array_inventory, items[i as usize]);
                list_item_t_append(list_inventory, items[i as usize]);
                i += 1;
            }
            printf(
                b"Added %d items to both containers\n\0" as *const u8 as *const core::ffi::c_char,
                num_items,
            );
            printf(
                b"\n--- Iterating through Array ---\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let mut array_count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut item: item_t = item_t {
                id: 0,
                name: [0; 64],
                category: [0; 32],
                price: 0.,
                quantity: 0,
            };
            let mut _i: size_t = 0 as size_t;
            while _i < (*array_inventory).size && {
                item = *((*array_inventory).data).add(_i);
                1 as core::ffi::c_int != 0
            } {
                array_count += 1;
                _i = _i.wrapping_add(1);
            }
            printf(
                b"Array iteration count: %d\n\0" as *const u8 as *const core::ffi::c_char,
                array_count,
            );
            printf(
                b"\n--- Iterating through List ---\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let mut list_count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut _node: *mut list_node_item_t_t = (*list_inventory).head;
            while !_node.is_null() && {
                item = (*_node).data;
                1 as core::ffi::c_int != 0
            } {
                list_count += 1;
                _node = (*_node).next as *mut list_node_item_t_t;
            }
            printf(
                b"List iteration count: %d\n\0" as *const u8 as *const core::ffi::c_char,
                list_count,
            );
            let price_threshold: core::ffi::c_double = 200.0f64;
            printf(
                b"\n--- Items above $%.2f (Array) ---\n\0" as *const u8 as *const core::ffi::c_char,
                price_threshold,
            );
            let mut _i_0: size_t = 0 as size_t;
            while _i_0 < (*array_inventory).size && {
                item = *((*array_inventory).data).add(_i_0);
                1 as core::ffi::c_int != 0
            } {
                if item.price >= price_threshold {
                    printf(
                        b"  %s: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                        (item.name).as_ptr(),
                        item.price,
                    );
                }
                _i_0 = _i_0.wrapping_add(1);
            }
            printf(
                b"\n--- Items above $%.2f (List) ---\n\0" as *const u8 as *const core::ffi::c_char,
                price_threshold,
            );
            let mut _node_0: *mut list_node_item_t_t = (*list_inventory).head;
            while !_node_0.is_null() && {
                item = (*_node_0).data;
                1 as core::ffi::c_int != 0
            } {
                if item.price >= price_threshold {
                    printf(
                        b"  %s: $%.2f\n\0" as *const u8 as *const core::ffi::c_char,
                        (item.name).as_ptr(),
                        item.price,
                    );
                }
                _node_0 = (*_node_0).next as *mut list_node_item_t_t;
            }
            array_item_t_destroy(array_inventory);
            list_item_t_destroy(list_inventory);
        }
        unsafe fn main_0() -> core::ffi::c_int {
            printf(b"\xE2\x95\x94\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x97\n\0"
                        as *const u8 as *const core::ffi::c_char);
            printf(
                b"\xE2\x95\x91   GENERIC FOR_EACH MACRO DEMO         \xE2\x95\x91\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"\xE2\x95\x91   Demonstrating Generic Containers    \xE2\x95\x91\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\xE2\x95\x9A\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x9D\n\0"
                        as *const u8 as *const core::ffi::c_char);
            let mut input: [core::ffi::c_char; 256] = [0; 256];
            let mut choice: core::ffi::c_int = 0;
            loop {
                print_menu();
                if (fgets(
                    input.as_mut_ptr(),
                    ::core::mem::size_of::<[core::ffi::c_char; 256]>() as core::ffi::c_int,
                    stdin,
                ))
                .is_null()
                {
                    break;
                }
                if sscanf(
                    input.as_ptr(),
                    b"%d\0" as *const u8 as *const core::ffi::c_char,
                    &mut choice as *mut core::ffi::c_int,
                ) != 1 as core::ffi::c_int
                {
                    printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                } else {
                    match choice {
                        1 => {
                            demo_integer_containers();
                        }
                        2 => {
                            demo_double_containers();
                        }
                        3 => {
                            demo_inventory_array();
                        }
                        4 => {
                            demo_order_list();
                        }
                        5 => {
                            demo_mixed_operations();
                        }
                        6 => {
                            printf(
                                b"\n=== Running All Demos ===\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            demo_integer_containers();
                            demo_double_containers();
                            demo_inventory_array();
                            demo_order_list();
                            demo_mixed_operations();
                            printf(
                                b"\n========================================\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            printf(
                                b"  All demos completed successfully!\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            printf(
                                b"========================================\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                        }
                        7 => {
                            printf(b"\nGoodbye!\n\0" as *const u8 as *const core::ffi::c_char);
                            return 0 as core::ffi::c_int;
                        }
                        _ => {
                            printf(b"Invalid choice\n\0" as *const u8 as *const core::ffi::c_char);
                        }
                    }
                }
            }
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "generic-foreach",
        SOURCE,
        &["array_int_create#arr", "list_int_create#list"],
        // M1 MIR-source migration: realloc temporary no longer classified as owning local.
        &[
            "src::inventory::array_int_push#new_data",
            "src::inventory::array_double_push#new_data",
            "src::inventory::array_item_t_push#new_data",
            "src::inventory::array_order_t_push#new_data",
        ],
    );
}
