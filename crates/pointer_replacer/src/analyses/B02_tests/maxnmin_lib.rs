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
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct Node {
            pub id: core::ffi::c_int,
            pub parent_id: core::ffi::c_int,
            pub name: [core::ffi::c_char; 50],
            pub value: core::ffi::c_double,
            pub active: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Node {}
        #[automatically_derived]
        impl ::core::clone::Clone for Node {
            #[inline]
            fn clone(&self) -> Node {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 50]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_NODES: core::ffi::c_int = 100 as core::ffi::c_int;
        pub const MAX_NAME_LEN: core::ffi::c_int = 50 as core::ffi::c_int;
        static mut node_storage: [Node; 100] = [Node {
            id: 0,
            parent_id: 0,
            name: [0; 50],
            value: 0.,
            active: 0,
        }; 100];
        static mut node_count: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn add_node(
            id: core::ffi::c_int,
            parent_id: core::ffi::c_int,
            name: *const core::ffi::c_char,
            value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            if node_count >= MAX_NODES {
                return -(1 as core::ffi::c_int);
            }
            let mut new_node: Node = {
                Node {
                    id,
                    parent_id,
                    name: [0; 50],
                    value,
                    active: 1 as core::ffi::c_int,
                }
            };
            strncpy(
                (new_node.name).as_mut_ptr(),
                name,
                (MAX_NAME_LEN - 1 as core::ffi::c_int) as size_t,
            );
            new_node.name[(MAX_NAME_LEN - 1 as core::ffi::c_int) as usize] =
                '\0' as i32 as core::ffi::c_char;
            let fresh0 = node_count;
            node_count += 1;
            node_storage[fresh0 as usize] = new_node;
            node_count - 1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_node_by_id(id: core::ffi::c_int) -> *mut Node {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < node_count {
                if node_storage[i as usize].id == id && node_storage[i as usize].active != 0 {
                    return &mut *node_storage.as_mut_ptr().offset(i as isize) as *mut Node;
                }
                i += 1;
            }
            std::ptr::null_mut::<Node>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_children_count(
            parent_id: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < node_count {
                if node_storage[i as usize].parent_id == parent_id
                    && node_storage[i as usize].active != 0
                {
                    count += 1;
                }
                i += 1;
            }
            count
        }
        #[no_mangle]
        pub unsafe extern "C" fn calculate_subtree_sum(
            node_id: core::ffi::c_int,
        ) -> core::ffi::c_double {
            let node: *mut Node = find_node_by_id(node_id);
            if node.is_null() {
                return 0.0f64;
            }
            let mut sum: core::ffi::c_double = (*node).value;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < node_count {
                if node_storage[i as usize].parent_id == node_id
                    && node_storage[i as usize].active != 0
                {
                    sum += calculate_subtree_sum(node_storage[i as usize].id);
                }
                i += 1;
            }
            sum
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_string(
            mut str: *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            if *str != 0 {
                while *str != 0 {
                    result += *str as core::ffi::c_int;
                    str = str.offset(1);
                }
            }
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn safe_double_to_int(d: core::ffi::c_double) -> core::ffi::c_int {
            if d > INT_MAX as core::ffi::c_double {
                return INT_MAX;
            }
            if d < INT_MIN as core::ffi::c_double {
                return INT_MIN;
            }
            if d != d {
                return 0 as core::ffi::c_int;
            }
            d as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn maxnmin(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            node_count = 0 as core::ffi::c_int;
            add_node(
                1 as core::ffi::c_int,
                -(1 as core::ffi::c_int),
                b"root\0" as *const u8 as *const core::ffi::c_char,
                10.5f64,
            );
            add_node(
                2 as core::ffi::c_int,
                1 as core::ffi::c_int,
                b"child1\0" as *const u8 as *const core::ffi::c_char,
                20.7f64,
            );
            add_node(
                3 as core::ffi::c_int,
                1 as core::ffi::c_int,
                b"child2\0" as *const u8 as *const core::ffi::c_char,
                15.3f64,
            );
            add_node(
                4 as core::ffi::c_int,
                2 as core::ffi::c_int,
                b"grandchild1\0" as *const u8 as *const core::ffi::c_char,
                5.9f64,
            );
            add_node(
                5 as core::ffi::c_int,
                2 as core::ffi::c_int,
                b"grandchild2\0" as *const u8 as *const core::ffi::c_char,
                8.2f64,
            );
            add_node(
                6 as core::ffi::c_int,
                3 as core::ffi::c_int,
                b"grandchild3\0" as *const u8 as *const core::ffi::c_char,
                12.4f64,
            );
            let node_id: core::ffi::c_int = param1 % 6 as core::ffi::c_int + 1 as core::ffi::c_int;
            let selected_node: *mut Node = find_node_by_id(node_id);
            if !selected_node.is_null() {
                let name_ptr: *mut core::ffi::c_char = ((*selected_node).name).as_mut_ptr();
                if *name_ptr != 0 {
                    result += process_string(name_ptr);
                }
                let subtree_sum: core::ffi::c_double = calculate_subtree_sum(node_id);
                let sum_as_int: core::ffi::c_int = safe_double_to_int(subtree_sum);
                result += sum_as_int;
            }
            let second_node_id: core::ffi::c_int =
                param2 % 6 as core::ffi::c_int + 1 as core::ffi::c_int;
            let second_node: *mut Node = find_node_by_id(second_node_id);
            if !second_node.is_null() {
                let value_multiplied: core::ffi::c_double =
                    (*second_node).value * param3 as core::ffi::c_double;
                let converted_value: core::ffi::c_int = safe_double_to_int(value_multiplied);
                result += converted_value;
            }
            let parent_id: core::ffi::c_int =
                param4 % 3 as core::ffi::c_int + 1 as core::ffi::c_int;
            let children: core::ffi::c_int = get_children_count(parent_id);
            result += children * 10 as core::ffi::c_int;
            let mut calculation: core::ffi::c_double = (param1 + param2) as core::ffi::c_double
                / (param3 + 1 as core::ffi::c_int) as core::ffi::c_double;
            calculation *= param4 as core::ffi::c_double;
            let final_calc: core::ffi::c_int = safe_double_to_int(calculation);
            result += final_calc;
            result
        }
        pub const INT_MAX: core::ffi::c_int = __INT_MAX__;
        pub const INT_MIN: core::ffi::c_int = -__INT_MAX__ - 1 as core::ffi::c_int;
        pub const __INT_MAX__: core::ffi::c_int = 2147483647 as core::ffi::c_int;
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("maxnmin_lib", SOURCE, &[], &[]);
}
