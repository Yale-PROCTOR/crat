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
    pub mod lib {
        extern "C" {
            fn sprintf(
                __s: *mut core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn sqrt(__x: core::ffi::c_double) -> core::ffi::c_double;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct Node {
            pub id: core::ffi::c_int,
            pub parent_id: core::ffi::c_int,
            pub value: core::ffi::c_double,
            pub data: [core::ffi::c_int; 4],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Node {}
        #[automatically_derived]
        impl ::core::clone::Clone for Node {
            #[inline]
            fn clone(&self) -> Node {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_int; 4]>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        static mut node_storage: [Node; 100] = [Node {
            id: 0,
            parent_id: 0,
            value: 0.,
            data: [0; 4],
        }; 100];
        static mut node_count: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const STATUS_ERROR: core::ffi::c_int = 0o2 as core::ffi::c_int;
        unsafe extern "C" fn find_node_by_id(id: core::ffi::c_int) -> *mut Node {
            let mut i: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < node_count {
                if node_storage[i as usize].id == id {
                    return &mut *node_storage.as_mut_ptr().offset(i as isize) as *mut Node;
                }
                i += 1;
            }
            std::ptr::null_mut::<Node>()
        }
        unsafe extern "C" fn process_backward(
            array: *mut core::ffi::c_int,
            size: size_t,
            start_offset: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut sum: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut ptr: *mut core::ffi::c_int = std::ptr::null_mut::<core::ffi::c_int>();
            let mut start: *mut core::ffi::c_int = std::ptr::null_mut::<core::ffi::c_int>();
            ptr = array.add(size);
            start = array.offset(start_offset as isize);
            while ptr > start {
                ptr = ptr.offset(-1);
                sum += *ptr;
            }
            sum
        }
        unsafe extern "C" fn compute_size_metric(
            str: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            let len: size_t = strlen(str);
            let mut metric: core::ffi::c_int = 0;
            metric = len as core::ffi::c_int;
            metric = metric * 2 as core::ffi::c_int + 0o10 as core::ffi::c_int;
            metric
        }
        unsafe extern "C" fn safe_double_to_int(
            mut value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            if value > 2147483647.0f64 {
                value = 2147483647.0f64;
            }
            if value < -2147483648.0f64 {
                value = -2147483648.0f64;
            }
            value as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn jumpnode(
            operation_mode: core::ffi::c_int,
            node_id: core::ffi::c_int,
            depth: core::ffi::c_int,
            flags: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut current_node: *mut Node = std::ptr::null_mut::<Node>();
            let mut parent_node: *mut Node = std::ptr::null_mut::<Node>();
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0;
            let mut accumulated_value: core::ffi::c_double = 0.;
            let mut temp_array: [core::ffi::c_int; 20] = [0; 20];
            let mut array_size: size_t = 0;
            let mut buffer: [core::ffi::c_char; 50] = [0; 50];
            match operation_mode {
                1 => {
                    current_node = find_node_by_id(node_id);
                    if current_node.is_null() {
                        return STATUS_ERROR | 0o20 as core::ffi::c_int;
                    }
                    accumulated_value = (*current_node).value;
                    i = 0 as core::ffi::c_int;
                    while i < depth && (*current_node).parent_id != -(1 as core::ffi::c_int) {
                        parent_node = find_node_by_id((*current_node).parent_id);
                        if parent_node.is_null() {
                            break;
                        }
                        accumulated_value += (*parent_node).value * 1.5f64;
                        current_node = parent_node;
                        i += 1;
                    }
                    result = safe_double_to_int(accumulated_value);
                }
                2 => {
                    current_node = find_node_by_id(node_id);
                    if current_node.is_null() {
                        return STATUS_ERROR | 0o40 as core::ffi::c_int;
                    }
                    i = 0 as core::ffi::c_int;
                    while i < 4 as core::ffi::c_int {
                        temp_array[i as usize] = (*current_node).data[i as usize];
                        i += 1;
                    }
                    i = 4 as core::ffi::c_int;
                    while i < 0o20 as core::ffi::c_int {
                        temp_array[i as usize] = i * 0o7 as core::ffi::c_int;
                        i += 1;
                    }
                    array_size = 0o20 as size_t;
                    result = process_backward(temp_array.as_mut_ptr(), array_size, depth);
                    result += array_size as core::ffi::c_int * flags;
                }
                3 => {
                    sprintf(
                        buffer.as_mut_ptr(),
                        b"Node_%d_Depth_%d\0" as *const u8 as *const core::ffi::c_char,
                        node_id,
                        depth,
                    );
                    result = compute_size_metric(buffer.as_ptr());
                    result += flags & 0o177 as core::ffi::c_int;
                }
                4 => {
                    current_node = find_node_by_id(node_id);
                    if current_node.is_null() {
                        return STATUS_ERROR | 0o100 as core::ffi::c_int;
                    }
                    accumulated_value = 0.0f64;
                    i = 0 as core::ffi::c_int;
                    while i < 4 as core::ffi::c_int {
                        accumulated_value +=
                            sqrt((*current_node).data[i as usize] as core::ffi::c_double)
                                * 2.718281828f64;
                        i += 1;
                    }
                    accumulated_value *= 1.0f64 + depth as core::ffi::c_double * 0.1f64;
                    result = safe_double_to_int(accumulated_value);
                    if node_count > 2 as core::ffi::c_int {
                        let end_ptr: *mut Node =
                            &mut *node_storage.as_mut_ptr().offset(node_count as isize)
                                as *mut Node;
                        let mut iter: *mut Node = end_ptr;
                        let mut backward_sum: core::ffi::c_int = 0 as core::ffi::c_int;
                        i = 0 as core::ffi::c_int;
                        while i < 3 as core::ffi::c_int && iter > node_storage.as_mut_ptr() {
                            iter = iter.offset(-1);
                            backward_sum += safe_double_to_int((*iter).value);
                            i += 1;
                        }
                        result += backward_sum;
                    }
                }
                _ => {
                    result = STATUS_ERROR | 0o200 as core::ffi::c_int;
                }
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("jumpnode_lib", SOURCE);
}
