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
            fn strchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
        pub type Operation = core::ffi::c_uint;
        pub const OP_MODULO: Operation = 5;
        pub const OP_DIVIDE: Operation = 4;
        pub const OP_SUBTRACT: Operation = 3;
        pub const OP_MULTIPLY: Operation = 2;
        pub const OP_ADD: Operation = 1;
        #[repr(C)]
        pub struct TreeNode {
            pub id: core::ffi::c_int,
            pub value: core::ffi::c_int,
            pub parent_id: core::ffi::c_int,
            pub left_child_id: core::ffi::c_int,
            pub right_child_id: core::ffi::c_int,
            pub label: [core::ffi::c_char; 32],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for TreeNode {}
        #[automatically_derived]
        impl ::core::clone::Clone for TreeNode {
            #[inline]
            fn clone(&self) -> TreeNode {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                *self
            }
        }
        pub type OperationFunc = Option<
            unsafe extern "C" fn(
                core::ffi::c_int,
                core::ffi::c_int,
                core::ffi::c_int,
                core::ffi::c_int,
            ) -> core::ffi::c_int,
        >;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_NODES: core::ffi::c_int = 50 as core::ffi::c_int;
        #[no_mangle]
        pub static mut node_table: [TreeNode; 50] = [TreeNode {
            id: 0,
            value: 0,
            parent_id: 0,
            left_child_id: 0,
            right_child_id: 0,
            label: [0; 32],
        }; 50];
        #[no_mangle]
        pub static mut node_count: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn add_op(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a + b
        }
        #[no_mangle]
        pub unsafe extern "C" fn multiply_op(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a * b
        }
        #[no_mangle]
        pub unsafe extern "C" fn subtract_op(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a - b
        }
        #[no_mangle]
        pub unsafe extern "C" fn divide_op(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if b == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            a / b
        }
        #[no_mangle]
        pub unsafe extern "C" fn modulo_op(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if b == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            a % b
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_node_by_id(id: core::ffi::c_int) -> *mut TreeNode {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < node_count {
                if node_table[i as usize].id == id {
                    return &mut *node_table.as_mut_ptr().offset(i as isize) as *mut TreeNode;
                }
                i += 1;
            }
            std::ptr::null_mut::<TreeNode>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn add_tree_node(
            id: core::ffi::c_int,
            value: core::ffi::c_int,
            parent_id: core::ffi::c_int,
            label: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if node_count >= MAX_NODES {
                return -(1 as core::ffi::c_int);
            }
            let node: *mut TreeNode =
                &mut *node_table.as_mut_ptr().offset(node_count as isize) as *mut TreeNode;
            (*node).id = id;
            (*node).value = value;
            (*node).parent_id = parent_id;
            (*node).left_child_id = -(1 as core::ffi::c_int);
            (*node).right_child_id = -(1 as core::ffi::c_int);
            strncpy(((*node).label).as_mut_ptr(), label, 31 as size_t);
            (*node).label[31 as core::ffi::c_int as usize] = '\0' as i32 as core::ffi::c_char;
            if parent_id != -(1 as core::ffi::c_int) {
                let parent: *mut TreeNode = find_node_by_id(parent_id);
                if parent.is_null() || (*parent).id != parent_id {
                    return -(1 as core::ffi::c_int);
                }
                if (*parent).left_child_id == -(1 as core::ffi::c_int) {
                    (*parent).left_child_id = id;
                } else if (*parent).right_child_id == -(1 as core::ffi::c_int) {
                    (*parent).right_child_id = id;
                }
            }
            node_count += 1;
            node_count - 1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn calculate_tree_sum(node_id: core::ffi::c_int) -> core::ffi::c_int {
            let node: *mut TreeNode = find_node_by_id(node_id);
            if node.is_null() || (*node).id != node_id {
                return 0 as core::ffi::c_int;
            }
            let mut sum: core::ffi::c_int = (*node).value;
            if (*node).left_child_id != -(1 as core::ffi::c_int) {
                sum += calculate_tree_sum((*node).left_child_id);
            }
            if (*node).right_child_id != -(1 as core::ffi::c_int) {
                sum += calculate_tree_sum((*node).right_child_id);
            }
            sum
        }
        #[no_mangle]
        pub unsafe extern "C" fn parse_operation(op_str: *const core::ffi::c_char) -> Operation {
            if op_str.is_null() || !(strchr(op_str, '+' as i32)).is_null() {
                return OP_ADD;
            }
            if !(strchr(op_str, '*' as i32)).is_null() {
                return OP_MULTIPLY;
            }
            if !(strchr(op_str, '-' as i32)).is_null() {
                return OP_SUBTRACT;
            }
            if !(strchr(op_str, '/' as i32)).is_null() {
                return OP_DIVIDE;
            }
            if !(strchr(op_str, '%' as i32)).is_null() {
                return OP_MODULO;
            }
            OP_ADD
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_operation_func(op: Operation) -> OperationFunc {
            match op as core::ffi::c_int {
                1 => Some(
                    add_op
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                2 => Some(
                    multiply_op
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                3 => Some(
                    subtract_op
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                4 => Some(
                    divide_op
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                5 => Some(
                    modulo_op
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                _ => Some(
                    add_op
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn inreftree(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            node_count = 0 as core::ffi::c_int;
            add_tree_node(
                1 as core::ffi::c_int,
                param1,
                -(1 as core::ffi::c_int),
                b"root\0" as *const u8 as *const core::ffi::c_char,
            );
            add_tree_node(
                2 as core::ffi::c_int,
                param2,
                1 as core::ffi::c_int,
                b"left\0" as *const u8 as *const core::ffi::c_char,
            );
            add_tree_node(
                3 as core::ffi::c_int,
                param3,
                1 as core::ffi::c_int,
                b"right\0" as *const u8 as *const core::ffi::c_char,
            );
            add_tree_node(
                4 as core::ffi::c_int,
                param4,
                2 as core::ffi::c_int,
                b"left-left\0" as *const u8 as *const core::ffi::c_char,
            );
            let mut target_id: core::ffi::c_int = -(1 as core::ffi::c_int);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < node_count {
                if !(strchr((node_table[i as usize].label).as_ptr(), 'l' as i32)).is_null() {
                    target_id = node_table[i as usize].id;
                    break;
                } else {
                    i += 1;
                }
            }
            let target: *mut TreeNode = find_node_by_id(target_id);
            if target.is_null() || (*target).value == 0 as core::ffi::c_int {
                target_id = 1 as core::ffi::c_int;
            }
            let tree_sum: core::ffi::c_int = calculate_tree_sum(1 as core::ffi::c_int);
            let op_string: *const core::ffi::c_char =
                b"+*-%\0" as *const u8 as *const core::ffi::c_char;
            let op_char: [core::ffi::c_char; 2] = [
                *op_string.offset((tree_sum % 4 as core::ffi::c_int) as isize),
                '\0' as i32 as core::ffi::c_char,
            ];
            let op: Operation = parse_operation(op_char.as_ptr());
            let op_value: core::ffi::c_int = op as core::ffi::c_int;
            let func: OperationFunc = get_operation_func(op);
            let result: core::ffi::c_int = func.expect("non-null function pointer")(
                tree_sum,
                target_id,
                0 as core::ffi::c_int,
                0 as core::ffi::c_int,
            );
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("inreftree_lib", SOURCE, &[], &[]);
}
