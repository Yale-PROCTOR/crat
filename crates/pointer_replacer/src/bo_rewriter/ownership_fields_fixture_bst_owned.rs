// R533-2 fixture: bst's node fields Owning by override (the L01^6 verdict).
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
#![feature(rt)]
#![feature(libstd_sys_internals)]
#![feature(structural_match)]
extern crate libc;
pub mod src {
    pub mod bst {
        use ::libc;
        extern "C" {
            fn printf(_: *const libc::c_char, _: ...)
            -> libc::c_int;
            fn malloc(_: libc::c_ulong)
            -> *mut libc::c_void;
            fn free(_: *mut libc::c_void);
        }
        #[repr(C)]
        pub struct node {
            pub key: libc::c_int,
            pub left: *mut node,
            pub right: *mut node,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for node { }
        #[automatically_derived]
        impl ::core::clone::Clone for node {
            #[inline]
            fn clone(&self) -> node {
                let _: ::core::clone::AssertParamIsClone<libc::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut node>;
                let _: ::core::clone::AssertParamIsClone<*mut node>;
                *self
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn newNode(mut item: libc::c_int) -> *mut node {
            let mut temp =
                malloc(::std::mem::size_of::<node>() as libc::c_ulong) as
                    *mut node;
            (*temp).key = item;
            (*temp).left = 0 as *mut node;
            (*temp).right = 0 as *mut node;
            return temp;
        }
        #[no_mangle]
        pub unsafe extern "C" fn inorder(mut root: *mut node) {
            if !root.is_null() {
                inorder((*root).left);
                printf(b"%d \0" as *const u8 as *const libc::c_char,
                    (*root).key);
                inorder((*root).right);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn insert(mut node: *mut node,
            mut key: libc::c_int) -> *mut node {
            if node.is_null() { return newNode(key); }
            if key < (*node).key {
                (*node).left = insert((*node).left, key);
            } else { (*node).right = insert((*node).right, key); }
            return node;
        }
        #[no_mangle]
        pub unsafe extern "C" fn minValueNode(mut node: *mut node)
            -> *mut node {
            while !node.is_null() && !((*node).left).is_null() {
                node = (*node).left;
            }
            return node;
        }
        #[no_mangle]
        pub unsafe extern "C" fn deleteNode(mut root: *mut node,
            mut key: libc::c_int) -> *mut node {
            if root.is_null() { return root; }
            if key < (*root).key {
                (*root).left = deleteNode((*root).left, key);
            } else if key > (*root).key {
                (*root).right = deleteNode((*root).right, key);
            } else {
                if ((*root).left).is_null() {
                    let mut temp = (*root).right;
                    free(root as *mut libc::c_void);
                    return temp;
                } else {
                    if ((*root).right).is_null() {
                        let mut temp_0 = (*root).left;
                        free(root as *mut libc::c_void);
                        return temp_0;
                    }
                }
                let mut temp_1 = minValueNode((*root).right);
                (*root).key = (*temp_1).key;
                (*root).right = deleteNode((*root).right, (*temp_1).key);
            }
            return root;
        }
    }
}