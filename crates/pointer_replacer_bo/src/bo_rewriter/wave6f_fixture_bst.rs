#![feature(derive_clone_copy)]
// w6f-bst-frame
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
extern "C" {
    fn malloc(_: u64) -> *mut ::std::ffi::c_void;
    fn free(_: *mut ::std::ffi::c_void);
}
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}
#[automatically_derived]
impl ::core::marker::Copy for node { }
#[automatically_derived]
impl ::core::clone::Clone for node {
    #[inline]
    fn clone(&self) -> node {
        let _: ::core::clone::AssertParamIsClone<i32>;
        let _: ::core::clone::AssertParamIsClone<*mut node>;
        let _: ::core::clone::AssertParamIsClone<*mut node>;
        *self
    }
}
#[no_mangle]
pub unsafe extern "C" fn newNode(mut item: i32) -> *mut node {
    let mut temp = malloc(::std::mem::size_of::<node>() as u64) as *mut node;
    (*temp).key = item;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    return temp;
}
#[no_mangle]
pub unsafe extern "C" fn inorder(mut root: *mut node) {
    if !root.is_null() {
        inorder((*root).left);
        inorder((*root).right);
    }
}
#[no_mangle]
pub unsafe extern "C" fn insert(mut node: *mut node, mut key: i32) -> *mut node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else { (*node).right = insert((*node).right, key); }
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn minValueNode(mut node: *mut node) -> *mut node {
    while !node.is_null() && !((*node).left).is_null() {
        node = (*node).left;
    }
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn deleteNode(mut root: *mut node, mut key: i32) -> *mut node {
    if root.is_null() { return root; }
    if key < (*root).key {
        (*root).left = deleteNode((*root).left, key);
    } else if key > (*root).key {
        (*root).right = deleteNode((*root).right, key);
    } else {
        if ((*root).left).is_null() {
            let mut temp = (*root).right;
            free(root as *mut ::std::ffi::c_void);
            return temp;
        } else {
            if ((*root).right).is_null() {
                let mut temp_0 = (*root).left;
                free(root as *mut ::std::ffi::c_void);
                return temp_0;
            }
        }
        let mut temp_1 = minValueNode((*root).right);
        (*root).key = (*temp_1).key;
        (*root).right = deleteNode((*root).right, (*temp_1).key);
    }
    return root;
}
