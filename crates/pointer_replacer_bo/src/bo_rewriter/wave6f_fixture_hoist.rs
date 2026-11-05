#![feature(derive_clone_copy)]
// w6f-hoist-frame
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
#[no_mangle]
pub unsafe extern "C" fn deleteNode(mut root: *mut node, mut key: i32) -> *mut node {
    if root.is_null() { return root; }
    if key < (*root).key {
        (*root).left = deleteNode((*root).left, key);
    } else if key > (*root).key {
        (*root).right = deleteNode((*root).right, key);
    } else {
        let mut temp = (*root).left;
        free(root as *mut ::std::ffi::c_void);
        return temp;
    }
    return root;
}
#[no_mangle]
pub unsafe extern "C" fn removeMin(mut root: *mut node) {
    let mut temp = (*root).right;
    (*root).key = (*temp).key;
    (*root).right = deleteNode((*root).right, (*temp).key);
}
