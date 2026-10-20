//! w6f-quadtree-root-frame
//!
//! Reduction of quadtree's `quadtree_t.root` — the CROWN unit
//! `quadtree_new::tree` depends on this field delivering as an OWNED field
//! (relay 059 / R518-3). Faithful in the three respects that decide it: the
//! constructor stores a certified constructor result into the field, the store
//! is NULL-TESTED with the container freed on the null path (the
//! `crown-null-from-raw-and-destruction-conflict` shape), and the destructor
//! hands the field to a local free-callee before freeing the container.
#![allow(dead_code, non_camel_case_types, non_snake_case, unused_mut, unused_unsafe)]

extern "C" {
    fn malloc(_: u64) -> *mut std::ffi::c_void;
    fn free(_: *mut std::ffi::c_void);
}

#[repr(C)]
pub struct quadtree_node {
    pub ne: *mut quadtree_node,
    pub nw: *mut quadtree_node,
    pub key: *mut std::ffi::c_void,
}
#[automatically_derived]
impl ::core::marker::Copy for quadtree_node {}
#[automatically_derived]
impl ::core::clone::Clone for quadtree_node {
    #[inline]
    fn clone(&self) -> quadtree_node {
        *self
    }
}

#[repr(C)]
pub struct quadtree {
    pub root: *mut quadtree_node,
    pub length: u32,
}
#[automatically_derived]
impl ::core::marker::Copy for quadtree {}
#[automatically_derived]
impl ::core::clone::Clone for quadtree {
    #[inline]
    fn clone(&self) -> quadtree {
        *self
    }
}

pub unsafe extern "C" fn quadtree_node_with_bounds() -> *mut quadtree_node {
    let mut node = malloc(::std::mem::size_of::<quadtree_node>() as u64) as *mut quadtree_node;
    if node.is_null() { return 0 as *mut quadtree_node; }
    (*node).ne = 0 as *mut quadtree_node;
    (*node).nw = 0 as *mut quadtree_node;
    (*node).key = 0 as *mut std::ffi::c_void;
    return node;
}

pub unsafe extern "C" fn quadtree_node_free(mut node: *mut quadtree_node) {
    if node.is_null() { return; }
    quadtree_node_free((*node).ne);
    quadtree_node_free((*node).nw);
    free(node as *mut std::ffi::c_void);
}

#[no_mangle]
pub unsafe extern "C" fn quadtree_new() -> *mut quadtree {
    let mut tree = 0 as *mut quadtree;
    tree = malloc(::std::mem::size_of::<quadtree>() as u64) as *mut quadtree;
    if tree.is_null() { return 0 as *mut quadtree; }
    (*tree).root = quadtree_node_with_bounds();
    if ((*tree).root).is_null() {
        free(tree as *mut std::ffi::c_void);
        return 0 as *mut quadtree;
    }
    (*tree).length = 0 as i32 as u32;
    return tree;
}

#[no_mangle]
pub unsafe extern "C" fn quadtree_free(mut tree: *mut quadtree) {
    quadtree_node_free((*tree).root);
    free(tree as *mut std::ffi::c_void);
}
