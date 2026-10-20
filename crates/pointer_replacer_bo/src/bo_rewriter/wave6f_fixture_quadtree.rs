#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
pub struct quadtree_node {
    pub ne: *mut quadtree_node,
    pub nw: *mut quadtree_node,
    pub value: i32,
}
#[automatically_derived]
impl ::core::marker::Copy for quadtree_node { }
#[automatically_derived]
impl ::core::clone::Clone for quadtree_node {
    #[inline]
    fn clone(&self) -> quadtree_node {
        let _: ::core::clone::AssertParamIsClone<*mut quadtree_node>;
        let _: ::core::clone::AssertParamIsClone<i32>;
        *self
    }
}
pub type quadtree_node_t = quadtree_node;
#[no_mangle]
pub unsafe extern "C" fn quadtree_walk(mut root: *mut quadtree_node_t,
    mut descent: Option<unsafe extern "C" fn(*mut quadtree_node_t) -> ()>,
    mut ascent: Option<unsafe extern "C" fn(*mut quadtree_node_t) -> ()>) {
    (Some(descent.expect("non-null function pointer"))).expect("non-null function pointer")(root);
    if !((*root).nw).is_null() {
        quadtree_walk((*root).nw, descent, ascent);
    }
    if !((*root).ne).is_null() {
        quadtree_walk((*root).ne, descent, ascent);
    }
    (Some(ascent.expect("non-null function pointer"))).expect("non-null function pointer")(root);
}
unsafe extern "C" fn bump(mut node: *mut quadtree_node_t) {
    (*node).value += 1;
}
#[no_mangle]
pub unsafe extern "C" fn walk_all(mut root: *mut quadtree_node_t) {
    quadtree_walk(root, Some(bump as unsafe extern "C" fn(*mut quadtree_node_t) -> ()), Some(bump as unsafe extern "C" fn(*mut quadtree_node_t) -> ()));
}
