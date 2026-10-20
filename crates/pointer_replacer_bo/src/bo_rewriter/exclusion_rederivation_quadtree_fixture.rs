//! quadtree `find_` / `get_quadrant_` — relay 025's three
//! `cross-class-interval-collision` rows (`find_::node`, `get_quadrant_::{root,
//! point}`), copied verbatim from the derived substrate (lib.rs 36–60, 128–181,
//! 309–316, 329–343, 385–399, `insert_` 400–430 reduced to the write through
//! `root` and the recursion through the quadrant) with the structs they need. The
//! recursive call `find_(get_quadrant_(node, &mut test), x, y)` carries
//! `find_`'s `c` reborrow of the raw-returning call (`c-raw-reborrow-mut`,
//! 18271..18301 in the corpus program) over `get_quadrant_`'s argument adapter
//! `&mut test` → `&test` (`shared-weakening`, 18291..18300): a strict
//! containment in one caller.
pub(super) const QUADTREE_FIND: &str = r#"#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
#[repr(C)]
pub struct quadtree_point {
    pub x: libc::c_double,
    pub y: libc::c_double,
}
impl ::core::marker::Copy for quadtree_point {}
impl ::core::clone::Clone for quadtree_point {
    fn clone(&self) -> quadtree_point { *self }
}
pub type quadtree_point_t = quadtree_point;
#[repr(C)]
pub struct quadtree_bounds {
    pub nw: *mut quadtree_point_t,
    pub se: *mut quadtree_point_t,
    pub width: libc::c_double,
    pub height: libc::c_double,
}
impl ::core::marker::Copy for quadtree_bounds {}
impl ::core::clone::Clone for quadtree_bounds {
    fn clone(&self) -> quadtree_bounds { *self }
}
pub type quadtree_bounds_t = quadtree_bounds;
#[repr(C)]
pub struct quadtree_node {
    pub ne: *mut quadtree_node,
    pub nw: *mut quadtree_node,
    pub se: *mut quadtree_node,
    pub sw: *mut quadtree_node,
    pub bounds: *mut quadtree_bounds_t,
    pub point: *mut quadtree_point_t,
    pub key: *mut libc::c_void,
}
impl ::core::marker::Copy for quadtree_node {}
impl ::core::clone::Clone for quadtree_node {
    fn clone(&self) -> quadtree_node { *self }
}
pub type quadtree_node_t = quadtree_node;
#[no_mangle]
pub unsafe extern "C" fn quadtree_node_isleaf(mut node:
        *mut quadtree_node_t) -> libc::c_int {
    return ((*node).point !=
                    0 as *mut libc::c_void as *mut quadtree_point_t) as
            libc::c_int;
}
unsafe extern "C" fn node_contains_(mut outer:
        *mut quadtree_node_t, mut it: *mut quadtree_point_t)
    -> libc::c_int {
    return (!((*outer).bounds).is_null() &&
                                (*(*(*outer).bounds).nw).x < (*it).x &&
                            (*(*(*outer).bounds).nw).y > (*it).y &&
                        (*(*(*outer).bounds).se).x > (*it).x &&
                    (*(*(*outer).bounds).se).y < (*it).y) as libc::c_int;
}
unsafe extern "C" fn get_quadrant_(mut root: *mut quadtree_node_t,
    mut point: *mut quadtree_point_t) -> *mut quadtree_node_t {
    if node_contains_((*root).nw, point) != 0 {
        return (*root).nw;
    }
    if node_contains_((*root).ne, point) != 0 {
        return (*root).ne;
    }
    if node_contains_((*root).sw, point) != 0 {
        return (*root).sw;
    }
    if node_contains_((*root).se, point) != 0 {
        return (*root).se;
    }
    return 0 as *mut quadtree_node_t;
}
unsafe extern "C" fn find_(mut node: *mut quadtree_node_t,
    mut x: libc::c_double, mut y: libc::c_double)
    -> *mut quadtree_point_t {
    if quadtree_node_isleaf(node) != 0 {
        if (*(*node).point).x == x && (*(*node).point).y == y {
            return (*node).point;
        }
    } else {
        let mut test = quadtree_point_t { x: 0., y: 0. };
        test.x = x;
        test.y = y;
        return find_(get_quadrant_(node, &mut test), x, y);
    }
    return 0 as *mut quadtree_point_t;
}
unsafe extern "C" fn insert_(mut root: *mut quadtree_node_t,
    mut point: *mut quadtree_point_t) -> libc::c_int {
    if quadtree_node_isleaf(root) == 0 {
        (*root).point = point;
        return 1 as libc::c_int;
    } else {
        let mut quadrant = get_quadrant_(root, point);
        return if quadrant.is_null() {
                0 as libc::c_int
            } else { insert_(quadrant, point) };
    }
}
#[no_mangle]
pub unsafe extern "C" fn quadtree_search(mut root: *mut quadtree_node_t,
    mut x: libc::c_double, mut y: libc::c_double) -> *mut quadtree_point_t {
    return find_(root, x, y);
}
"#;
