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
    pub mod src {
        pub mod bounds {
            use crate::src::src::point::quadtree_point_free;
            use crate::src::src::point::quadtree_point_new;
            use ::libc;
            extern "C" {
                fn fabs(_: libc::c_double)
                -> libc::c_double;
                fn free(_: *mut libc::c_void);
                fn malloc(_: libc::c_ulong)
                -> *mut libc::c_void;
                fn fmax(_: libc::c_double, _: libc::c_double)
                -> libc::c_double;
                fn fmin(_: libc::c_double, _: libc::c_double)
                -> libc::c_double;
            }
            #[repr(C)]
            pub struct quadtree_point {
                pub x: libc::c_double,
                pub y: libc::c_double,
            }
            #[automatically_derived]
            impl ::core::marker::Copy for quadtree_point { }
            #[automatically_derived]
            impl ::core::clone::Clone for quadtree_point {
                #[inline]
                fn clone(&self) -> quadtree_point {
                    let _: ::core::clone::AssertParamIsClone<libc::c_double>;
                    let _: ::core::clone::AssertParamIsClone<libc::c_double>;
                    *self
                }
            }
            pub type quadtree_point_t = quadtree_point;
            #[repr(C)]
            pub struct quadtree_bounds {
                pub nw: *mut quadtree_point_t,
                pub se: *mut quadtree_point_t,
                pub width: libc::c_double,
                pub height: libc::c_double,
            }
            #[automatically_derived]
            impl ::core::marker::Copy for quadtree_bounds { }
            #[automatically_derived]
            impl ::core::clone::Clone for quadtree_bounds {
                #[inline]
                fn clone(&self) -> quadtree_bounds {
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_point_t>;
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_point_t>;
                    let _: ::core::clone::AssertParamIsClone<libc::c_double>;
                    let _: ::core::clone::AssertParamIsClone<libc::c_double>;
                    *self
                }
            }
            pub type quadtree_bounds_t = quadtree_bounds;
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_bounds_extend(mut bounds:
                    *mut quadtree_bounds_t, mut x: libc::c_double,
                mut y: libc::c_double) {
                (*(*bounds).nw).x = fmin(x, (*(*bounds).nw).x);
                (*(*bounds).nw).y = fmax(y, (*(*bounds).nw).y);
                (*(*bounds).se).x = fmax(x, (*(*bounds).se).x);
                (*(*bounds).se).y = fmin(y, (*(*bounds).se).y);
                (*bounds).width = fabs((*(*bounds).nw).x - (*(*bounds).se).x);
                (*bounds).height =
                    fabs((*(*bounds).nw).y - (*(*bounds).se).y);
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_bounds_free(mut bounds:
                    *mut quadtree_bounds_t) {
                quadtree_point_free((*bounds).nw);
                quadtree_point_free((*bounds).se);
                free(bounds as *mut libc::c_void);
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_bounds_new()
                -> *mut quadtree_bounds_t {
                let mut bounds = 0 as *mut quadtree_bounds_t;
                bounds =
                    malloc(::std::mem::size_of::<quadtree_bounds_t>() as
                                libc::c_ulong) as *mut quadtree_bounds_t;
                if bounds.is_null() { return 0 as *mut quadtree_bounds_t; }
                (*bounds).nw =
                    quadtree_point_new(::std::f32::INFINITY as libc::c_double,
                        -::std::f32::INFINITY as libc::c_double);
                (*bounds).se =
                    quadtree_point_new(-::std::f32::INFINITY as libc::c_double,
                        ::std::f32::INFINITY as libc::c_double);
                (*bounds).width = 0 as libc::c_int as libc::c_double;
                (*bounds).height = 0 as libc::c_int as libc::c_double;
                return bounds;
            }
        }
        pub mod node {
            use crate::src::src::bounds::quadtree_bounds_extend;
            use crate::src::src::bounds::quadtree_bounds_free;
            use crate::src::src::bounds::quadtree_bounds_new;
            use crate::src::src::bounds::quadtree_bounds_t;
            use crate::src::src::bounds::quadtree_point_t;
            use crate::src::src::point::quadtree_point_free;
            use ::libc;
            extern "C" {
                fn free(_: *mut libc::c_void);
                fn malloc(_: libc::c_ulong)
                -> *mut libc::c_void;
            }
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
            #[automatically_derived]
            impl ::core::marker::Copy for quadtree_node { }
            #[automatically_derived]
            impl ::core::clone::Clone for quadtree_node {
                #[inline]
                fn clone(&self) -> quadtree_node {
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_node>;
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_node>;
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_node>;
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_node>;
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_bounds_t>;
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_point_t>;
                    let _: ::core::clone::AssertParamIsClone<*mut libc::c_void>;
                    *self
                }
            }
            pub type quadtree_node_t = quadtree_node;
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_ispointer(mut node:
                    *mut quadtree_node_t) -> libc::c_int {
                return (!((*node).nw).is_null() && !((*node).ne).is_null() &&
                                        !((*node).sw).is_null() && !((*node).se).is_null() &&
                                quadtree_node_isleaf(node) == 0) as libc::c_int;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_isempty(mut node:
                    *mut quadtree_node_t) -> libc::c_int {
                return (((*node).nw).is_null() && ((*node).ne).is_null() &&
                                        ((*node).sw).is_null() && ((*node).se).is_null() &&
                                quadtree_node_isleaf(node) == 0) as libc::c_int;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_isleaf(mut node:
                    *mut quadtree_node_t) -> libc::c_int {
                return ((*node).point !=
                                0 as *mut libc::c_void as *mut quadtree_point_t) as
                        libc::c_int;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_reset(mut node:
                    *mut quadtree_node_t,
                mut key_free:
                    Option<unsafe extern "C" fn(*mut libc::c_void) -> ()>) {
                quadtree_point_free((*node).point);
                (Some(key_free.expect("non-null function pointer"))).expect("non-null function pointer")((*node).key);
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_new()
                -> *mut quadtree_node_t {
                let mut node = 0 as *mut quadtree_node_t;
                node =
                    malloc(::std::mem::size_of::<quadtree_node_t>() as
                                libc::c_ulong) as *mut quadtree_node_t;
                if node.is_null() { return 0 as *mut quadtree_node_t; }
                (*node).ne = 0 as *mut quadtree_node;
                (*node).nw = 0 as *mut quadtree_node;
                (*node).se = 0 as *mut quadtree_node;
                (*node).sw = 0 as *mut quadtree_node;
                (*node).point = 0 as *mut quadtree_point_t;
                (*node).bounds = 0 as *mut quadtree_bounds_t;
                (*node).key = 0 as *mut libc::c_void;
                return node;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_with_bounds(mut minx:
                    libc::c_double, mut miny: libc::c_double,
                mut maxx: libc::c_double, mut maxy: libc::c_double)
                -> *mut quadtree_node_t {
                let mut node = 0 as *mut quadtree_node_t;
                node = quadtree_node_new();
                if node.is_null() { return 0 as *mut quadtree_node_t; }
                (*node).bounds = quadtree_bounds_new();
                if ((*node).bounds).is_null() {
                    return 0 as *mut quadtree_node_t;
                }
                quadtree_bounds_extend((*node).bounds, maxx, maxy);
                quadtree_bounds_extend((*node).bounds, minx, miny);
                return node;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_node_free(mut node:
                    *mut quadtree_node_t,
                mut key_free:
                    Option<unsafe extern "C" fn(*mut libc::c_void) -> ()>) {
                if !((*node).nw).is_null() {
                    quadtree_node_free((*node).nw, key_free);
                }
                if !((*node).ne).is_null() {
                    quadtree_node_free((*node).ne, key_free);
                }
                if !((*node).sw).is_null() {
                    quadtree_node_free((*node).sw, key_free);
                }
                if !((*node).se).is_null() {
                    quadtree_node_free((*node).se, key_free);
                }
                quadtree_bounds_free((*node).bounds);
                quadtree_node_reset(node, key_free);
                free(node as *mut libc::c_void);
            }
        }
        pub mod point {
            use crate::src::src::bounds::quadtree_point_t;
            use ::libc;
            extern "C" {
                fn free(_: *mut libc::c_void);
                fn malloc(_: libc::c_ulong)
                -> *mut libc::c_void;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_point_new(mut x: libc::c_double,
                mut y: libc::c_double) -> *mut quadtree_point_t {
                let mut point = 0 as *mut quadtree_point_t;
                point =
                    malloc(::std::mem::size_of::<quadtree_point_t>() as
                                libc::c_ulong) as *mut quadtree_point_t;
                if point.is_null() { return 0 as *mut quadtree_point_t; }
                (*point).x = x;
                (*point).y = y;
                return point;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_point_free(mut point:
                    *mut quadtree_point_t) {
                free(point as *mut libc::c_void);
            }
        }
        pub mod quadtree {
            use crate::src::src::bounds::quadtree_point_t;
            use crate::src::src::node::quadtree_node_free;
            use crate::src::src::node::quadtree_node_isempty;
            use crate::src::src::node::quadtree_node_isleaf;
            use crate::src::src::node::quadtree_node_ispointer;
            use crate::src::src::node::quadtree_node_reset;
            use crate::src::src::node::quadtree_node_t;
            use crate::src::src::node::quadtree_node_with_bounds;
            use crate::src::src::point::quadtree_point_new;
            use ::libc;
            extern "C" {
                fn malloc(_: libc::c_ulong)
                -> *mut libc::c_void;
                fn free(_: *mut libc::c_void);
            }
            #[repr(C)]
            pub struct quadtree {
                pub root: *mut quadtree_node_t,
                pub key_free: Option<unsafe extern "C" fn(*mut libc::c_void)
                    -> ()>,
                pub length: libc::c_uint,
            }
            #[automatically_derived]
            impl ::core::marker::Copy for quadtree { }
            #[automatically_derived]
            impl ::core::clone::Clone for quadtree {
                #[inline]
                fn clone(&self) -> quadtree {
                    let _:
                            ::core::clone::AssertParamIsClone<*mut quadtree_node_t>;
                    let _:
                            ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(*mut libc::c_void)
                                -> ()>>;
                    let _: ::core::clone::AssertParamIsClone<libc::c_uint>;
                    *self
                }
            }
            pub type quadtree_t = quadtree;
            unsafe extern "C" fn node_contains_(mut outer:
                    *mut quadtree_node_t, mut it: *mut quadtree_point_t)
                -> libc::c_int {
                return (!((*outer).bounds).is_null() &&
                                            (*(*(*outer).bounds).nw).x < (*it).x &&
                                        (*(*(*outer).bounds).nw).y > (*it).y &&
                                    (*(*(*outer).bounds).se).x > (*it).x &&
                                (*(*(*outer).bounds).se).y < (*it).y) as libc::c_int;
            }
            unsafe extern "C" fn elision_(mut key: *mut libc::c_void) {}
            unsafe extern "C" fn reset_node_(mut tree: *mut quadtree_t,
                mut node: *mut quadtree_node_t) {
                if ((*tree).key_free).is_some() {
                    quadtree_node_reset(node, (*tree).key_free);
                } else {
                    quadtree_node_reset(node,
                        Some(elision_ as
                                unsafe extern "C" fn(*mut libc::c_void) -> ()));
                };
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
            unsafe extern "C" fn split_node_(mut tree: *mut quadtree_t,
                mut node: *mut quadtree_node_t) -> libc::c_int {
                let mut nw = 0 as *mut quadtree_node_t;
                let mut ne = 0 as *mut quadtree_node_t;
                let mut sw = 0 as *mut quadtree_node_t;
                let mut se = 0 as *mut quadtree_node_t;
                let mut x = (*(*(*node).bounds).nw).x;
                let mut y = (*(*(*node).bounds).nw).y;
                let mut hw =
                    (*(*node).bounds).width /
                        2 as libc::c_int as libc::c_double;
                let mut hh =
                    (*(*node).bounds).height /
                        2 as libc::c_int as libc::c_double;
                nw = quadtree_node_with_bounds(x, y - hh, x + hw, y);
                if nw.is_null() { return 0 as libc::c_int; }
                ne =
                    quadtree_node_with_bounds(x + hw, y - hh,
                        x + hw * 2 as libc::c_int as libc::c_double, y);
                if ne.is_null() { return 0 as libc::c_int; }
                sw =
                    quadtree_node_with_bounds(x,
                        y - hh * 2 as libc::c_int as libc::c_double, x + hw,
                        y - hh);
                if sw.is_null() { return 0 as libc::c_int; }
                se =
                    quadtree_node_with_bounds(x + hw,
                        y - hh * 2 as libc::c_int as libc::c_double,
                        x + hw * 2 as libc::c_int as libc::c_double, y - hh);
                if se.is_null() { return 0 as libc::c_int; }
                (*node).nw = nw;
                (*node).ne = ne;
                (*node).sw = sw;
                (*node).se = se;
                let mut old = (*node).point;
                let mut key = (*node).key;
                (*node).point = 0 as *mut quadtree_point_t;
                (*node).key = 0 as *mut libc::c_void;
                return insert_(tree, node, old, key);
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
            unsafe extern "C" fn insert_(mut tree: *mut quadtree_t,
                mut root: *mut quadtree_node_t,
                mut point: *mut quadtree_point_t, mut key: *mut libc::c_void)
                -> libc::c_int {
                if quadtree_node_isempty(root) != 0 {
                    (*root).point = point;
                    (*root).key = key;
                    return 1 as libc::c_int;
                } else {
                    if quadtree_node_isleaf(root) != 0 {
                        if (*(*root).point).x == (*point).x &&
                                (*(*root).point).y == (*point).y {
                            reset_node_(tree, root);
                            (*root).point = point;
                            (*root).key = key;
                            return 0 as libc::c_int;
                        } else {
                            if split_node_(tree, root) == 0 { return 0 as libc::c_int; }
                            return insert_(tree, root, point, key);
                        }
                    } else {
                        if quadtree_node_ispointer(root) != 0 {
                            let mut quadrant = get_quadrant_(root, point);
                            return if quadrant.is_null() {
                                    0 as libc::c_int
                                } else { insert_(tree, quadrant, point, key) };
                        }
                    }
                }
                return 0 as libc::c_int;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_new(mut minx: libc::c_double,
                mut miny: libc::c_double, mut maxx: libc::c_double,
                mut maxy: libc::c_double) -> *mut quadtree_t {
                let mut tree = 0 as *mut quadtree_t;
                tree =
                    malloc(::std::mem::size_of::<quadtree_t>() as libc::c_ulong)
                        as *mut quadtree_t;
                if tree.is_null() { return 0 as *mut quadtree_t; }
                (*tree).root =
                    quadtree_node_with_bounds(minx, miny, maxx, maxy);
                if ((*tree).root).is_null() {
                    free(tree as *mut libc::c_void);
                    return 0 as *mut quadtree_t;
                }
                (*tree).key_free = None;
                (*tree).length = 0 as libc::c_int as libc::c_uint;
                return tree;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_insert(mut tree:
                    *mut quadtree_t, mut x: libc::c_double,
                mut y: libc::c_double, mut key: *mut libc::c_void)
                -> libc::c_int {
                let mut point = 0 as *mut quadtree_point_t;
                point = quadtree_point_new(x, y);
                if point.is_null() { return 0 as libc::c_int; }
                if node_contains_((*tree).root, point) == 0 {
                    return 0 as libc::c_int;
                }
                if insert_(tree, (*tree).root, point, key) == 0 {
                    return 0 as libc::c_int;
                }
                (*tree).length = ((*tree).length).wrapping_add(1);
                return 1 as libc::c_int;
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_search(mut tree:
                    *mut quadtree_t, mut x: libc::c_double,
                mut y: libc::c_double) -> *mut quadtree_point_t {
                return find_((*tree).root, x, y);
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_free(mut tree:
                    *mut quadtree_t) {
                if ((*tree).key_free).is_some() {
                    quadtree_node_free((*tree).root, (*tree).key_free);
                } else {
                    quadtree_node_free((*tree).root,
                        Some(elision_ as
                                unsafe extern "C" fn(*mut libc::c_void) -> ()));
                }
                free(tree as *mut libc::c_void);
            }
            #[no_mangle]
            pub unsafe extern "C" fn quadtree_walk(mut root:
                    *mut quadtree_node_t,
                mut descent:
                    Option<unsafe extern "C" fn(*mut quadtree_node_t) -> ()>,
                mut ascent:
                    Option<unsafe extern "C" fn(*mut quadtree_node_t) -> ()>) {
                (Some(descent.expect("non-null function pointer"))).expect("non-null function pointer")(root);
                if !((*root).nw).is_null() {
                    quadtree_walk((*root).nw, descent, ascent);
                }
                if !((*root).ne).is_null() {
                    quadtree_walk((*root).ne, descent, ascent);
                }
                if !((*root).sw).is_null() {
                    quadtree_walk((*root).sw, descent, ascent);
                }
                if !((*root).se).is_null() {
                    quadtree_walk((*root).se, descent, ascent);
                }
                (Some(ascent.expect("non-null function pointer"))).expect("non-null function pointer")(root);
            }
        }
    }
    pub mod test {
        use crate::src::src::bounds::quadtree_bounds_extend;
        use crate::src::src::bounds::quadtree_bounds_free;
        use crate::src::src::bounds::quadtree_bounds_new;
        use crate::src::src::bounds::quadtree_bounds_t;
        use crate::src::src::bounds::quadtree_point_t;
        use crate::src::src::node::quadtree_node_isempty;
        use crate::src::src::node::quadtree_node_isleaf;
        use crate::src::src::node::quadtree_node_ispointer;
        use crate::src::src::node::quadtree_node_new;
        use crate::src::src::node::quadtree_node_t;
        use crate::src::src::point::quadtree_point_free;
        use crate::src::src::point::quadtree_point_new;
        use crate::src::src::quadtree::quadtree_free;
        use crate::src::src::quadtree::quadtree_insert;
        use crate::src::src::quadtree::quadtree_new;
        use crate::src::src::quadtree::quadtree_search;
        use crate::src::src::quadtree::quadtree_t;
        use crate::src::src::quadtree::quadtree_walk;
        use ::libc;
        extern "C" {
            fn __assert_fail(__assertion: *const libc::c_char,
            __file: *const libc::c_char, __line: libc::c_uint,
            __function: *const libc::c_char)
            -> !;
            fn printf(_: *const libc::c_char, _: ...)
            -> libc::c_int;
            fn puts(__s: *const libc::c_char)
            -> libc::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn descent(mut node: *mut quadtree_node_t) {
            if !((*node).bounds).is_null() {
                printf(b"{ nw.x:%f, nw.y:%f, se.x:%f, se.y:%f }: \0" as
                            *const u8 as *const libc::c_char, (*(*(*node).bounds).nw).x,
                    (*(*(*node).bounds).nw).y, (*(*(*node).bounds).se).x,
                    (*(*(*node).bounds).se).y);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn ascent(mut node: *mut quadtree_node_t) {
            printf(b"\n\0" as *const u8 as *const libc::c_char);
        }
        unsafe extern "C" fn test_node() {
            let mut node = quadtree_node_new();
            if quadtree_node_isleaf(node) == 0
                {} else {
                __assert_fail(b"!quadtree_node_isleaf(node)\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    26 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'n' as i8, b'o' as i8, b'd' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_node_isempty(node) != 0
                {} else {
                __assert_fail(b"quadtree_node_isempty(node)\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    27 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'n' as i8, b'o' as i8, b'd' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_node_ispointer(node) == 0
                {} else {
                __assert_fail(b"!quadtree_node_ispointer(node)\0" as *const u8
                        as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    28 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'n' as i8, b'o' as i8, b'd' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
        }
        unsafe extern "C" fn test_bounds() {
            let mut bounds = quadtree_bounds_new();
            if !bounds.is_null()
                {} else {
                __assert_fail(b"bounds\0" as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    35 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*(*bounds).nw).x == ::std::f32::INFINITY as libc::c_double
                {} else {
                __assert_fail(b"bounds->nw->x == INFINITY\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    36 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*(*bounds).se).x == -::std::f32::INFINITY as libc::c_double
                {} else {
                __assert_fail(b"bounds->se->x == -INFINITY\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    37 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            quadtree_bounds_extend(bounds, 5.0f64, 5.0f64);
            if (*(*bounds).nw).x == 5.0f64
                {} else {
                __assert_fail(b"bounds->nw->x == 5.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    40 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*(*bounds).se).x == 5.0f64
                {} else {
                __assert_fail(b"bounds->se->x == 5.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    41 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            quadtree_bounds_extend(bounds, 10.0f64, 10.0f64);
            if (*(*bounds).nw).y == 10.0f64
                {} else {
                __assert_fail(b"bounds->nw->y == 10.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    44 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*(*bounds).nw).y == 10.0f64
                {} else {
                __assert_fail(b"bounds->nw->y == 10.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    45 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*(*bounds).se).y == 5.0f64
                {} else {
                __assert_fail(b"bounds->se->y == 5.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    46 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*(*bounds).se).y == 5.0f64
                {} else {
                __assert_fail(b"bounds->se->y == 5.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    47 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*bounds).width == 5.0f64
                {} else {
                __assert_fail(b"bounds->width == 5.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    49 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*bounds).height == 5.0f64
                {} else {
                __assert_fail(b"bounds->height == 5.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    50 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'b' as i8, b'o' as i8, b'u' as i8, b'n' as i8,
                                    b'd' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            quadtree_bounds_free(bounds);
        }
        unsafe extern "C" fn test_tree() {
            let mut val = 10 as libc::c_int;
            let mut tree =
                quadtree_new(1 as libc::c_int as libc::c_double,
                    1 as libc::c_int as libc::c_double,
                    10 as libc::c_int as libc::c_double,
                    10 as libc::c_int as libc::c_double);
            if (*(*(*(*tree).root).bounds).nw).x ==
                    1 as libc::c_int as libc::c_double
                {} else {
                __assert_fail(b"tree->root->bounds->nw->x == 1\0" as *const u8
                        as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    61 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*(*(*(*tree).root).bounds).nw).y == 10.0f64
                {} else {
                __assert_fail(b"tree->root->bounds->nw->y == 10.0\0" as
                            *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    62 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*(*(*(*tree).root).bounds).se).x == 10.0f64
                {} else {
                __assert_fail(b"tree->root->bounds->se->x == 10.0\0" as
                            *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    63 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*(*(*(*tree).root).bounds).se).y ==
                    1 as libc::c_int as libc::c_double
                {} else {
                __assert_fail(b"tree->root->bounds->se->y == 1\0" as *const u8
                        as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    64 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 0 as libc::c_int as libc::c_double,
                        0 as libc::c_int as libc::c_double,
                        &mut val as *mut libc::c_int as *mut libc::c_void) ==
                    0 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 0, 0, &val) == 0\0" as
                            *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    67 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 10 as libc::c_int as libc::c_double,
                        10 as libc::c_int as libc::c_double,
                        &mut val as *mut libc::c_int as *mut libc::c_void) ==
                    0 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 10, 10, &val) == 0\0" as
                            *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    68 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 110.0f64, 110.0f64,
                        &mut val as *mut libc::c_int as *mut libc::c_void) ==
                    0 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 110.0, 110.0, &val) == 0\0"
                            as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    69 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 8.0f64, 2.0f64,
                        &mut val as *mut libc::c_int as *mut libc::c_void) !=
                    0 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 8.0, 2.0, &val) != 0\0"
                            as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    71 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*tree).length == 1 as libc::c_int as libc::c_uint
                {} else {
                __assert_fail(b"tree->length == 1\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    72 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*(*(*tree).root).point).x == 8.0f64
                {} else {
                __assert_fail(b"tree->root->point->x == 8.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    73 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*(*(*tree).root).point).y == 2.0f64
                {} else {
                __assert_fail(b"tree->root->point->y == 2.0\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    74 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 2.0f64, 3.0f64,
                        &mut val as *mut libc::c_int as *mut libc::c_void) !=
                    0 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 2.0, 3.0, &val) != 0\0"
                            as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    76 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 2.0f64, 3.0f64,
                        &mut val as *mut libc::c_int as *mut libc::c_void) ==
                    0 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 2.0, 3.0, &val) == 0\0"
                            as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    77 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*tree).length == 2 as libc::c_int as libc::c_uint
                {} else {
                __assert_fail(b"tree->length == 2\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    78 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if ((*(*tree).root).point).is_null()
                {} else {
                __assert_fail(b"tree->root->point == NULL\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    79 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if quadtree_insert(tree, 3.0f64, 1.1f64,
                        &mut val as *mut libc::c_int as *mut libc::c_void) ==
                    1 as libc::c_int
                {} else {
                __assert_fail(b"quadtree_insert(tree, 3.0, 1.1, &val) == 1\0"
                            as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    81 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*tree).length == 3 as libc::c_int as libc::c_uint
                {} else {
                __assert_fail(b"tree->length == 3\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    82 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            if (*quadtree_search(tree, 3.0f64, 1.1f64)).x == 3.0f64
                {} else {
                __assert_fail(b"quadtree_search(tree, 3.0, 1.1)->x == 3.0\0"
                            as *const u8 as *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    83 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b't' as i8, b'r' as i8, b'e' as i8, b'e' as i8,
                                    b'(' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            };
            quadtree_walk((*tree).root,
                Some(ascent as
                        unsafe extern "C" fn(*mut quadtree_node_t) -> ()),
                Some(descent as
                        unsafe extern "C" fn(*mut quadtree_node_t) -> ()));
            quadtree_free(tree);
        }
        unsafe extern "C" fn test_points() {
            let mut point =
                quadtree_point_new(5 as libc::c_int as libc::c_double,
                    6 as libc::c_int as libc::c_double);
            if (*point).x == 5 as libc::c_int as libc::c_double
                {} else {
                __assert_fail(b"point->x == 5\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    91 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'p' as i8, b'o' as i8, b'i' as i8, b'n' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            if (*point).y == 6 as libc::c_int as libc::c_double
                {} else {
                __assert_fail(b"point->y == 6\0" as *const u8 as
                        *const libc::c_char,
                    b"test.c\0" as *const u8 as *const libc::c_char,
                    92 as libc::c_int as libc::c_uint,
                    ([b'v' as i8, b'o' as i8, b'i' as i8, b'd' as i8,
                                    b' ' as i8, b't' as i8, b'e' as i8, b's' as i8, b't' as i8,
                                    b'_' as i8, b'p' as i8, b'o' as i8, b'i' as i8, b'n' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            };
            quadtree_point_free(point);
        }
        unsafe fn main_0(mut argc: libc::c_int,
            mut argv: *mut *const libc::c_char) -> libc::c_int {
            printf(b"\nquadtree_t: %ld\n\0" as *const u8 as
                    *const libc::c_char,
                ::std::mem::size_of::<quadtree_t>() as libc::c_ulong);
            printf(b"quadtree_node_t: %ld\n\0" as *const u8 as
                    *const libc::c_char,
                ::std::mem::size_of::<quadtree_node_t>() as libc::c_ulong);
            printf(b"quadtree_bounds_t: %ld\n\0" as *const u8 as
                    *const libc::c_char,
                ::std::mem::size_of::<quadtree_bounds_t>() as libc::c_ulong);
            printf(b"quadtree_point_t: %ld\n\0" as *const u8 as
                    *const libc::c_char,
                ::std::mem::size_of::<quadtree_point_t>() as libc::c_ulong);
            printf(b"\x1B[33mtree\x1B[0m \0" as *const u8 as
                    *const libc::c_char);
            test_tree();
            puts(b"\x1B[1;32m \xE2\x9C\x93 \x1B[0m\0" as *const u8 as
                    *const libc::c_char);
            printf(b"\x1B[33mnode\x1B[0m \0" as *const u8 as
                    *const libc::c_char);
            test_node();
            puts(b"\x1B[1;32m \xE2\x9C\x93 \x1B[0m\0" as *const u8 as
                    *const libc::c_char);
            printf(b"\x1B[33mbounds\x1B[0m \0" as *const u8 as
                    *const libc::c_char);
            test_bounds();
            puts(b"\x1B[1;32m \xE2\x9C\x93 \x1B[0m\0" as *const u8 as
                    *const libc::c_char);
            printf(b"\x1B[33mpoints\x1B[0m \0" as *const u8 as
                    *const libc::c_char);
            test_points();
            puts(b"\x1B[1;32m \xE2\x9C\x93 \x1B[0m\0" as *const u8 as
                    *const libc::c_char);
            return 0;
        }
    }
}