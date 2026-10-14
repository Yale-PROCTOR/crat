extern "C" {
    fn REFINATOR_MALLOC_rbtree() -> *mut rbtree;
    fn REFINATOR_MALLOC_node_t() -> *mut node_t;
    fn REFINATOR_FREE_rbtree(t: *mut rbtree) -> ::core::ffi::c_int;
    fn REFINATOR_FREE_node_t(n: *mut node_t) -> ::core::ffi::c_int;
}
pub type __key_t = ::core::ffi::c_int;
pub type key_t = __key_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct node_t {
    pub color: ::core::ffi::c_int,
    pub key: key_t,
    pub parent: *mut node_t,
    pub left: *mut node_t,
    pub right: *mut node_t,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct rbtree {
    pub root: *mut node_t,
    pub nil: *mut node_t,
}
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<
    ::core::ffi::c_void,
>();
#[no_mangle]
pub static mut RBTREE_RED: ::core::ffi::c_int = 0 as ::core::ffi::c_int;
#[no_mangle]
pub static mut RBTREE_BLACK: ::core::ffi::c_int = 1 as ::core::ffi::c_int;
#[no_mangle]
pub unsafe extern "C" fn new_rbtree() -> *mut rbtree {
    let mut p = REFINATOR_MALLOC_rbtree();
    let mut nilNode = REFINATOR_MALLOC_node_t();
    (*nilNode).color = RBTREE_BLACK;
    (*p).nil = nilNode;
    (*p).root = nilNode;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn right_rotation(mut tree: *mut rbtree, mut x: *mut node_t) {
    let mut y = ::core::ptr::null_mut::<node_t>();
    y = (*x).left as *mut node_t;
    (*x).left = (*y).right;
    if (*y).right != (*tree).nil {
        (*(*y).right).parent = x as *mut node_t;
    }
    (*y).parent = (*x).parent;
    if (*x).parent == (*tree).nil {
        (*tree).root = y;
    } else if x == (*(*x).parent).left {
        (*(*x).parent).left = y as *mut node_t;
    } else {
        (*(*x).parent).right = y as *mut node_t;
    }
    (*y).right = x as *mut node_t;
    (*x).parent = y as *mut node_t;
}
#[no_mangle]
pub unsafe extern "C" fn left_rotation(mut tree: *mut rbtree, mut x: *mut node_t) {
    let mut y = ::core::ptr::null_mut::<node_t>();
    y = (*x).right as *mut node_t;
    (*x).right = (*y).left;
    if (*y).left != (*tree).nil {
        (*(*y).left).parent = x as *mut node_t;
    }
    (*y).parent = (*x).parent;
    if (*x).parent == (*tree).nil {
        (*tree).root = y;
    } else if x == (*(*x).parent).left {
        (*(*x).parent).left = y as *mut node_t;
    } else {
        (*(*x).parent).right = y as *mut node_t;
    }
    (*y).left = x as *mut node_t;
    (*x).parent = y as *mut node_t;
}
#[no_mangle]
pub unsafe extern "C" fn REFINATOR_FREE_node(mut t: *mut rbtree, mut x: *mut node_t) {
    if (*x).left != (*t).nil {
        REFINATOR_FREE_node(t, (*x).left as *mut node_t);
    }
    if (*x).right != (*t).nil {
        REFINATOR_FREE_node(t, (*x).right as *mut node_t);
    }
    REFINATOR_FREE_node_t(x);
    x = ::core::ptr::null_mut::<node_t>();
}
#[no_mangle]
pub unsafe extern "C" fn delete_rbtree(mut t: *mut rbtree) {
    if (*t).root != (*t).nil {
        REFINATOR_FREE_node(t, (*t).root);
    }
    REFINATOR_FREE_node_t((*t).nil);
    REFINATOR_FREE_rbtree(t);
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_insert_fixup(mut t: *mut rbtree, mut z: *mut node_t) {
    let mut y = ::core::ptr::null_mut::<node_t>();
    while (*(*z).parent).color == RBTREE_RED {
        if (*z).parent == (*(*(*z).parent).parent).left {
            y = (*(*(*z).parent).parent).right as *mut node_t;
            if (*y).color == RBTREE_RED {
                (*(*z).parent).color = RBTREE_BLACK;
                (*y).color = RBTREE_BLACK;
                (*(*(*z).parent).parent).color = RBTREE_RED;
                z = (*(*z).parent).parent as *mut node_t;
            } else {
                if z == (*(*z).parent).right {
                    z = (*z).parent as *mut node_t;
                    left_rotation(t, z);
                }
                (*(*z).parent).color = RBTREE_BLACK;
                (*(*(*z).parent).parent).color = RBTREE_RED;
                right_rotation(t, (*(*z).parent).parent as *mut node_t);
            }
        } else {
            y = (*(*(*z).parent).parent).left as *mut node_t;
            if (*y).color == RBTREE_RED {
                (*(*z).parent).color = RBTREE_BLACK;
                (*y).color = RBTREE_BLACK;
                (*(*(*z).parent).parent).color = RBTREE_RED;
                z = (*(*z).parent).parent as *mut node_t;
            } else {
                if z == (*(*z).parent).left {
                    z = (*z).parent as *mut node_t;
                    right_rotation(t, z);
                }
                (*(*z).parent).color = RBTREE_BLACK;
                (*(*(*z).parent).parent).color = RBTREE_RED;
                left_rotation(t, (*(*z).parent).parent as *mut node_t);
            }
        }
    }
    (*(*t).root).color = RBTREE_BLACK;
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_insert(mut t: *mut rbtree, key: key_t) -> *mut node_t {
    let mut y = (*t).nil;
    let mut x = (*t).root;
    let mut z = REFINATOR_MALLOC_node_t();
    (*z).key = key;
    while x != (*t).nil {
        y = x;
        if (*z).key < (*x).key {
            x = (*x).left as *mut node_t;
        } else {
            x = (*x).right as *mut node_t;
        }
    }
    (*z).parent = y as *mut node_t;
    if y == (*t).nil {
        (*t).root = z;
    } else if (*z).key < (*y).key {
        (*y).left = z as *mut node_t;
    } else {
        (*y).right = z as *mut node_t;
    }
    (*z).left = (*t).nil as *mut node_t;
    (*z).right = (*t).nil as *mut node_t;
    (*z).color = RBTREE_RED;
    rbtree_insert_fixup(t, z);
    return z;
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_find(mut t: *const rbtree, key: key_t) -> *mut node_t {
    let mut current = (*t).root;
    while current != (*t).nil {
        if (*current).key == key {
            return current;
        }
        if (*current).key < key {
            current = (*current).right as *mut node_t;
        } else {
            current = (*current).left as *mut node_t;
        }
    }
    return ::core::ptr::null_mut::<node_t>();
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_min(mut t: *const rbtree) -> *mut node_t {
    if (*t).root == (*t).nil {
        return ::core::ptr::null_mut::<node_t>();
    }
    let mut curr = (*t).root;
    while (*curr).left != (*t).nil {
        curr = (*curr).left as *mut node_t;
    }
    return curr;
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_max(mut t: *const rbtree) -> *mut node_t {
    if (*t).root == (*t).nil {
        return ::core::ptr::null_mut::<node_t>();
    }
    let mut curr = (*t).root;
    while (*curr).right != (*t).nil {
        curr = (*curr).right as *mut node_t;
    }
    return curr;
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_transplant(
    mut t: *mut rbtree,
    mut u: *mut node_t,
    mut v: *mut node_t,
) {
    if (*u).parent == (*t).nil {
        (*t).root = v;
    } else if u == (*(*u).parent).left {
        (*(*u).parent).left = v as *mut node_t;
    } else {
        (*(*u).parent).right = v as *mut node_t;
    }
    (*v).parent = (*u).parent;
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_delete_fixup(mut t: *mut rbtree, mut x: *mut node_t) {
    while x != (*t).root && (*x).color == RBTREE_BLACK {
        if x == (*(*x).parent).left {
            let mut w = (*(*x).parent).right as *mut node_t;
            if (*w).color == RBTREE_RED {
                (*w).color = RBTREE_BLACK;
                (*(*x).parent).color = RBTREE_RED;
                left_rotation(t, (*x).parent as *mut node_t);
                w = (*(*x).parent).right as *mut node_t;
            }
            if (*(*w).left).color == RBTREE_BLACK && (*(*w).right).color == RBTREE_BLACK
            {
                (*w).color = RBTREE_RED;
                x = (*x).parent as *mut node_t;
            } else {
                if (*(*w).right).color == RBTREE_BLACK {
                    (*(*w).left).color = RBTREE_BLACK;
                    (*w).color = RBTREE_RED;
                    right_rotation(t, w);
                    w = (*(*x).parent).right as *mut node_t;
                }
                (*w).color = (*(*x).parent).color;
                (*(*x).parent).color = RBTREE_BLACK;
                (*(*w).right).color = RBTREE_BLACK;
                left_rotation(t, (*x).parent as *mut node_t);
                x = (*t).root;
            }
        } else {
            let mut w_0 = (*(*x).parent).left as *mut node_t;
            if (*w_0).color == RBTREE_RED {
                (*w_0).color = RBTREE_BLACK;
                (*(*x).parent).color = RBTREE_RED;
                right_rotation(t, (*x).parent as *mut node_t);
                w_0 = (*(*x).parent).left as *mut node_t;
            }
            if (*(*w_0).right).color == RBTREE_BLACK
                && (*(*w_0).left).color == RBTREE_BLACK
            {
                (*w_0).color = RBTREE_RED;
                x = (*x).parent as *mut node_t;
            } else {
                if (*(*w_0).left).color == RBTREE_BLACK {
                    (*(*w_0).right).color = RBTREE_BLACK;
                    (*w_0).color = RBTREE_RED;
                    left_rotation(t, w_0);
                    w_0 = (*(*x).parent).left as *mut node_t;
                }
                (*w_0).color = (*(*x).parent).color;
                (*(*x).parent).color = RBTREE_BLACK;
                (*(*w_0).left).color = RBTREE_BLACK;
                right_rotation(t, (*x).parent as *mut node_t);
                x = (*t).root;
            }
        }
    }
    (*x).color = RBTREE_BLACK;
}
#[no_mangle]
pub unsafe extern "C" fn rbtree_erase(
    mut t: *mut rbtree,
    mut p: *mut node_t,
) -> ::core::ffi::c_int {
    let mut y = ::core::ptr::null_mut::<node_t>();
    let mut x = ::core::ptr::null_mut::<node_t>();
    let mut yOriginalColor: ::core::ffi::c_int = 0;
    y = p;
    yOriginalColor = (*y).color;
    if (*p).left == (*t).nil {
        x = (*p).right as *mut node_t;
        rbtree_transplant(t, p, (*p).right as *mut node_t);
    } else if (*p).right == (*t).nil {
        x = (*p).left as *mut node_t;
        rbtree_transplant(t, p, (*p).left as *mut node_t);
    } else {
        y = (*p).right as *mut node_t;
        while (*y).left != (*t).nil {
            y = (*y).left as *mut node_t;
        }
        yOriginalColor = (*y).color;
        x = (*y).right as *mut node_t;
        if (*y).parent == p {
            (*x).parent = y as *mut node_t;
        } else {
            rbtree_transplant(t, y, (*y).right as *mut node_t);
            (*y).right = (*p).right;
            (*(*y).right).parent = y as *mut node_t;
        }
        rbtree_transplant(t, p, y);
        (*y).left = (*p).left;
        (*(*y).left).parent = y as *mut node_t;
        (*y).color = (*p).color;
    }
    if yOriginalColor == RBTREE_BLACK {
        rbtree_delete_fixup(t, x);
    }
    REFINATOR_FREE_node_t(p);
    return 0 as ::core::ffi::c_int;
}
