// w6f-avl-frame
// avl's `src/avl.rs` as the derived substrate spells it
// (`benchmarks/rs-crown-derived/avl/lib.rs`): the rotation pair era-5b named
// `TerminalRoleC` — a field moved out, stored into the other node, and the
// rotated owner returned — plus `insert`'s recursive stores and the `height`
// / `getBalance` readers. The libc aliases are spelled as plain types and
// `printf` is dropped (the fixture has no varargs).
#![allow(
    dead_code,
    unused_mut,
    unused_unsafe,
    unused_assignments,
    unused_variables,
    non_camel_case_types,
    non_snake_case
)]
extern "C" {
    fn malloc(_: u64) -> *mut std::ffi::c_void;
    fn free(_: *mut std::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
    pub height: i32,
}
#[automatically_derived]
impl ::core::marker::Copy for Node {}
#[automatically_derived]
impl ::core::clone::Clone for Node {
    #[inline]
    fn clone(&self) -> Node {
        *self
    }
}
pub unsafe extern "C" fn height(mut N: *mut Node) -> i32 {
    if N.is_null() {
        return 0 as i32;
    }
    return (*N).height;
}
pub unsafe extern "C" fn max(mut a: i32, mut b: i32) -> i32 {
    return if a > b { a } else { b };
}
pub unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>() as u64) as *mut Node;
    (*node).key = key;
    (*node).left = 0 as *mut Node;
    (*node).right = 0 as *mut Node;
    (*node).height = 1 as i32;
    return node;
}
pub unsafe extern "C" fn rightRotate(mut y: *mut Node) -> *mut Node {
    let mut x = (*y).left;
    let mut T2 = (*x).right;
    (*y).left = T2;
    (*y).height = max(height((*y).left), height((*y).right)) + 1 as i32;
    (*x).right = y;
    (*x).height = max(height((*x).left), height((*x).right)) + 1 as i32;
    return x;
}
pub unsafe extern "C" fn leftRotate(mut x: *mut Node) -> *mut Node {
    let mut y = (*x).right;
    let mut T2 = (*y).left;
    (*x).right = T2;
    (*x).height = max(height((*x).left), height((*x).right)) + 1 as i32;
    (*y).left = x;
    (*y).height = max(height((*y).left), height((*y).right)) + 1 as i32;
    return y;
}
pub unsafe extern "C" fn getBalance(mut N: *mut Node) -> i32 {
    if N.is_null() {
        return 0 as i32;
    }
    return height((*N).left) - height((*N).right);
}
pub unsafe extern "C" fn insert(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() {
        return newNode(key);
    }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else if key > (*node).key {
        (*node).right = insert((*node).right, key);
    } else {
        return node;
    }
    (*node).height = 1 as i32 + max(height((*node).left), height((*node).right));
    let mut balance = getBalance(node);
    if balance > 1 as i32 && key < (*(*node).left).key {
        return rightRotate(node);
    }
    if balance < -(1 as i32) && key > (*(*node).right).key {
        return leftRotate(node);
    }
    if balance > 1 as i32 && key > (*(*node).left).key {
        (*node).left = leftRotate((*node).left);
        return rightRotate(node);
    }
    if balance < -(1 as i32) && key < (*(*node).right).key {
        (*node).right = rightRotate((*node).right);
        return leftRotate(node);
    }
    return node;
}
pub unsafe extern "C" fn minValueNode(mut node: *mut Node) -> *mut Node {
    while !((*node).left).is_null() {
        node = (*node).left;
    }
    return node;
}
pub unsafe extern "C" fn preOrder(mut root: *mut Node) {
    if !root.is_null() {
        preOrder((*root).left);
        preOrder((*root).right);
    }
}
