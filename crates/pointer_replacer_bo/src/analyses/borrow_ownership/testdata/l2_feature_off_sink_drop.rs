unsafe extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}

pub unsafe fn delete_node(mut root: *mut node, key: i32) -> *mut node {
    if root.is_null() {
        return root;
    }
    if key < unsafe { (*root).key } {
        unsafe { (*root).left = delete_node((*root).left, key) };
    } else if key > unsafe { (*root).key } {
        unsafe { (*root).right = delete_node((*root).right, key) };
    } else if unsafe { (*root).left.is_null() } {
        let temp: *mut node = unsafe { (*root).right };
        unsafe { free(root as *mut core::ffi::c_void) };
        return temp;
    } else if unsafe { (*root).right.is_null() } {
        let temp: *mut node = unsafe { (*root).left };
        unsafe { free(root as *mut core::ffi::c_void) };
        return temp;
    } else {
        let temp: *mut node = unsafe { (*root).right };
        unsafe {
            (*root).key = (*temp).key;
            (*root).right = delete_node((*root).right, (*temp).key);
        }
    }
    root
}
