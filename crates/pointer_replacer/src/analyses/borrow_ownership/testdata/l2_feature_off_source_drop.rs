unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
