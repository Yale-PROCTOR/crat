// w6f-owned-array-frame
// lodepng's `filter` reduction as the derived substrate spells it
// (`benchmarks/rs-crown-derived/lodepng/lib.rs`, the `attempt` arrays): each
// element is its OWN allocation (one `lodepng_malloc` per element, inside the
// loop), the elements are read through a callee and by offset, and each is
// released at its own `lodepng_free` — six corpus arrays have this shape.
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
    fn malloc(size: u64) -> *mut std::ffi::c_void;
    fn free(ptr: *mut std::ffi::c_void);
}
// lodepng's own wrappers, as the substrate has them: the allocator and the
// DEALLOCATOR are local functions over libc's.
pub unsafe extern "C" fn lodepng_malloc(mut size: u64) -> *mut std::ffi::c_void {
    return malloc(size);
}
pub unsafe extern "C" fn lodepng_free(mut ptr: *mut std::ffi::c_void) {
    free(ptr);
}
pub unsafe extern "C" fn filterScanline(mut out: *mut u8, mut scanline: *const u8, mut len: u64) {
    let mut i = 0 as u64;
    while i < len {
        *out.offset(i as isize) = *scanline.offset(i as isize);
        i = i.wrapping_add(1);
    }
}
pub unsafe extern "C" fn filter(mut in_0: *const u8, mut linebytes: u64) -> u32 {
    let mut attempt: [*mut u8; 5] = [0 as *mut u8; 5];
    let mut error = 0 as u32;
    let mut type_1: u8 = 0;
    type_1 = 0 as u8;
    while type_1 as i32 != 5 as i32 {
        attempt[type_1 as usize] = lodepng_malloc(linebytes) as *mut u8;
        if (attempt[type_1 as usize]).is_null() {
            error = 83 as u32;
        }
        type_1 = type_1.wrapping_add(1);
    }
    if error == 0 {
        type_1 = 0 as u8;
        while type_1 as i32 != 5 as i32 {
            filterScanline(attempt[type_1 as usize], in_0, linebytes);
            let mut s = *(attempt[type_1 as usize]).offset(0 as isize);
            error = error.wrapping_add(s as u32);
            type_1 = type_1.wrapping_add(1);
        }
    }
    type_1 = 0 as u8;
    while type_1 as i32 != 5 as i32 {
        lodepng_free(attempt[type_1 as usize] as *mut std::ffi::c_void);
        type_1 = type_1.wrapping_add(1);
    }
    return error;
}

// The BORROWED-element control: the elements are views of a caller's rows,
// written through but never allocated or released — the family whose `&mut`
// elements would need a disjointness argument (parked, R395-2).
pub unsafe extern "C" fn borrowed_rows(mut row_a: *mut u8, mut row_b: *mut u8) -> u32 {
    let mut rows: [*mut u8; 2] = [0 as *mut u8; 2];
    rows[0 as usize] = row_a;
    rows[1 as usize] = row_b;
    let mut i = 0 as usize;
    let mut sum = 0 as u32;
    while i < 2 as usize {
        *(rows[i]).offset(0 as isize) = 1 as u8;
        sum = sum.wrapping_add(*(rows[i]).offset(0 as isize) as u32);
        i = i.wrapping_add(1);
    }
    return sum;
}

// Allocated per element and never released: the owned family's evidence is
// incomplete — the C free sites are what the drops are placed at, so without
// them there is nothing to place (leak parity is not claimed, addendum 101,
// but a drop may not be invented at a site C does not have).
pub unsafe extern "C" fn leaked(mut len: u64) -> u32 {
    let mut scratch: [*mut u8; 2] = [0 as *mut u8; 2];
    let mut i = 0 as usize;
    while i < 2 as usize {
        scratch[i] = lodepng_malloc(len) as *mut u8;
        i = i.wrapping_add(1);
    }
    return *(scratch[0 as usize]).offset(0 as isize) as u32;
}

// The release is not a deallocator: C would keep a pointer the Box still
// owns, so the transaction holds rather than hand out a view.
pub unsafe extern "C" fn record(mut ptr: *mut std::ffi::c_void) {}
pub unsafe extern "C" fn registered(mut len: u64) -> u32 {
    let mut kept: [*mut u8; 2] = [0 as *mut u8; 2];
    let mut i = 0 as usize;
    while i < 2 as usize {
        kept[i] = lodepng_malloc(len) as *mut u8;
        record(kept[i] as *mut std::ffi::c_void);
        i = i.wrapping_add(1);
    }
    return *(kept[0 as usize]).offset(0 as isize) as u32;
}

// An owned-element array handed on WHOLE: the element is a boxed slice (two
// words), so the NPO layout the whole-array view rests on does not hold —
// the transaction says so instead of skipping the use.
pub unsafe extern "C" fn take_all(mut ptrs: *const *mut u8, mut len: u64) -> u32 {
    return (*ptrs.offset(0 as isize)).is_null() as u32;
}
pub unsafe extern "C" fn whole(mut len: u64) -> u32 {
    let mut bufs: [*mut u8; 2] = [0 as *mut u8; 2];
    let mut i = 0 as usize;
    while i < 2 as usize {
        bufs[i] = lodepng_malloc(len) as *mut u8;
        i = i.wrapping_add(1);
    }
    let mut r = take_all(bufs.as_ptr(), len);
    i = 0 as usize;
    while i < 2 as usize {
        lodepng_free(bufs[i] as *mut std::ffi::c_void);
        i = i.wrapping_add(1);
    }
    return r;
}
