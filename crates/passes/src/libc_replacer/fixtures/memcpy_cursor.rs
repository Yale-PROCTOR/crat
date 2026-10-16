fn check(condition: bool) {
    if !condition {
        std::process::exit(23);
    }
}

unsafe fn copy(dst: &mut [u8; 6], src: SliceCursor<'_, u8>, offset: isize, count: usize, raw: *const u8) {
    let _value = *raw;
    memcpy(dst.as_mut_ptr().offset(offset) as *mut _, src.as_ptr() as *const _, count);
}

fn main() {
    let data = [10u8, 20, 30, 40, 50];
    let src = SliceCursor { base: &data, pos: 1 };
    let original = src.as_ptr();
    let mut dst = [99u8; 6];
    unsafe { copy(&mut dst, src, 2, 3, data.as_ptr()); }
    check(dst == [99, 99, 20, 30, 40, 99]);
    check(src.pos == 1 && src.as_ptr() == original);

    dst = [99; 6];
    unsafe { copy(&mut dst, src, 3, 3, data.as_ptr()); }
    check(dst == [99, 99, 99, 20, 30, 40]);
    let empty = SliceCursor { base: &data, pos: data.len() };
    unsafe { copy(&mut dst, empty, 6, 0, data.as_ptr()); }
    check(dst == [99, 99, 99, 20, 30, 40]);
    check(empty.pos == data.len());

    let mut source = [10u8, 20, 30, 40, 50];
    let mut source_cursor = SliceCursorMut { base: &mut source, pos: 1 };
    dst = [99; 6];
    {
        let mut destination_cursor = SliceCursorMut { base: &mut dst, pos: 2 };
        unsafe {
            memcpy(destination_cursor.as_mut_ptr() as *mut _, source_cursor.as_deref_mut().offset_by(1).as_ptr() as *const _, 2);
        }
        check(destination_cursor.pos == 2);
        destination_cursor.as_slice_mut()[2] = 77;
    }
    check(dst == [99, 99, 30, 40, 77, 99]);
    check(source_cursor.pos == 1);
    source_cursor.as_slice_mut()[0] = 88;
    check(source_cursor.as_slice()[0] == 88);
}
