#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
// wave-5d report 137 §5: binn's `copy_be32(p, &mut id as ..)` with
// `p` loaded from the item's buffer. Under R838 the classifier's proof is not
// taken; A5's fallback learns `psource` as the raw view, rendered from the
// operand peeled of its casts: the program's cast to `*mut u32` is put back.
// `int32`'s address is stored in the item first, so the narrowing (a loaded
// pointer beside a local whose address never reaches memory) does not apply.
pub struct Item {
    pub pbuf: *mut u8,
    pub used: i32,
    pub last: *mut i32,
}
unsafe fn copy_be32(mut pdest: *mut u32, mut psource: *mut u32) {
    let mut source = psource as *mut u8;
    let mut dest = pdest as *mut u8;
    *dest.offset(0) = *source.offset(3);
    *dest.offset(1) = *source.offset(2);
    *dest.offset(2) = *source.offset(1);
    *dest.offset(3) = *source.offset(0);
}
pub unsafe fn save(mut item: *mut Item, mut v: i32) {
    let mut int32: i32 = v;
    (*item).last = &mut int32;
    let mut p = (*item).pbuf.offset((*item).used as isize);
    copy_be32(p as *mut u32, &mut int32 as *mut i32 as *mut u32);
    (*item).used += 4;
}
