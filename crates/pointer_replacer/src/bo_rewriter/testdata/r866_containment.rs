#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
// R866-1 (fan-out 083): brotli's ProcessCommandsInternal takes
// `br = &mut (*s).br` and calls SafeReadDistance(&mut *s, &mut *br): `br`
// lies inside `s`'s referent, so the two `&mut` formals overlap by
// construction; both are held raw.
pub struct BitReader {
    pub val: u64,
    pub pos: u32,
}
pub struct State {
    pub state: i32,
    pub br: BitReader,
}
unsafe fn safe_read(mut s: *mut State, mut br: *mut BitReader) -> i32 {
    (*br).pos += 1;
    (*s).state += 1;
    (*s).state
}
pub unsafe fn process(mut s: *mut State) -> i32 {
    let mut br: *mut BitReader = &mut (*s).br;
    safe_read(&mut *s, &mut *br)
}
// The direct spelling: the field's address beside the object's reborrow.
unsafe fn safe_read2(mut s: *mut State, mut br: *mut BitReader) -> i32 {
    (*br).pos += 1;
    (*s).state += 1;
    (*s).state
}
pub unsafe fn direct(mut s: *mut State) -> i32 {
    safe_read2(&mut *s, &mut (*s).br)
}
// Control: two distinct locals' addresses stay delivered.
unsafe fn safe_read3(mut s: *mut State, mut br: *mut BitReader) -> i32 {
    (*br).pos += 1;
    (*s).state += 1;
    (*s).state
}
pub unsafe fn control() -> i32 {
    let mut s = State { state: 0, br: BitReader { val: 0, pos: 0 } };
    let mut b = BitReader { val: 0, pos: 0 };
    safe_read3(&mut s, &mut b)
}
// The substrate's own spelling (brotli lib.rs: `SafeReadDistance(s, br)`):
// both arguments bare, `br`'s one definition the field's address.
unsafe fn safe_read4(mut s: *mut State, mut br: *mut BitReader) -> i32 {
    (*br).pos += 1;
    (*s).state += 1;
    (*s).state
}
pub unsafe fn process_bare(mut s: *mut State) -> i32 {
    let mut br: *mut BitReader = &mut (*s).br;
    safe_read4(s, br)
}
// The callers that make `s` a reference, as brotli's decoder state is (the
// record delivers both formals `&mut`).
pub unsafe fn top() -> i32 {
    let mut st = State { state: 0, br: BitReader { val: 0, pos: 0 } };
    process(&mut st) + direct(&mut st) + process_bare(&mut st)
}
