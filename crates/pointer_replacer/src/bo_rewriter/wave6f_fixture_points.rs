#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
pub struct kmVec2 {
    pub x: f32,
    pub y: f32,
}
unsafe extern "C" fn kmVec2Dot(mut a: *const kmVec2, mut b: *const kmVec2) -> f32 {
    return (*a).x * (*b).x + (*a).y * (*b).y;
}
#[no_mangle]
pub unsafe extern "C" fn kmRay2IntersectBox(
    mut p1: *const kmVec2,
    mut p2: *const kmVec2,
    mut p3: *const kmVec2,
    mut p4: *const kmVec2,
) -> f32 {
    let mut acc = 0.0f32;
    let mut points: [*const kmVec2; 4] = [0 as *const kmVec2; 4];
    points[0 as usize] = p1;
    points[1 as usize] = p2;
    points[2 as usize] = p3;
    points[3 as usize] = p4;
    let mut i = 0 as u32;
    while i < 4 as u32 {
        let mut this_point = points[i as usize];
        let mut next_point = points[(if i == 3 as u32 { 0 as u32 } else { i.wrapping_add(1) }) as usize];
        acc += kmVec2Dot(this_point, next_point) + (*this_point).x;
        i = i.wrapping_add(1);
    }
    return acc;
}
