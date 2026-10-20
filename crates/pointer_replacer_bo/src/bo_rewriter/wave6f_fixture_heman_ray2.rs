// heman's `kazmath/ray2.rs` reduction as the derived substrate spells it
// (`benchmarks/rs-crown-derived/heman/lib.rs`, `kmRay2IntersectBox` and the
// callees its loads reach). The array-of-pointers local, its four stores,
// the three element loads (`points[i]`, the `if`-arm pair) and both use
// shapes — a local callee taking `*const kmVec2`, and a by-value deref —
// are the corpus text; the libc aliases are spelled as plain types.
#![allow(
    dead_code,
    unused_mut,
    unused_unsafe,
    unused_assignments,
    unused_variables,
    non_camel_case_types,
    non_snake_case
)]
#[repr(C, packed)]
pub struct kmVec2 {
    pub x: f32,
    pub y: f32,
}
#[automatically_derived]
impl ::core::marker::Copy for kmVec2 {}
#[automatically_derived]
impl ::core::clone::Clone for kmVec2 {
    fn clone(&self) -> kmVec2 {
        *self
    }
}
#[repr(C)]
pub struct kmRay2 {
    pub start: kmVec2,
    pub dir: kmVec2,
}
#[automatically_derived]
impl ::core::marker::Copy for kmRay2 {}
#[automatically_derived]
impl ::core::clone::Clone for kmRay2 {
    fn clone(&self) -> kmRay2 {
        *self
    }
}
pub unsafe extern "C" fn kmVec2Dot(mut pV1: *const kmVec2, mut pV2: *const kmVec2) -> f32 {
    return (*pV1).x * (*pV2).x + (*pV1).y * (*pV2).y;
}
pub unsafe extern "C" fn kmVec2Length(mut pIn: *const kmVec2) -> f32 {
    return ((*pIn).x * (*pIn).x + (*pIn).y * (*pIn).y) as f64 as f32;
}
pub unsafe extern "C" fn kmVec2Subtract(
    mut pOut: *mut kmVec2,
    mut pV1: *const kmVec2,
    mut pV2: *const kmVec2,
) -> *mut kmVec2 {
    (*pOut).x = (*pV1).x - (*pV2).x;
    (*pOut).y = (*pV1).y - (*pV2).y;
    return pOut;
}
pub unsafe extern "C" fn kmVec2Assign(
    mut pOut: *mut kmVec2,
    mut pIn: *const kmVec2,
) -> *mut kmVec2 {
    (*pOut).x = (*pIn).x;
    (*pOut).y = (*pIn).y;
    return pOut;
}
pub unsafe extern "C" fn calculate_line_normal(
    mut p1: kmVec2,
    mut p2: kmVec2,
    mut other_point: kmVec2,
    mut normal_out: *mut kmVec2,
) {
    let mut edge = kmVec2 {
        x: p2.x - p1.x,
        y: p2.y - p1.y,
    };
    (*normal_out).x = -edge.y;
    (*normal_out).y = edge.x;
    let mut other = kmVec2 {
        x: other_point.x - p1.x,
        y: other_point.y - p1.y,
    };
    if kmVec2Dot(normal_out, &mut other) > 0 as i32 as f32 {
        (*normal_out).x = -(*normal_out).x;
        (*normal_out).y = -(*normal_out).y;
    }
}
pub unsafe extern "C" fn kmRay2IntersectLineSegment(
    mut ray: *const kmRay2,
    mut p1: *const kmVec2,
    mut p2: *const kmVec2,
    mut intersection: *mut kmVec2,
) -> u8 {
    let mut ua: f32 = (*p2).x - (*p1).x;
    let mut ub: f32 = (*p2).y - (*p1).y;
    if ua == 0 as i32 as f32 && ub == 0 as i32 as f32 {
        return 0 as i32 as u8;
    }
    (*intersection).x = (*p1).x + ua * (*ray).dir.x;
    (*intersection).y = (*p1).y + ub * (*ray).dir.y;
    return 1 as i32 as u8;
}
pub unsafe extern "C" fn kmRay2IntersectBox(
    mut ray: *const kmRay2,
    mut p1: *const kmVec2,
    mut p2: *const kmVec2,
    mut p3: *const kmVec2,
    mut p4: *const kmVec2,
    mut intersection: *mut kmVec2,
    mut normal_out: *mut kmVec2,
) -> u8 {
    let mut intersected = 0 as i32 as u8;
    let mut intersect = kmVec2 { x: 0., y: 0. };
    let mut final_intersect = kmVec2 { x: 0., y: 0. };
    let mut normal = kmVec2 { x: 0., y: 0. };
    let mut distance = 10000.0f32;
    let mut points: [*const kmVec2; 4] = [0 as *const kmVec2; 4];
    points[0 as i32 as usize] = p1;
    points[1 as i32 as usize] = p2;
    points[2 as i32 as usize] = p3;
    points[3 as i32 as usize] = p4;
    let mut i = 0 as i32 as u32;
    while i < 4 as i32 as u32 {
        let mut this_point = points[i as usize];
        let mut next_point = if i == 3 as i32 as u32 {
            points[0 as i32 as usize]
        } else {
            points[i.wrapping_add(1 as i32 as u32) as usize]
        };
        let mut other_point = if i == 3 as i32 as u32 || i == 0 as i32 as u32 {
            points[1 as i32 as usize]
        } else {
            points[0 as i32 as usize]
        };
        if kmRay2IntersectLineSegment(ray, this_point, next_point, &mut intersect) != 0 {
            let mut tmp = kmVec2 { x: 0., y: 0. };
            let mut this_distance =
                kmVec2Length(kmVec2Subtract(&mut tmp, &mut intersect, &(*ray).start));
            let mut this_normal = kmVec2 { x: 0., y: 0. };
            calculate_line_normal(*this_point, *next_point, *other_point, &mut this_normal);
            if this_distance < distance && kmVec2Dot(&mut this_normal, &(*ray).dir) < 0.0f32 {
                kmVec2Assign(&mut final_intersect, &mut intersect);
                distance = this_distance;
                intersected = 1 as i32 as u8;
                kmVec2Assign(&mut normal, &mut this_normal);
            }
        }
        i = i.wrapping_add(1);
    }
    if intersected != 0 {
        (*intersection).x = final_intersect.x;
        (*intersection).y = final_intersect.y;
        if !normal_out.is_null() {
            (*normal_out).x = normal.x;
            (*normal_out).y = normal.y;
        }
    }
    return intersected;
}
