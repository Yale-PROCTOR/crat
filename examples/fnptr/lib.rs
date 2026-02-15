#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]

unsafe extern "C" fn apply(
    mut f: Option<unsafe extern "C" fn(i32) -> i32>,
    mut x: i32,
) -> i32 {
    return f.expect("non-null function pointer")(x);
}

pub unsafe extern "C" fn double_val(mut x: i32) -> i32 {
    return x * 2i32;
}

fn main() {
    unsafe {
        apply(
            Some(double_val as unsafe extern "C" fn(i32) -> i32),
            21i32,
        );
    }
}
