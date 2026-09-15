#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
pub struct lil_env {
    pub name: *const i8,
    pub depth: i32,
}
#[automatically_derived]
impl ::core::marker::Copy for lil_env { }
#[automatically_derived]
impl ::core::clone::Clone for lil_env {
    #[inline]
    fn clone(&self) -> lil_env {
        let _: ::core::clone::AssertParamIsClone<*const i8>;
        let _: ::core::clone::AssertParamIsClone<i32>;
        *self
    }
}
#[no_mangle]
pub unsafe extern "C" fn env_set_name(mut env: *mut lil_env, mut name: *const i8) {
    (*env).name = name;
    (*env).depth = 0;
}
#[no_mangle]
pub unsafe extern "C" fn env_first_char(mut env: *mut lil_env) -> i8 {
    if ((*env).name).is_null() {
        return 0 as i8;
    }
    return *(*env).name;
}
