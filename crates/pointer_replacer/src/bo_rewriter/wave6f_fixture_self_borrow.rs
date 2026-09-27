// w6f-self-borrow-frame
#![allow(dead_code, unused_mut, unused_unsafe, non_camel_case_types, unused_variables, unused_assignments)]
#[repr(C)]
pub struct Params {
    pub quality: i32,
    pub dist: i32,
}
#[repr(C)]
pub struct Hx {
    pub n: i32,
    pub params: *const Params,
}
#[repr(C)]
pub struct Hy {
    pub m: i32,
}
#[repr(C)]
pub union U {
    pub hx: Hx,
    pub hy: Hy,
}
#[repr(C)]
pub struct Hasher {
    pub common: i32,
    pub privat: U,
}
#[repr(C)]
pub struct State {
    pub hasher_: Hasher,
    pub params: Params,
}
impl ::core::marker::Copy for Params {}
impl ::core::clone::Clone for Params {
    fn clone(&self) -> Params {
        *self
    }
}
impl ::core::marker::Copy for Hx {}
impl ::core::clone::Clone for Hx {
    fn clone(&self) -> Hx {
        *self
    }
}
impl ::core::marker::Copy for Hy {}
impl ::core::clone::Clone for Hy {
    fn clone(&self) -> Hy {
        *self
    }
}
impl ::core::marker::Copy for U {}
impl ::core::clone::Clone for U {
    fn clone(&self) -> U {
        *self
    }
}
impl ::core::marker::Copy for Hasher {}
impl ::core::clone::Clone for Hasher {
    fn clone(&self) -> Hasher {
        *self
    }
}
pub unsafe extern "C" fn initialize(mut self_0: *mut Hx, mut params: *const Params) {
    (*self_0).n = 1;
    (*self_0).params = params;
}
pub unsafe extern "C" fn setup(mut hasher: *mut Hasher, mut params: *mut Params) {
    initialize(&mut (*hasher).privat.hx, params);
}
pub unsafe extern "C" fn quality(mut self_0: *const Hx) -> i32 {
    return (*(*self_0).params).quality;
}
pub unsafe extern "C" fn encode(mut s: *mut State) {
    setup(&mut (*s).hasher_, &mut (*s).params);
}
