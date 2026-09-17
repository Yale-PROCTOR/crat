#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_float = f32; pub type c_double = f64; pub type c_int = i32; pub type c_void = core::ffi::c_void; }
unsafe extern "C" { fn sqrt(x: libc::c_double) -> libc::c_double; }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmMat3 { pub mat: [libc::c_float; 9], }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmQuaternion { pub x: libc::c_float, pub y: libc::c_float, pub z: libc::c_float, pub w: libc::c_float, }
            pub unsafe extern "C" fn kmQuaternionRotationMatrix(mut pOut:
                    *mut kmQuaternion, mut pIn: *const kmMat3)
                -> *mut kmQuaternion {
                let mut x: libc::c_float = 0.;
                let mut y: libc::c_float = 0.;
                let mut z: libc::c_float = 0.;
                let mut w: libc::c_float = 0.;
                let mut pMatrix = 0 as *mut libc::c_float;
                let mut m4x4: [libc::c_float; 16] =
                    [0 as libc::c_int as libc::c_float, 0., 0., 0., 0., 0., 0.,
                            0., 0., 0., 0., 0., 0., 0., 0., 0.];
                let mut scale = 0.0f32;
                let mut diagonal = 0.0f32;
                if pIn.is_null() { return 0 as *mut kmQuaternion; }
                m4x4[0 as libc::c_int as usize] =
                    (*pIn).mat[0 as libc::c_int as usize];
                m4x4[5 as libc::c_int as usize] =
                    (*pIn).mat[4 as libc::c_int as usize];
                m4x4[10 as libc::c_int as usize] =
                    (*pIn).mat[8 as libc::c_int as usize];
                m4x4[15 as libc::c_int as usize] =
                    1 as libc::c_int as libc::c_float;
                pMatrix =
                    &mut *m4x4.as_mut_ptr().offset(0 as libc::c_int as isize) as
                        *mut libc::c_float;
                diagonal =
                    *pMatrix.offset(0 as libc::c_int as isize) +
                                *pMatrix.offset(5 as libc::c_int as isize) +
                            *pMatrix.offset(10 as libc::c_int as isize) +
                        1 as libc::c_int as libc::c_float;
                if diagonal as libc::c_double > 0.0001f64 {
                    scale =
                        sqrt(diagonal as libc::c_double) as libc::c_float *
                            2 as libc::c_int as libc::c_float;
                    x =
                        (*pMatrix.offset(9 as libc::c_int as isize) -
                                    *pMatrix.offset(6 as libc::c_int as isize)) / scale;
                    y =
                        (*pMatrix.offset(2 as libc::c_int as isize) -
                                    *pMatrix.offset(8 as libc::c_int as isize)) / scale;
                    z =
                        (*pMatrix.offset(4 as libc::c_int as isize) -
                                    *pMatrix.offset(1 as libc::c_int as isize)) / scale;
                    w = 0.25f32 * scale;
                } else {
                    scale =
                        sqrt((1.0f32 + *pMatrix.offset(0 as libc::c_int as isize) -
                                                    *pMatrix.offset(5 as libc::c_int as isize) -
                                                *pMatrix.offset(10 as libc::c_int as isize)) as
                                        libc::c_double) as libc::c_float * 2.0f32;
                    x = 0.25f32 * scale;
                    y =
                        (*pMatrix.offset(4 as libc::c_int as isize) +
                                    *pMatrix.offset(1 as libc::c_int as isize)) / scale;
                    z =
                        (*pMatrix.offset(2 as libc::c_int as isize) +
                                    *pMatrix.offset(8 as libc::c_int as isize)) / scale;
                    w =
                        (*pMatrix.offset(9 as libc::c_int as isize) -
                                    *pMatrix.offset(6 as libc::c_int as isize)) / scale;
                }
                (*pOut).x = x;
                (*pOut).y = y;
                (*pOut).z = z;
                (*pOut).w = w;
                return pOut;
            }
