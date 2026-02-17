use super::run_ownership_case;

const SOURCE: &str = r####"
#![warn(mutable_transmutes)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(c_variadic)]
#![feature(extern_types)]
#![feature(linkage)]
#![feature(rustc_private)]
#![feature(thread_local)]
#![feature(builtin_syntax)]
#![feature(core_intrinsics)]
#![feature(derive_clone_copy)]
#![feature(hint_must_use)]
#![feature(panic_internals)]
pub mod src {
    pub mod lib {
        pub type btac1c_u16 = core::ffi::c_ushort;
        pub type btac1c_s16 = core::ffi::c_short;
        pub type btac1c_byte = core::ffi::c_uchar;
        #[repr(C)]
        pub struct btac1c_idxstate_s {
            pub idx: btac1c_u16,
            pub lpred: btac1c_s16,
            pub rpred: btac1c_s16,
            pub tag: btac1c_byte,
            pub bcfcn: btac1c_byte,
            pub bsfcn: btac1c_byte,
            pub usefx: btac1c_byte,
            pub firfx: [[btac1c_s16; 8]; 4],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for btac1c_idxstate_s {}
        #[automatically_derived]
        impl ::core::clone::Clone for btac1c_idxstate_s {
            #[inline]
            fn clone(&self) -> btac1c_idxstate_s {
                let _: ::core::clone::AssertParamIsClone<btac1c_u16>;
                let _: ::core::clone::AssertParamIsClone<btac1c_s16>;
                let _: ::core::clone::AssertParamIsClone<btac1c_byte>;
                let _: ::core::clone::AssertParamIsClone<[[btac1c_s16; 8]; 4]>;
                *self
            }
        }
        pub type btac1c_idxstate = btac1c_idxstate_s;
        unsafe extern "C" fn BTAC1C2_PredictSample(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            let mut pred: core::ffi::c_int = 0;
            let mut p0: core::ffi::c_int = 0;
            let mut p1: core::ffi::c_int = 0;
            let mut i: core::ffi::c_int = 0;
            i = idx;
            match pfcn {
                0 => {
                    pred = *psamp
                        .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                }
                1 => {
                    pred = 2 as core::ffi::c_int
                        * *psamp
                            .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        - *psamp
                            .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                }
                2 => {
                    pred = (3 as core::ffi::c_int
                        * *psamp.offset(
                            ((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        )
                        - *psamp.offset(
                            ((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        ))
                        >> 1 as core::ffi::c_int;
                }
                3 => {
                    pred = (5 as core::ffi::c_int
                        * *psamp.offset(
                            ((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        )
                        - *psamp.offset(
                            ((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        ))
                        >> 2 as core::ffi::c_int;
                }
                4 => {
                    p0 = *psamp
                        .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    p1 = *psamp
                        .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    pred = p0 - (p1 >> 1 as core::ffi::c_int);
                }
                5 => {
                    p0 = *psamp
                        .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    p1 = *psamp
                        .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    pred = (3 as core::ffi::c_int * p0 - p1) >> 2 as core::ffi::c_int;
                }
                6 => {
                    p0 = *psamp
                        .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    p1 = *psamp
                        .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    pred = (5 as core::ffi::c_int * p0 - p1) >> 3 as core::ffi::c_int;
                }
                7 => {
                    pred = (18 as core::ffi::c_int
                        * *psamp.offset(
                            ((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        )
                        - 4 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 3 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 2 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 1 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            ))
                        / 16 as core::ffi::c_int;
                }
                8 => {
                    pred = (72 as core::ffi::c_int
                        * *psamp.offset(
                            ((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        )
                        - 16 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 12 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 8 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 5 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 3 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 3 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 1 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            ))
                        / 64 as core::ffi::c_int;
                }
                9 => {
                    pred = (76 as core::ffi::c_int
                        * *psamp.offset(
                            ((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        )
                        - 17 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 10 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 7 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 5 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 4 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + 4 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        - 3 as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            ))
                        / 64 as core::ffi::c_int;
                }
                10 => {
                    p0 = *psamp
                        .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    p1 = *psamp
                        .offset(((i - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    pred = (5 as core::ffi::c_int * p0 - p1) >> 4 as core::ffi::c_int;
                }
                11 => {
                    p0 = *psamp
                        .offset(((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    p1 = *psamp
                        .offset(((i - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                        + *psamp
                            .offset(((i - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
                    pred = (p0 + p1) >> 3 as core::ffi::c_int;
                }
                12..=15 => {
                    pred = ((*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                        [0 as core::ffi::c_int as usize]
                        as core::ffi::c_int
                        * *psamp.offset(
                            ((i - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                        )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [1 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [2 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [3 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [4 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [5 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [6 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            )
                        + (*ridx).firfx[(pfcn - 12 as core::ffi::c_int) as usize]
                            [7 as core::ffi::c_int as usize]
                            as core::ffi::c_int
                            * *psamp.offset(
                                ((i - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize,
                            ))
                        / 256 as core::ffi::c_int;
                }
                _ => {
                    pred = 0 as core::ffi::c_int;
                }
            }
            pred
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn0(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn1(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            2 as core::ffi::c_int
                * *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn2(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            (3 as core::ffi::c_int
                * *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize))
                >> 1 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn3(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            (5 as core::ffi::c_int
                * *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize))
                >> 2 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn4(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            let mut p0: core::ffi::c_int = 0;
            let mut p1: core::ffi::c_int = 0;
            p0 = *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            p1 = *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            p0 - (p1 >> 1 as core::ffi::c_int)
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn5(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            let mut p0: core::ffi::c_int = 0;
            let mut p1: core::ffi::c_int = 0;
            p0 = *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            p1 = *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            (3 as core::ffi::c_int * p0 - p1) >> 2 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn6(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            let mut p0: core::ffi::c_int = 0;
            let mut p1: core::ffi::c_int = 0;
            p0 = *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            p1 = *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            (5 as core::ffi::c_int * p0 - p1) >> 3 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn7(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            (18 as core::ffi::c_int
                * *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 4 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 3 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 2 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 1 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize))
                / 16 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn8(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            (72 as core::ffi::c_int
                * *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 16 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 12 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 8 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 5 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 3 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 3 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 1 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize))
                / 64 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn9(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            (76 as core::ffi::c_int
                * *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 17 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 10 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 7 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 5 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 4 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + 4 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                - 3 as core::ffi::c_int
                    * *psamp
                        .offset(((idx - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize))
                / 64 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn10(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            let mut p0: core::ffi::c_int = 0;
            let mut p1: core::ffi::c_int = 0;
            p0 = *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            p1 = *psamp.offset(((idx - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            (5 as core::ffi::c_int * p0 - p1) >> 3 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_PredictSample_Pfn11(
            psamp: *mut core::ffi::c_int,
            idx: core::ffi::c_int,
            pfcn: core::ffi::c_int,
            ridx: *mut btac1c_idxstate,
        ) -> core::ffi::c_int {
            let mut p0: core::ffi::c_int = 0;
            let mut p1: core::ffi::c_int = 0;
            p0 = *psamp.offset(((idx - 1 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 2 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 3 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 4 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            p1 = *psamp.offset(((idx - 5 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 6 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 7 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize)
                + *psamp.offset(((idx - 8 as core::ffi::c_int) & 7 as core::ffi::c_int) as isize);
            (p0 + p1) >> 1 as core::ffi::c_int
        }
        unsafe extern "C" fn BTAC1C2_GetPredictFunc(
            pfcn: core::ffi::c_int,
        ) -> *mut core::ffi::c_void {
            let mut fcn: *mut core::ffi::c_void = std::ptr::null_mut::<core::ffi::c_void>();
            match pfcn {
                0 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn0
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                1 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn1
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                2 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn2
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                3 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn3
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                4 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn4
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                5 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn5
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                6 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn6
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                7 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn7
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                8 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn8
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                9 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn9
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                10 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn10
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                11 => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample_Pfn11
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
                _ => {
                    fcn = ::core::mem::transmute::<
                        Option<
                            unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            ) -> core::ffi::c_int,
                        >,
                        *mut core::ffi::c_void,
                    >(Some(
                        BTAC1C2_PredictSample
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_int,
                                core::ffi::c_int,
                                core::ffi::c_int,
                                *mut btac1c_idxstate,
                            )
                                -> core::ffi::c_int,
                    ));
                }
            }
            fcn
        }
        #[no_mangle]
        pub unsafe extern "C" fn call_predict(pfcn: core::ffi::c_int) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let fcn: *mut core::ffi::c_void = BTAC1C2_GetPredictFunc(pfcn);
            match pfcn {
                0 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn0
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                1 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn1
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                2 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn2
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                3 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn3
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                4 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn4
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                5 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn5
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                6 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn6
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                7 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn7
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                8 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn8
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                9 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn9
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                10 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn10
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                11 => {
                    result = (fcn
                        == ::core::mem::transmute::<
                            Option<
                                unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                            >,
                            *mut core::ffi::c_void,
                        >(Some(
                            BTAC1C2_PredictSample_Pfn11
                                as unsafe extern "C" fn(
                                    *mut core::ffi::c_int,
                                    core::ffi::c_int,
                                    core::ffi::c_int,
                                    *mut btac1c_idxstate,
                                )
                                    -> core::ffi::c_int,
                        ))) as core::ffi::c_int;
                }
                _ => {}
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("call_predict_lib", SOURCE);
}
