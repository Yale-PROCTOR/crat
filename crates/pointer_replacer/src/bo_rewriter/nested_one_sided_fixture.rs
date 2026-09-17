// R436/N1 fixtures — the corpus shape the pair rule cannot reach. Both bodies
// are `indicators::ema::ti_ema` from rs-crown-derived (its assert dropped): a
// lookback indicator whose body is NOT the elementwise pattern, so the pair
// rule holds it at `IntervalChanged` even though both tables are delivered
// flat slices with an inner Ref level.
//
//   ti_ema           — both tables' row loads lead the block, so BOTH deliver
//                      in one plan (R445-3 dropped the lane boundary).
//   ti_ema_late_out  — the output table's row load sits AFTER an early return,
//                      so it is not a leading load: only the input table
//                      delivers and the output table keeps its frame form.
//   ti_ema_late_in   — the mirror image: the mutable output table delivers.
//   ti_ema_extra_use — the output table is read a second time after the loop,
//                      so not every use of it is an admitted row load.
pub mod indicators {
    pub mod ema {
        // Safety: callers supply one initialized, readable pointer-table cell
        // per table. For positive size the inner input pointer covers size live
        // doubles and the output row is writable for size doubles.
        pub unsafe extern "C" fn ti_ema(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut input: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as std::os::raw::c_int;
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            if period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int;
            }
            let per: std::os::raw::c_double = 2 as std::os::raw::c_int as std::os::raw::c_double
                / (period as std::os::raw::c_double
                    + 1 as std::os::raw::c_int as std::os::raw::c_double);
            let mut val: std::os::raw::c_double = *input.offset(0 as std::os::raw::c_int as isize);
            *output.offset(0 as std::os::raw::c_int as isize) = val;
            let mut i: std::os::raw::c_int = 0;
            i = 1 as std::os::raw::c_int;
            while i < size {
                val = (*input.offset(i as isize) - val) * per + val;
                *output.offset(i as isize) = val;
                i += 1
            }
            return 0 as std::os::raw::c_int;
        }
    }
    pub mod ema_late_out {
        // Safety: as above. The output table cell is read only after the
        // period guard, so its load is not one of the block's leading loads.
        pub unsafe extern "C" fn ti_ema_late_out(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut input: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as std::os::raw::c_int;
            if period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int;
            }
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let per: std::os::raw::c_double = 2 as std::os::raw::c_int as std::os::raw::c_double
                / (period as std::os::raw::c_double
                    + 1 as std::os::raw::c_int as std::os::raw::c_double);
            let mut val: std::os::raw::c_double = *input.offset(0 as std::os::raw::c_int as isize);
            *output.offset(0 as std::os::raw::c_int as isize) = val;
            let mut i: std::os::raw::c_int = 0;
            i = 1 as std::os::raw::c_int;
            while i < size {
                val = (*input.offset(i as isize) - val) * per + val;
                *output.offset(i as isize) = val;
                i += 1
            }
            return 0 as std::os::raw::c_int;
        }
    }
    pub mod ema_late_in {
        // Safety: as above. Here it is the INPUT table cell that is read only
        // after the period guard, so the MUTABLE output table is the one this
        // arm delivers.
        pub unsafe extern "C" fn ti_ema_late_in(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as std::os::raw::c_int;
            if period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int;
            }
            let mut input: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let per: std::os::raw::c_double = 2 as std::os::raw::c_int as std::os::raw::c_double
                / (period as std::os::raw::c_double
                    + 1 as std::os::raw::c_int as std::os::raw::c_double);
            let mut val: std::os::raw::c_double = *input.offset(0 as std::os::raw::c_int as isize);
            *output.offset(0 as std::os::raw::c_int as isize) = val;
            let mut i: std::os::raw::c_int = 0;
            i = 1 as std::os::raw::c_int;
            while i < size {
                val = (*input.offset(i as isize) - val) * per + val;
                *output.offset(i as isize) = val;
                i += 1
            }
            return 0 as std::os::raw::c_int;
        }
    }
    pub mod ema_extra_use {
        // Safety: as above. The output table is read a SECOND time after the
        // loop, so not every use of it is an admitted row load.
        pub unsafe extern "C" fn ti_ema_extra_use(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut input: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as std::os::raw::c_int;
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            if period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int;
            }
            let mut val: std::os::raw::c_double = *input.offset(0 as std::os::raw::c_int as isize);
            let mut i: std::os::raw::c_int = 0;
            i = 0 as std::os::raw::c_int;
            while i < size {
                val = *input.offset(i as isize) + val;
                *output.offset(i as isize) = val;
                i += 1
            }
            let last: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            *last.offset(0 as std::os::raw::c_int as isize) = val;
            return 0 as std::os::raw::c_int;
        }
    }
}
pub struct IndicatorInfo {
    pub indicator: Option<
        unsafe extern "C" fn(
            std::os::raw::c_int,
            *const *const std::os::raw::c_double,
            *const std::os::raw::c_double,
            *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int,
    >,
}
pub static INDICATORS: [IndicatorInfo; 4] = [
    IndicatorInfo {
        indicator: Some(
            indicators::ema::ti_ema
                as unsafe extern "C" fn(
                    std::os::raw::c_int,
                    *const *const std::os::raw::c_double,
                    *const std::os::raw::c_double,
                    *const *mut std::os::raw::c_double,
                ) -> std::os::raw::c_int,
        ),
    },
    IndicatorInfo {
        indicator: Some(
            indicators::ema_late_out::ti_ema_late_out
                as unsafe extern "C" fn(
                    std::os::raw::c_int,
                    *const *const std::os::raw::c_double,
                    *const std::os::raw::c_double,
                    *const *mut std::os::raw::c_double,
                ) -> std::os::raw::c_int,
        ),
    },
    IndicatorInfo {
        indicator: Some(
            indicators::ema_late_in::ti_ema_late_in
                as unsafe extern "C" fn(
                    std::os::raw::c_int,
                    *const *const std::os::raw::c_double,
                    *const std::os::raw::c_double,
                    *const *mut std::os::raw::c_double,
                ) -> std::os::raw::c_int,
        ),
    },
    IndicatorInfo {
        indicator: Some(
            indicators::ema_extra_use::ti_ema_extra_use
                as unsafe extern "C" fn(
                    std::os::raw::c_int,
                    *const *const std::os::raw::c_double,
                    *const std::os::raw::c_double,
                    *const *mut std::os::raw::c_double,
                ) -> std::os::raw::c_int,
        ),
    },
];
