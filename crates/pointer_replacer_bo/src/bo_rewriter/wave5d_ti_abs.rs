// Original ti_abs body from rs-crown-derived, inside its original module path.
// The pointer-table registration preserves the original raw C signature.
pub mod indicators {
    pub mod abs {
        #[link(name = "m")]
        unsafe extern "C" {
            fn fabs(value: std::os::raw::c_double) -> std::os::raw::c_double;
        }
        // Safety: callers supply one initialized, readable pointer-table cell
        // per table. For positive size, the inner pointers cover size live
        // doubles and the output is writable; raw input/output may overlap.
        pub unsafe extern "C" fn ti_abs(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut in1: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let mut i: std::os::raw::c_int = 0;
            i = 0 as std::os::raw::c_int;
            while i < size {
                *output.offset(i as isize) = fabs(*in1.offset(i as isize));
                i += 1
            }
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
pub static INDICATOR: IndicatorInfo = IndicatorInfo {
    indicator: Some(
        indicators::abs::ti_abs
            as unsafe extern "C" fn(
                std::os::raw::c_int,
                *const *const std::os::raw::c_double,
                *const std::os::raw::c_double,
                *const *mut std::os::raw::c_double,
            ) -> std::os::raw::c_int,
    ),
};
