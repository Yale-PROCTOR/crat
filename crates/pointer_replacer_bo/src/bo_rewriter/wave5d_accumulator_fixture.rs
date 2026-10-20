// Original indicator bodies, wrapper registration scaffold only.
// Test callers must supply the pointer-table cells and initialized writable
// arrays covering every original access (including unconditional prefix uses).
pub mod indicators {
    pub mod ad {
        pub unsafe extern "C" fn ti_ad(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut high: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let mut low: *const std::os::raw::c_double =
                *inputs.offset(1 as std::os::raw::c_int as isize);
            let mut close: *const std::os::raw::c_double =
                *inputs.offset(2 as std::os::raw::c_int as isize);
            let mut volume: *const std::os::raw::c_double =
                *inputs.offset(3 as std::os::raw::c_int as isize);
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let mut sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut i: std::os::raw::c_int = 0;
            i = 0 as std::os::raw::c_int;
            while i < size {
                let hl: std::os::raw::c_double = *high.offset(i as isize) - *low.offset(i as isize);
                if hl != 0.0f64 {
                    sum += (*close.offset(i as isize)
                        - *low.offset(i as isize)
                        - *high.offset(i as isize)
                        + *close.offset(i as isize))
                        / hl
                        * *volume.offset(i as isize)
                }
                *output.offset(i as isize) = sum;
                i += 1
            }
            return 0 as std::os::raw::c_int;
        }
    }
    pub mod edecay {
        pub unsafe extern "C" fn ti_edecay(
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
            let scale: std::os::raw::c_double = 1.0f64 - 1.0f64 / period as std::os::raw::c_double;
            *output = *input.offset(0 as std::os::raw::c_int as isize);
            let fresh0 = *output;
            output = output.offset(1);
            let mut i: std::os::raw::c_int = 0;
            i = 1 as std::os::raw::c_int;
            while i < size {
                let mut d: std::os::raw::c_double =
                    *output.offset(-(1 as std::os::raw::c_int) as isize) * scale;
                *output = if *input.offset(i as isize) > d {
                    *input.offset(i as isize)
                } else {
                    d
                };
                let fresh1 = *output;
                output = output.offset(1);
                i += 1
            }
            return 0 as std::os::raw::c_int;
        }
    }
    pub mod obv {
        pub unsafe extern "C" fn ti_obv(
            mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double,
        ) -> std::os::raw::c_int {
            let mut close: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let mut volume: *const std::os::raw::c_double =
                *inputs.offset(1 as std::os::raw::c_int as isize);
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let mut sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            *output = sum;
            let fresh0 = *output;
            output = output.offset(1);
            let mut prev: std::os::raw::c_double = *close.offset(0 as std::os::raw::c_int as isize);
            let mut i: std::os::raw::c_int = 0;
            i = 1 as std::os::raw::c_int;
            while i < size {
                if *close.offset(i as isize) > prev {
                    sum += *volume.offset(i as isize)
                } else if *close.offset(i as isize) < prev {
                    sum -= *volume.offset(i as isize)
                }
                prev = *close.offset(i as isize);
                *output = sum;
                let fresh1 = *output;
                output = output.offset(1);
                i += 1
            }
            return 0 as std::os::raw::c_int;
        }
    }
}
pub type Indicator =
    unsafe extern "C" fn(i32, *const *const f64, *const f64, *const *mut f64) -> i32;
pub static INDICATORS: [Option<Indicator>; 3] = [
    Some(indicators::ad::ti_ad as Indicator),
    Some(indicators::edecay::ti_edecay as Indicator),
    Some(indicators::obv::ti_obv as Indicator),
];
