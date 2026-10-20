// **The N2 seam fixture** (nested's handover packet, 2026-09-17; transplanted
// verbatim under their relay 034 §2 / R453-6). `ti_sma_cursor` is the corpus
// shape where a depth-2 table's row is consumed as a CURSOR: the row is read at
// `i - period`, which the offset-sign analysis reads as possibly negative, so
// this family takes it, while the table itself is nested's N1 market.
//
// The registration entry below is what makes the exposure plan a
// `PositiveSeedShim` — without it the signature is not reached the way the
// corpus reaches it.
pub mod indicators {
    pub mod sma_cursor {
        // Safety: as above. The input row is read at `i - period`, which the
        // offset-sign analysis reads as possibly negative, so the cursor family
        // takes this row: it is the N2 seam's shape.
        pub unsafe extern "C" fn ti_sma_cursor(
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
            let mut sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut i: std::os::raw::c_int = 0;
            i = 0 as std::os::raw::c_int;
            while i < period {
                sum += *input.offset(i as isize);
                i += 1
            }
            *output.offset(0 as std::os::raw::c_int as isize) = sum;
            i = period;
            while i < size {
                sum += *input.offset(i as isize);
                sum -= *input.offset((i - period) as isize);
                *output.offset((i - period + 1 as std::os::raw::c_int) as isize) = sum;
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
pub static INDICATORS: [IndicatorInfo; 1] = [IndicatorInfo {
    indicator: Some(
        indicators::sma_cursor::ti_sma_cursor
            as unsafe extern "C" fn(
                std::os::raw::c_int,
                *const *const std::os::raw::c_double,
                *const std::os::raw::c_double,
                *const *mut std::os::raw::c_double,
            ) -> std::os::raw::c_int,
    ),
}];
