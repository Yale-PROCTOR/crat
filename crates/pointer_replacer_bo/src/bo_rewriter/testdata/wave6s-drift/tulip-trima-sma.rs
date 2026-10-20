#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
unsafe extern "C" { fn __assert_rtn(_: *const std::os::raw::c_char, _: *const std::os::raw::c_char, _: std::os::raw::c_int, _: *const std::os::raw::c_char) -> !; }
        pub unsafe extern "C" fn ti_sma_start(mut options:
                *const std::os::raw::c_double) -> std::os::raw::c_int {
            return *options.offset(0 as std::os::raw::c_int as isize) as
                        std::os::raw::c_int - 1 as std::os::raw::c_int;
        }
        pub unsafe extern "C" fn ti_sma(mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double)
            -> std::os::raw::c_int {
            let mut input: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as
                    std::os::raw::c_int;
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let scale: std::os::raw::c_double =
                1.0f64 / period as std::os::raw::c_double;
            if period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int
            }
            if size <= ti_sma_start(options) {
                return 0 as std::os::raw::c_int
            }
            let mut sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut i: std::os::raw::c_int = 0;
            i = 0 as std::os::raw::c_int;
            while i < period { sum += *input.offset(i as isize); i += 1 }
            *output = sum * scale;
            let fresh0 = *output;
            output = output.offset(1);
            i = period;
            while i < size {
                sum += *input.offset(i as isize);
                sum -= *input.offset((i - period) as isize);
                *output = sum * scale;
                let fresh1 = *output;
                output = output.offset(1);
                i += 1
            }
            if !(output.offset_from(*outputs.offset(0 as std::os::raw::c_int
                                                            as isize)) as std::os::raw::c_long ==
                                        (size - ti_sma_start(options)) as std::os::raw::c_long) as
                            std::os::raw::c_int as std::os::raw::c_long != 0 {
                __assert_rtn(([b't' as i8, b'i' as i8, b'_' as i8, b's' as i8,
                                    b'm' as i8, b'a' as i8, b'\0' as i8]).as_ptr(),
                    b"indicators/sma.c\x00" as *const u8 as
                        *const std::os::raw::c_char, 57 as std::os::raw::c_int,
                    b"output - outputs[0] == size - ti_sma_start(options)\x00"
                            as *const u8 as *const std::os::raw::c_char);
            } else {};
            return 0 as std::os::raw::c_int;
        }
        pub unsafe extern "C" fn ti_trima_start(mut options:
                *const std::os::raw::c_double) -> std::os::raw::c_int {
            return *options.offset(0 as std::os::raw::c_int as isize) as
                        std::os::raw::c_int - 1 as std::os::raw::c_int;
        }
        pub unsafe extern "C" fn ti_trima(mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double)
            -> std::os::raw::c_int {
            let mut input: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as
                    std::os::raw::c_int;
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            if period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int
            }
            if size <= ti_trima_start(options) {
                return 0 as std::os::raw::c_int
            }
            if period <= 2 as std::os::raw::c_int {
                return ti_sma(size, inputs, options, outputs)
            }
            let mut weights: std::os::raw::c_double =
                1 as std::os::raw::c_int as std::os::raw::c_double /
                    (if period % 2 as std::os::raw::c_int != 0 {
                                (period / 2 as std::os::raw::c_int +
                                            1 as std::os::raw::c_int) *
                                    (period / 2 as std::os::raw::c_int +
                                            1 as std::os::raw::c_int)
                            } else {
                                (period / 2 as std::os::raw::c_int +
                                            1 as std::os::raw::c_int) *
                                    (period / 2 as std::os::raw::c_int)
                            }) as std::os::raw::c_double;
            let mut weight_sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut lead_sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut trail_sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let lead_period: std::os::raw::c_int =
                if period % 2 as std::os::raw::c_int != 0 {
                    (period) / 2 as std::os::raw::c_int
                } else {
                    (period / 2 as std::os::raw::c_int) -
                        1 as std::os::raw::c_int
                };
            let trail_period: std::os::raw::c_int =
                lead_period + 1 as std::os::raw::c_int;
            let mut i: std::os::raw::c_int = 0;
            let mut w: std::os::raw::c_int = 1 as std::os::raw::c_int;
            i = 0 as std::os::raw::c_int;
            while i < period - 1 as std::os::raw::c_int {
                weight_sum +=
                    *input.offset(i as isize) * w as std::os::raw::c_double;
                if i + 1 as std::os::raw::c_int > period - lead_period {
                    lead_sum += *input.offset(i as isize)
                }
                if i + 1 as std::os::raw::c_int <= trail_period {
                    trail_sum += *input.offset(i as isize)
                }
                if (i + 1 as std::os::raw::c_int) < trail_period { w += 1 }
                if i + 1 as std::os::raw::c_int >= period - lead_period {
                    w -= 1
                }
                i += 1
            }
            let mut lsi: std::os::raw::c_int =
                period - 1 as std::os::raw::c_int - lead_period +
                    1 as std::os::raw::c_int;
            let mut tsi1: std::os::raw::c_int =
                period - 1 as std::os::raw::c_int - period +
                        1 as std::os::raw::c_int + trail_period;
            let mut tsi2: std::os::raw::c_int =
                period - 1 as std::os::raw::c_int - period +
                    1 as std::os::raw::c_int;
            i = period - 1 as std::os::raw::c_int;
            while i < size {
                weight_sum += *input.offset(i as isize);
                *output = weight_sum * weights;
                let fresh0 = *output;
                output = output.offset(1);
                lead_sum += *input.offset(i as isize);
                weight_sum += lead_sum;
                weight_sum -= trail_sum;
                let fresh1 = lsi;
                lsi = lsi + 1;
                lead_sum -= *input.offset(fresh1 as isize);
                let fresh2 = tsi1;
                tsi1 = tsi1 + 1;
                trail_sum += *input.offset(fresh2 as isize);
                let fresh3 = tsi2;
                tsi2 = tsi2 + 1;
                trail_sum -= *input.offset(fresh3 as isize);
                i += 1
            }
            if !(output.offset_from(*outputs.offset(0 as std::os::raw::c_int
                                                            as isize)) as std::os::raw::c_long ==
                                        (size - ti_trima_start(options)) as std::os::raw::c_long) as
                            std::os::raw::c_int as std::os::raw::c_long != 0 {
                __assert_rtn(([b't' as i8, b'i' as i8, b'_' as i8, b't' as i8,
                                    b'r' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                                    b'\0' as i8]).as_ptr(),
                    b"indicators/trima.c\x00" as *const u8 as
                        *const std::os::raw::c_char, 103 as std::os::raw::c_int,
                    b"output - outputs[0] == size - ti_trima_start(options)\x00"
                            as *const u8 as *const std::os::raw::c_char);
            } else {};
            return 0 as std::os::raw::c_int;
        }
