use super::run_ownership_case_with_box_candidates;

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
    pub mod a {
        pub type size_t = usize;
        #[inline]
        unsafe extern "C" fn a_bias_call(
            fp: Option<unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int>,
            x: core::ffi::c_int,
        ) -> core::ffi::c_int {
            fp.expect("non-null function pointer")(
                (x ^ 0x55 as core::ffi::c_int) + 7 as core::ffi::c_int,
            )
        }
        static mut state_a: core::ffi::c_int = 0;
        unsafe extern "C" fn target(code: core::ffi::c_int) -> core::ffi::c_int {
            if code < 0 as core::ffi::c_int {
                return if state_a & 1 as core::ffi::c_int != 0 {
                    6 as core::ffi::c_int
                } else {
                    5 as core::ffi::c_int
                };
            }
            state_a ^= code << 1 as core::ffi::c_int;
            let k: core::ffi::c_int =
                (code >> 2 as core::ffi::c_int ^ state_a) & 7 as core::ffi::c_int;
            match k {
                0 => 0 as core::ffi::c_int,
                1 => 2 as core::ffi::c_int,
                2 => 4 as core::ffi::c_int,
                3 => 1 as core::ffi::c_int,
                4 => 3 as core::ffi::c_int,
                5 | 6 => 5 as core::ffi::c_int,
                _ => 7 as core::ffi::c_int,
            }
        }
        #[inline]
        unsafe extern "C" fn wrap(x: core::ffi::c_int) -> core::ffi::c_int {
            target(x - 5 as core::ffi::c_int)
        }
        #[no_mangle]
        pub unsafe extern "C" fn call_a_once(x: core::ffi::c_int) -> core::ffi::c_int {
            let fp: Option<unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int> =
                Some(target as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int);
            let a: core::ffi::c_int = fp.expect("non-null function pointer")(x);
            let b: core::ffi::c_int = wrap(a);
            let c: core::ffi::c_int = target(b ^ 3 as core::ffi::c_int);
            let d: core::ffi::c_int = a_bias_call(
                Some(target as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int),
                b,
            );
            a ^ b << 1 as core::ffi::c_int ^ c << 2 as core::ffi::c_int ^ d << 3 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_a_stream(
            xs: *const core::ffi::c_int,
            n: size_t,
        ) -> core::ffi::c_int {
            let mut acc: size_t = 0 as size_t;
            let mut i: size_t = 0 as size_t;
            while i < n {
                let v: core::ffi::c_int = *xs.add(i);
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < 3 as core::ffi::c_int {
                    let t: core::ffi::c_int = target(v + j);
                    if t & 1 as core::ffi::c_int == 0 as core::ffi::c_int {
                        acc = (acc as core::ffi::c_ulong).wrapping_add(t as core::ffi::c_ulong)
                            as size_t as size_t;
                    } else {
                        acc =
                            (acc as core::ffi::c_ulong ^ (t << j) as core::ffi::c_ulong) as size_t;
                        if t == 5 as core::ffi::c_int {
                            break;
                        }
                    }
                    j += 1;
                }
                i = i.wrapping_add(1);
            }
            if acc as core::ffi::c_ulonglong > 0x7fffffff as core::ffi::c_ulonglong {
                acc = 0x7fffffff as size_t;
            }
            if (acc as core::ffi::c_ulonglong)
                < -(0x80000000 as core::ffi::c_longlong) as core::ffi::c_ulonglong
            {
                acc = -(0x80000000 as core::ffi::c_longlong) as size_t;
            }
            acc as core::ffi::c_int
        }
    }
    pub mod b {
        use crate::src::a::size_t;
        #[inline]
        unsafe extern "C" fn b_twist_call(
            fp: Option<unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int>,
            x: core::ffi::c_int,
        ) -> core::ffi::c_int {
            fp.expect("non-null function pointer")(
                ((x + 9 as core::ffi::c_int) ^ 0x2222 as core::ffi::c_int) - 17 as core::ffi::c_int,
            )
        }
        static mut flipflop: core::ffi::c_int = 0;
        unsafe extern "C" fn target(code: core::ffi::c_int) -> core::ffi::c_int {
            flipflop ^= 1 as core::ffi::c_int;
            if code < 0 as core::ffi::c_int {
                return if flipflop != 0 {
                    2 as core::ffi::c_int
                } else {
                    6 as core::ffi::c_int
                };
            }
            let z: core::ffi::c_int = (code
                ^ (if flipflop != 0 {
                    0x7f as core::ffi::c_int
                } else {
                    0x1f as core::ffi::c_int
                }))
                % 8 as core::ffi::c_int;
            if z == 0 as core::ffi::c_int || z == 7 as core::ffi::c_int {
                return 4 as core::ffi::c_int;
            }
            if z == 1 as core::ffi::c_int || z == 2 as core::ffi::c_int {
                return 3 as core::ffi::c_int;
            }
            if z == 3 as core::ffi::c_int {
                return 1 as core::ffi::c_int;
            }
            if z == 4 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            if z == 5 as core::ffi::c_int {
                return 5 as core::ffi::c_int;
            }
            7 as core::ffi::c_int
        }
        #[inline]
        unsafe extern "C" fn w2(x: core::ffi::c_int) -> core::ffi::c_int {
            target(x + 9 as core::ffi::c_int)
        }
        #[no_mangle]
        pub unsafe extern "C" fn call_b_once(x: core::ffi::c_int) -> core::ffi::c_int {
            let fp: Option<unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int> =
                Some(target as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int);
            let a: core::ffi::c_int = target(x);
            let b: core::ffi::c_int = w2(a);
            let c: core::ffi::c_int = b_twist_call(
                Some(target as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int),
                a,
            );
            let d: core::ffi::c_int = fp.expect("non-null function pointer")(c ^ x);
            a << 1 as core::ffi::c_int
                ^ b << 2 as core::ffi::c_int
                ^ c << 3 as core::ffi::c_int
                ^ d << 4 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_b_stream(
            xs: *const core::ffi::c_int,
            n: size_t,
        ) -> core::ffi::c_int {
            let mut acc: core::ffi::c_int = 1 as core::ffi::c_int;
            let mut i: size_t = 0 as size_t;
            while i < n {
                let v: core::ffi::c_int = *xs.add(i);
                let mut iter: core::ffi::c_int = 0 as core::ffi::c_int;
                loop {
                    iter += 1;
                    if iter > 4 as core::ffi::c_int {
                        break;
                    }
                    let t: core::ffi::c_int = target(v - iter);
                    if t == 6 as core::ffi::c_int {
                        acc -= t;
                        break;
                    } else {
                        if t == 3 as core::ffi::c_int {
                            continue;
                        }
                        acc = (acc * 3 as core::ffi::c_int) ^ t;
                    }
                }
                i = i.wrapping_add(1);
            }
            acc
        }
    }
    pub mod engine {
        use crate::src::a::call_a_once;
        use crate::src::a::process_a_stream;
        use crate::src::a::size_t;
        use crate::src::b::call_b_once;
        use crate::src::b::process_b_stream;
        use crate::src::lib::target;
        use crate::src::util::iv_peek;
        use crate::src::util::iv_pop;
        use crate::src::util::iv_push;
        use crate::src::util::prog_fetch;
        use crate::src::util::prog_init;
        use crate::src::util::vm_trace;
        #[repr(C)]
        pub struct IntVec {
            pub data: *mut core::ffi::c_int,
            pub len: size_t,
            pub cap: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for IntVec {}
        #[automatically_derived]
        impl ::core::clone::Clone for IntVec {
            #[inline]
            fn clone(&self) -> IntVec {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct Program {
            pub code: *const core::ffi::c_int,
            pub n: size_t,
            pub ip: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Program {}
        #[automatically_derived]
        impl ::core::clone::Clone for Program {
            #[inline]
            fn clone(&self) -> Program {
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct VM {
            pub stack: IntVec,
            pub trace: IntVec,
            pub steps: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for VM {}
        #[automatically_derived]
        impl ::core::clone::Clone for VM {
            #[inline]
            fn clone(&self) -> VM {
                let _: ::core::clone::AssertParamIsClone<IntVec>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[inline]
        unsafe extern "C" fn inline_call(
            f: Option<unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int>,
            x: core::ffi::c_int,
        ) -> core::ffi::c_int {
            f.expect("non-null function pointer")(x)
        }
        unsafe extern "C" fn classify(
            impl_0: core::ffi::c_int,
            x: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if impl_0 == 0 as core::ffi::c_int {
                return inline_call(
                    Some(call_a_once as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int),
                    x,
                );
            }
            if impl_0 == 1 as core::ffi::c_int {
                return call_b_once(x + 1 as core::ffi::c_int);
            }
            inline_call(
                Some(target as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int),
                target(x + 1 as core::ffi::c_int),
            )
        }
        unsafe extern "C" fn process_stream(
            impl_0: core::ffi::c_int,
            buf: *const core::ffi::c_int,
            n: size_t,
        ) -> core::ffi::c_int {
            if impl_0 == 0 as core::ffi::c_int {
                return process_a_stream(buf, n);
            }
            if impl_0 == 1 as core::ffi::c_int {
                return process_b_stream(buf, n);
            }
            let mut acc: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: size_t = 0 as size_t;
            while i < n {
                let t: core::ffi::c_int = target(*buf.add(i));
                if t & 1 as core::ffi::c_int == 0 as core::ffi::c_int {
                    acc += t * 2 as core::ffi::c_int;
                } else {
                    acc ^= t + 7 as core::ffi::c_int;
                }
                i = i.wrapping_add(1);
            }
            acc
        }
        #[no_mangle]
        pub unsafe extern "C" fn run_engine(
            impl_id: core::ffi::c_int,
            code: *const core::ffi::c_int,
            n: size_t,
            vm: *mut VM,
        ) -> core::ffi::c_int {
            let mut p: Program = Program {
                code: std::ptr::null::<core::ffi::c_int>(),
                n: 0,
                ip: 0,
            };
            prog_init(&mut p, code, n);
            let mut op: core::ffi::c_int = 0;
            while prog_fetch(&mut p, &mut op) {
                (*vm).steps += 1;
                match op {
                    0 => {
                        let mut imm: core::ffi::c_int = 0;
                        if !prog_fetch(&mut p, &mut imm) {
                            return 1 as core::ffi::c_int;
                        }
                        iv_push(&mut (*vm).stack, imm);
                        vm_trace(vm, 0 as core::ffi::c_int);
                    }
                    1 => {
                        let mut a: core::ffi::c_int = 0;
                        let mut b: core::ffi::c_int = 0;
                        if !iv_pop(&mut (*vm).stack, &mut b) || !iv_pop(&mut (*vm).stack, &mut a) {
                            return 2 as core::ffi::c_int;
                        }
                        iv_push(&mut (*vm).stack, a + b);
                        vm_trace(vm, 1 as core::ffi::c_int);
                    }
                    2 => {
                        let mut a_0: core::ffi::c_int = 0;
                        let mut b_0: core::ffi::c_int = 0;
                        if !iv_pop(&mut (*vm).stack, &mut b_0)
                            || !iv_pop(&mut (*vm).stack, &mut a_0)
                        {
                            return 3 as core::ffi::c_int;
                        }
                        iv_push(&mut (*vm).stack, a_0 * b_0);
                        vm_trace(vm, 2 as core::ffi::c_int);
                    }
                    3 => {
                        let a_1: core::ffi::c_int =
                            iv_peek(&mut (*vm).stack, 0 as core::ffi::c_int);
                        iv_push(&mut (*vm).stack, a_1);
                        vm_trace(vm, 3 as core::ffi::c_int);
                    }
                    4 => {
                        let mut tmp: core::ffi::c_int = 0;
                        if !iv_pop(&mut (*vm).stack, &mut tmp) {
                            return 4 as core::ffi::c_int;
                        }
                        vm_trace(vm, 4 as core::ffi::c_int);
                    }
                    5 => {
                        let x: core::ffi::c_int = iv_peek(&mut (*vm).stack, 0 as core::ffi::c_int);
                        let bucket: core::ffi::c_int = classify(impl_id, x);
                        iv_push(&mut (*vm).stack, bucket);
                        match bucket {
                            0 => {
                                vm_trace(vm, 5 as core::ffi::c_int);
                            }
                            1 => {
                                vm_trace(vm, 6 as core::ffi::c_int);
                            }
                            2 => {
                                vm_trace(vm, 7 as core::ffi::c_int);
                            }
                            3 | 4 => {
                                vm_trace(vm, 8 as core::ffi::c_int);
                            }
                            _ => {
                                vm_trace(vm, 9 as core::ffi::c_int);
                            }
                        }
                    }
                    6 => {
                        let mut k: core::ffi::c_int = 0;
                        if !prog_fetch(&mut p, &mut k) {
                            return 5 as core::ffi::c_int;
                        }
                        let mut cond: core::ffi::c_int = 0;
                        if !iv_pop(&mut (*vm).stack, &mut cond) {
                            return 6 as core::ffi::c_int;
                        }
                        if cond != 0 {
                            if k as size_t > (p.n).wrapping_sub(p.ip) {
                                return 7 as core::ffi::c_int;
                            }
                            p.ip = (p.ip as core::ffi::c_ulong)
                                .wrapping_add(k as size_t as core::ffi::c_ulong)
                                as size_t as size_t;
                            vm_trace(vm, 10 as core::ffi::c_int);
                        } else {
                            vm_trace(vm, 11 as core::ffi::c_int);
                        }
                    }
                    7 => {
                        let mut times: core::ffi::c_int = 0;
                        if !prog_fetch(&mut p, &mut times) {
                            return 8 as core::ffi::c_int;
                        }
                        if p.ip >= p.n {
                            return 9 as core::ffi::c_int;
                        }
                        let saved_ip: size_t = p.ip;
                        let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                        while i < times {
                            let mut inner: Program = p;
                            inner.ip = saved_ip;
                            let rc: core::ffi::c_int =
                                run_engine(impl_id, (inner.code).add(inner.ip), 1 as size_t, vm);
                            if rc != 0 {
                                p.ip = saved_ip.wrapping_add(1 as size_t);
                                vm_trace(vm, 12 as core::ffi::c_int);
                                break;
                            } else {
                                i += 1;
                            }
                        }
                        p.ip = saved_ip.wrapping_add(1 as size_t);
                    }
                    8 => {
                        let x_0: core::ffi::c_int =
                            iv_peek(&mut (*vm).stack, 0 as core::ffi::c_int);
                        let y: core::ffi::c_int = classify(impl_id, x_0);
                        iv_push(&mut (*vm).stack, y);
                        vm_trace(vm, 13 as core::ffi::c_int);
                    }
                    9 => {
                        let mut m: core::ffi::c_int = 0;
                        if !prog_fetch(&mut p, &mut m) {
                            return 10 as core::ffi::c_int;
                        }
                        if m < 0 as core::ffi::c_int || m as size_t > (*vm).stack.len {
                            return 11 as core::ffi::c_int;
                        }
                        let vla = m as usize;
                        let mut tmp_0: Vec<core::ffi::c_int> = ::std::vec::from_elem(0, vla);
                        let mut i_0: core::ffi::c_int = m - 1 as core::ffi::c_int;
                        while i_0 >= 0 as core::ffi::c_int {
                            iv_pop(
                                &mut (*vm).stack,
                                &mut *tmp_0.as_mut_ptr().offset(i_0 as isize),
                            );
                            i_0 -= 1;
                        }
                        let mut i_1: core::ffi::c_int = m - 1 as core::ffi::c_int;
                        while i_1 >= 0 as core::ffi::c_int {
                            iv_pop(
                                &mut (*vm).stack,
                                &mut *tmp_0.as_mut_ptr().offset(i_1 as isize),
                            );
                            i_1 -= 1;
                        }
                        let s: core::ffi::c_int =
                            process_stream(impl_id, tmp_0.as_ptr(), m as size_t);
                        iv_push(&mut (*vm).stack, s);
                        vm_trace(vm, 14 as core::ffi::c_int);
                    }
                    10 => return 0 as core::ffi::c_int,
                    _ => return 99 as core::ffi::c_int,
                }
            }
            0 as core::ffi::c_int
        }
    }
    pub mod lib {
        #[no_mangle]
        pub unsafe extern "C" fn target(code: core::ffi::c_int) -> core::ffi::c_int {
            if code < 0 as core::ffi::c_int {
                return 7 as core::ffi::c_int;
            }
            let m: core::ffi::c_int = code % 10 as core::ffi::c_int;
            if m == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            if m <= 3 as core::ffi::c_int {
                return 1 as core::ffi::c_int;
            }
            if m <= 6 as core::ffi::c_int {
                return 2 as core::ffi::c_int;
            }
            if m == 7 as core::ffi::c_int {
                return 3 as core::ffi::c_int;
            }
            4 as core::ffi::c_int
        }
    }
    pub mod main {
        use crate::src::a::size_t;
        use crate::src::engine::run_engine;
        use crate::src::engine::IntVec;
        use crate::src::engine::VM;
        use crate::src::util::iv_free;
        use crate::src::util::iv_init;
        use crate::src::util::iv_push;
        use crate::src::util::vm_free;
        use crate::src::util::vm_init;
        use crate::src::util::vm_print;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stdin: *mut FILE;
            static mut stdout: *mut FILE;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn strtol(
                __nptr: *const core::ffi::c_char,
                __endptr: *mut *mut core::ffi::c_char,
                __base: core::ffi::c_int,
            ) -> core::ffi::c_long;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
        }
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        #[repr(C)]
        pub struct _IO_FILE {
            pub _flags: core::ffi::c_int,
            pub _IO_read_ptr: *mut core::ffi::c_char,
            pub _IO_read_end: *mut core::ffi::c_char,
            pub _IO_read_base: *mut core::ffi::c_char,
            pub _IO_write_base: *mut core::ffi::c_char,
            pub _IO_write_ptr: *mut core::ffi::c_char,
            pub _IO_write_end: *mut core::ffi::c_char,
            pub _IO_buf_base: *mut core::ffi::c_char,
            pub _IO_buf_end: *mut core::ffi::c_char,
            pub _IO_save_base: *mut core::ffi::c_char,
            pub _IO_backup_base: *mut core::ffi::c_char,
            pub _IO_save_end: *mut core::ffi::c_char,
            pub _markers: *mut _IO_marker,
            pub _chain: *mut _IO_FILE,
            pub _fileno: core::ffi::c_int,
            pub _flags2: core::ffi::c_int,
            pub _old_offset: __off_t,
            pub _cur_column: core::ffi::c_ushort,
            pub _vtable_offset: core::ffi::c_schar,
            pub _shortbuf: [core::ffi::c_char; 1],
            pub _lock: *mut core::ffi::c_void,
            pub _offset: __off64_t,
            pub _codecvt: *mut _IO_codecvt,
            pub _wide_data: *mut _IO_wide_data,
            pub _freeres_list: *mut _IO_FILE,
            pub _freeres_buf: *mut core::ffi::c_void,
            pub __pad5: size_t,
            pub _mode: core::ffi::c_int,
            pub _unused2: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for _IO_FILE {}
        #[automatically_derived]
        impl ::core::clone::Clone for _IO_FILE {
            #[inline]
            fn clone(&self) -> _IO_FILE {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_marker>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_ushort>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_schar>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 1]>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<__off64_t>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_codecvt>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_wide_data>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        pub type _IO_lock_t = ();
        pub type FILE = _IO_FILE;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const true_0: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const false_0: core::ffi::c_int = 0 as core::ffi::c_int;
        unsafe extern "C" fn usage(p: *const core::ffi::c_char) {
            fprintf(stderr,
                b"Usage: %s [--stdin] [bytecodes...]\nBytecodes are integers forming a small VM program.\n\0"
                        as *const u8 as *const core::ffi::c_char, p);
        }
        unsafe extern "C" fn read_stdin(v: *mut IntVec) -> size_t {
            let mut buf: [core::ffi::c_char; 4096] = [0; 4096];
            let mut count: size_t = 0 as size_t;
            while !(fgets(
                buf.as_mut_ptr(),
                ::core::mem::size_of::<[core::ffi::c_char; 4096]>() as core::ffi::c_int,
                stdin,
            ))
            .is_null()
            {
                let mut p: *mut core::ffi::c_char = buf.as_mut_ptr();
                while *p != 0 {
                    let mut q: *mut core::ffi::c_char = p;
                    while *q as core::ffi::c_int != 0
                        && *q as core::ffi::c_int != ' ' as i32
                        && *q as core::ffi::c_int != '\t' as i32
                        && *q as core::ffi::c_int != '\n' as i32
                        && *q as core::ffi::c_int != '\r' as i32
                    {
                        q = q.offset(1);
                    }
                    let save: core::ffi::c_char = *q;
                    *q = '\0' as i32 as core::ffi::c_char;
                    if *p != 0 {
                        let mut e: *mut core::ffi::c_char =
                            std::ptr::null_mut::<core::ffi::c_char>();
                        let t: core::ffi::c_long = strtol(p, &mut e, 10 as core::ffi::c_int);
                        if !e.is_null() && *e as core::ffi::c_int == '\0' as i32 {
                            iv_push(v, t as core::ffi::c_int);
                            count = count.wrapping_add(1);
                        }
                    }
                    *q = save;
                    p = if *q as core::ffi::c_int != 0 {
                        q.offset(1 as core::ffi::c_int as isize)
                    } else {
                        q
                    };
                }
            }
            count
        }
        unsafe fn main_0(
            argc: core::ffi::c_int,
            argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            let mut use_stdin: bool = false_0 != 0;
            let mut code: IntVec = IntVec {
                data: std::ptr::null_mut::<core::ffi::c_int>(),
                len: 0,
                cap: 0,
            };
            iv_init(&mut code);
            let mut i: core::ffi::c_int = 1 as core::ffi::c_int;
            while i < argc {
                if strcmp(
                    *argv.offset(i as isize),
                    b"--help\0" as *const u8 as *const core::ffi::c_char,
                ) == 0
                {
                    usage(*argv.offset(0 as core::ffi::c_int as isize));
                    iv_free(&mut code);
                    return 0 as core::ffi::c_int;
                } else if strcmp(
                    *argv.offset(i as isize),
                    b"--stdin\0" as *const u8 as *const core::ffi::c_char,
                ) == 0
                {
                    use_stdin = true_0 != 0;
                } else {
                    let mut e: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
                    let t: core::ffi::c_long =
                        strtol(*argv.offset(i as isize), &mut e, 10 as core::ffi::c_int);
                    if !e.is_null() && *e as core::ffi::c_int == '\0' as i32 {
                        iv_push(&mut code, t as core::ffi::c_int);
                    } else {
                        fprintf(
                            stderr,
                            b"skip '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                            *argv.offset(i as isize),
                        );
                    }
                }
                i += 1;
            }
            if use_stdin {
                read_stdin(&mut code);
            }
            if code.len == 0 as size_t {
                fprintf(
                    stderr,
                    b"no program\n\0" as *const u8 as *const core::ffi::c_char,
                );
                iv_free(&mut code);
                return 2 as core::ffi::c_int;
            }
            let mut vmA: VM = VM {
                stack: IntVec {
                    data: std::ptr::null_mut::<core::ffi::c_int>(),
                    len: 0,
                    cap: 0,
                },
                trace: IntVec {
                    data: std::ptr::null_mut::<core::ffi::c_int>(),
                    len: 0,
                    cap: 0,
                },
                steps: 0,
            };
            let mut vmB: VM = VM {
                stack: IntVec {
                    data: std::ptr::null_mut::<core::ffi::c_int>(),
                    len: 0,
                    cap: 0,
                },
                trace: IntVec {
                    data: std::ptr::null_mut::<core::ffi::c_int>(),
                    len: 0,
                    cap: 0,
                },
                steps: 0,
            };
            let mut vmE: VM = VM {
                stack: IntVec {
                    data: std::ptr::null_mut::<core::ffi::c_int>(),
                    len: 0,
                    cap: 0,
                },
                trace: IntVec {
                    data: std::ptr::null_mut::<core::ffi::c_int>(),
                    len: 0,
                    cap: 0,
                },
                steps: 0,
            };
            vm_init(&mut vmA);
            vm_init(&mut vmB);
            vm_init(&mut vmE);
            let rcA: core::ffi::c_int =
                run_engine(0 as core::ffi::c_int, code.data, code.len, &mut vmA);
            let rcB: core::ffi::c_int =
                run_engine(1 as core::ffi::c_int, code.data, code.len, &mut vmB);
            let rcE: core::ffi::c_int =
                run_engine(2 as core::ffi::c_int, code.data, code.len, &mut vmE);
            printf(
                b"RC:A=%d B=%d EXT=%d\n\0" as *const u8 as *const core::ffi::c_char,
                rcA,
                rcB,
                rcE,
            );
            vm_print(
                stdout,
                b"A:\0" as *const u8 as *const core::ffi::c_char,
                &mut vmA,
            );
            vm_print(
                stdout,
                b"B:\0" as *const u8 as *const core::ffi::c_char,
                &mut vmB,
            );
            vm_print(
                stdout,
                b"EXT:\0" as *const u8 as *const core::ffi::c_char,
                &mut vmE,
            );
            vm_free(&mut vmA);
            vm_free(&mut vmB);
            vm_free(&mut vmE);
            iv_free(&mut code);
            0 as core::ffi::c_int
        }
        pub fn main() {
            let mut args: Vec<*mut core::ffi::c_char> = Vec::new();
            for arg in ::std::env::args() {
                args.push(
                    (::std::ffi::CString::new(arg))
                        .expect("Failed to convert argument into CString.")
                        .into_raw(),
                );
            }
            args.push(::core::ptr::null_mut());
            unsafe {
                ::std::process::exit(main_0(
                    (args.len() - 1) as core::ffi::c_int,
                    args.as_mut_ptr() as *mut *mut core::ffi::c_char,
                ) as i32)
            }
        }
    }
    pub mod util {
        use crate::src::a::size_t;
        use crate::src::engine::IntVec;
        use crate::src::engine::Program;
        use crate::src::engine::VM;
        use crate::src::main::FILE;
        extern "C" {
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fputc(__c: core::ffi::c_int, __stream: *mut FILE) -> core::ffi::c_int;
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const true_0: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const false_0: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const SIZE_MAX: core::ffi::c_ulong = 18446744073709551615 as core::ffi::c_ulong;
        #[no_mangle]
        pub unsafe extern "C" fn iv_init(v: *mut IntVec) {
            (*v).data = std::ptr::null_mut::<core::ffi::c_int>();
            (*v).cap = 0 as size_t;
            (*v).len = (*v).cap;
        }
        #[no_mangle]
        pub unsafe extern "C" fn iv_free(v: *mut IntVec) {
            free((*v).data as *mut core::ffi::c_void);
            (*v).data = std::ptr::null_mut::<core::ffi::c_int>();
            (*v).cap = 0 as size_t;
            (*v).len = (*v).cap;
        }
        #[no_mangle]
        pub unsafe extern "C" fn iv_reserve(v: *mut IntVec, need: size_t) -> bool {
            if need <= (*v).cap {
                return true_0 != 0;
            }
            let mut nc: size_t = if (*v).cap != 0 { (*v).cap } else { 8 as size_t };
            while nc < need {
                if nc > (SIZE_MAX as size_t).wrapping_div(2 as size_t) {
                    return false_0 != 0;
                }
                nc = (nc as core::ffi::c_ulong).wrapping_mul(2 as core::ffi::c_ulong) as size_t
                    as size_t;
            }
            let p: *mut core::ffi::c_int = realloc(
                (*v).data as *mut core::ffi::c_void,
                nc.wrapping_mul(::core::mem::size_of::<core::ffi::c_int>() as size_t),
            ) as *mut core::ffi::c_int;
            if p.is_null() {
                return false_0 != 0;
            }
            (*v).data = p;
            (*v).cap = nc;
            true_0 != 0
        }
        #[no_mangle]
        pub unsafe extern "C" fn iv_push(v: *mut IntVec, x: core::ffi::c_int) -> bool {
            if (*v).len == (*v).cap
                && !iv_reserve(
                    v,
                    if (*v).cap != 0 {
                        ((*v).cap).wrapping_mul(2 as size_t)
                    } else {
                        8 as size_t
                    },
                )
            {
                return false_0 != 0;
            }
            let fresh0 = (*v).len;
            (*v).len = ((*v).len).wrapping_add(1);
            *((*v).data).add(fresh0) = x;
            true_0 != 0
        }
        #[no_mangle]
        pub unsafe extern "C" fn iv_pop(v: *mut IntVec, out: *mut core::ffi::c_int) -> bool {
            if (*v).len == 0 {
                return false_0 != 0;
            }
            if !out.is_null() {
                *out = *((*v).data).add(((*v).len).wrapping_sub(1 as size_t));
            }
            (*v).len = ((*v).len).wrapping_sub(1);
            true_0 != 0
        }
        #[no_mangle]
        pub unsafe extern "C" fn iv_peek(
            v: *const IntVec,
            def: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if (*v).len != 0 {
                *((*v).data).add(((*v).len).wrapping_sub(1 as size_t))
            } else {
                def
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn prog_init(
            p: *mut Program,
            code: *const core::ffi::c_int,
            n: size_t,
        ) {
            (*p).code = code;
            (*p).n = n;
            (*p).ip = 0 as size_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn prog_fetch(p: *mut Program, out: *mut core::ffi::c_int) -> bool {
            if (*p).ip >= (*p).n {
                return false_0 != 0;
            }
            let fresh1 = (*p).ip;
            (*p).ip = ((*p).ip).wrapping_add(1);
            *out = *((*p).code).add(fresh1);
            true_0 != 0
        }
        #[no_mangle]
        pub unsafe extern "C" fn vm_init(vm: *mut VM) {
            iv_init(&mut (*vm).stack);
            iv_init(&mut (*vm).trace);
            (*vm).steps = 0 as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn vm_free(vm: *mut VM) {
            iv_free(&mut (*vm).stack);
            iv_free(&mut (*vm).trace);
            (*vm).steps = 0 as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn vm_trace(vm: *mut VM, t: core::ffi::c_int) {
            iv_push(&mut (*vm).trace, t);
        }
        #[no_mangle]
        pub unsafe extern "C" fn vm_print(
            fp: *mut FILE,
            label: *const core::ffi::c_char,
            vm: *const VM,
        ) {
            fprintf(
                fp,
                b"%sSTACK_TOP=%d STEPS=%d TRACE=\0" as *const u8 as *const core::ffi::c_char,
                label,
                iv_peek(&(*vm).stack, -(777 as core::ffi::c_int)),
                (*vm).steps,
            );
            let mut i: size_t = 0 as size_t;
            while i < (*vm).trace.len {
                fputc(
                    [
                        b'a' as i8,
                        b'b' as i8,
                        b'c' as i8,
                        b'd' as i8,
                        b'e' as i8,
                        b'f' as i8,
                        b'g' as i8,
                        b'h' as i8,
                        b'i' as i8,
                        b'j' as i8,
                        b'k' as i8,
                        b'l' as i8,
                        b'm' as i8,
                        b'n' as i8,
                        b'o' as i8,
                        b'p' as i8,
                        b'q' as i8,
                        b'r' as i8,
                        b's' as i8,
                        b't' as i8,
                        b'u' as i8,
                        b'v' as i8,
                        b'w' as i8,
                        b'x' as i8,
                        b'y' as i8,
                        b'z' as i8,
                        b'\0' as i8,
                    ][(*((*vm).trace.data).add(i) & 25 as core::ffi::c_int) as usize]
                        as core::ffi::c_int,
                    fp,
                );
                i = i.wrapping_add(1);
            }
            fputc('\n' as i32, fp);
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("tu_linkage", SOURCE, &[], &[]);
}
