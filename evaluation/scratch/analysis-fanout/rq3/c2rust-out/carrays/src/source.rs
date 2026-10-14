extern "C" {
    fn drand48() -> ::core::ffi::c_double;
    fn malloc(__size: size_t) -> *mut ::core::ffi::c_void;
    fn memcpy(
        __dest: *mut ::core::ffi::c_void,
        __src: *const ::core::ffi::c_void,
        __n: size_t,
    ) -> *mut ::core::ffi::c_void;
    fn __assert_fail(
        __assertion: *const ::core::ffi::c_char,
        __file: *const ::core::ffi::c_char,
        __line: ::core::ffi::c_uint,
        __function: *const ::core::ffi::c_char,
    ) -> !;
}
pub type size_t = usize;
pub type __uint32_t = u32;
pub type uint32_t = __uint32_t;
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<
    ::core::ffi::c_void,
>();
pub const __ASSERT_FUNCTION: [::core::ffi::c_char; 63] = unsafe {
    ::core::mem::transmute::<
        [u8; 63],
        [::core::ffi::c_char; 63],
    >(*b"void *gca_qselect(void *, size_t, size_t, size_t, int, void *)\0")
};
pub const SIZE_MAX: ::core::ffi::c_ulong = 18446744073709551615 as ::core::ffi::c_ulong;
unsafe extern "C" fn call_compar(
    mut compar_id: ::core::ffi::c_int,
    mut a: *const ::core::ffi::c_void,
    mut b: *const ::core::ffi::c_void,
    mut arg: *mut ::core::ffi::c_void,
) -> ::core::ffi::c_int {
    return 0 as ::core::ffi::c_int;
}
unsafe extern "C" fn call_searchf(
    mut compar_id: ::core::ffi::c_int,
    mut _val: *const ::core::ffi::c_void,
    mut _arg: *const ::core::ffi::c_void,
) -> ::core::ffi::c_int {
    return 0 as ::core::ffi::c_int;
}
#[inline]
unsafe extern "C" fn gca_swapm(
    mut aa: *mut ::core::ffi::c_void,
    mut bb: *mut ::core::ffi::c_void,
    mut es: size_t,
) {
    let mut end = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut a = aa as *mut ::core::ffi::c_char;
    let mut b = bb as *mut ::core::ffi::c_char;
    let mut tmp: ::core::ffi::c_char = 0;
    end = a.offset(es as isize);
    while a < end {
        tmp = *a;
        *a = *b;
        *b = tmp;
        a = a.offset(1);
        b = b.offset(1);
    }
}
#[inline]
unsafe extern "C" fn gca_isortr(
    mut _ptr: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut m: size_t,
    mut el: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let mut b = _ptr as *mut ::core::ffi::c_char;
    let mut pi = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut pj = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut end = b.offset(el.wrapping_mul(n.wrapping_add(m)) as isize);
    pi = b.offset(el.wrapping_mul(n) as isize);
    while pi < end {
        pj = pi;
        while pj > b
            && call_compar(
                compar_id,
                pj.offset(-(el as isize)) as *const ::core::ffi::c_void,
                pj as *const ::core::ffi::c_void,
                arg,
            ) > 0 as ::core::ffi::c_int
        {
            gca_swapm(
                pj.offset(-(el as isize)) as *mut ::core::ffi::c_void,
                pj as *mut ::core::ffi::c_void,
                el,
            );
            pj = pj.offset(-(el as isize));
        }
        pi = pi.offset(el as isize);
    }
}
#[inline]
unsafe extern "C" fn gca_imerge(
    mut _ptr: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut m: size_t,
    mut el: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let mut b = _ptr as *mut ::core::ffi::c_char;
    let mut pi = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut pj = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut end = b.offset(el.wrapping_mul(n.wrapping_add(m)) as isize);
    pi = b.offset(el.wrapping_mul(n) as isize);
    while pi < end {
        pj = pi;
        while pj > b
            && call_compar(
                compar_id,
                pj.offset(-(el as isize)) as *const ::core::ffi::c_void,
                pj as *const ::core::ffi::c_void,
                arg,
            ) > 0 as ::core::ffi::c_int
        {
            gca_swapm(
                pj.offset(-(el as isize)) as *mut ::core::ffi::c_void,
                pj as *mut ::core::ffi::c_void,
                el,
            );
            pj = pj.offset(-(el as isize));
        }
        if pj == pi {
            break;
        }
        pi = pi.offset(el as isize);
    }
}
#[no_mangle]
pub unsafe extern "C" fn gca_calc_GCD(mut a: uint32_t, mut b: uint32_t) -> uint32_t {
    let mut shift: uint32_t = 0;
    if a == 0 as uint32_t {
        return b;
    }
    if b == 0 as uint32_t {
        return a;
    }
    shift = 0 as uint32_t;
    while (a | b) & 1 as uint32_t == 0 as uint32_t {
        a >>= 1 as ::core::ffi::c_int;
        b >>= 1 as ::core::ffi::c_int;
        shift = shift.wrapping_add(1);
    }
    while a & 1 as uint32_t == 0 as uint32_t {
        a >>= 1 as ::core::ffi::c_int;
    }
    loop {
        while b & 1 as uint32_t == 0 as uint32_t {
            b >>= 1 as ::core::ffi::c_int;
        }
        if a > b {
            let mut _tmp: uint32_t = a as uint32_t;
            a = b;
            b = _tmp as uint32_t;
        }
        b = b.wrapping_sub(a);
        if !(b != 0 as uint32_t) {
            break;
        }
    }
    return a << shift;
}
#[no_mangle]
pub unsafe extern "C" fn gca_cycle_left(
    mut _ptr: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
    mut shift: size_t,
) {
    let mut ptr = _ptr as *mut ::core::ffi::c_char;
    if n <= 1 as size_t || shift == 0 {
        return;
    }
    shift = shift.wrapping_rem(n);
    let mut i: size_t = 0;
    let mut j: size_t = 0;
    let mut k: size_t = 0;
    let mut gcd: size_t = gca_calc_GCD(n as uint32_t, shift as uint32_t) as size_t;
    let vla = es as usize;
    let mut tmp: Vec<::core::ffi::c_char> = ::std::vec::from_elem(0, vla);
    i = 0 as size_t;
    while i < gcd {
        memcpy(
            tmp.as_mut_ptr() as *mut ::core::ffi::c_void,
            ptr.offset(es.wrapping_mul(i) as isize) as *const ::core::ffi::c_void,
            es,
        );
        j = i;
        loop {
            k = j.wrapping_add(shift);
            if k >= n {
                k = (k as ::core::ffi::c_ulong).wrapping_sub(n as ::core::ffi::c_ulong)
                    as size_t as size_t;
            }
            if k == i {
                break;
            }
            memcpy(
                ptr.offset(es.wrapping_mul(j) as isize) as *mut ::core::ffi::c_void,
                ptr.offset(es.wrapping_mul(k) as isize) as *const ::core::ffi::c_void,
                es,
            );
            j = k;
        }
        memcpy(
            ptr.offset(es.wrapping_mul(j) as isize) as *mut ::core::ffi::c_void,
            tmp.as_mut_ptr() as *const ::core::ffi::c_void,
            es,
        );
        i = i.wrapping_add(1);
    }
}
#[no_mangle]
pub unsafe extern "C" fn gca_cycle_right(
    mut _ptr: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
    mut shift: size_t,
) {
    if n == 0 || shift == 0 {
        return;
    }
    shift = shift.wrapping_rem(n);
    gca_cycle_left(_ptr, n, es, n.wrapping_sub(shift));
}
#[no_mangle]
pub unsafe extern "C" fn gca_reverse(
    mut _ptr: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
) {
    if n <= 1 as size_t || es == 0 {
        return;
    }
    let mut a = _ptr as *mut ::core::ffi::c_char;
    let mut b = a.offset(es.wrapping_mul(n.wrapping_sub(1 as size_t)) as isize);
    while a < b {
        gca_swapm(a as *mut ::core::ffi::c_void, b as *mut ::core::ffi::c_void, es);
        a = a.offset(es as isize);
        b = b.offset(-(es as isize));
    }
}
#[no_mangle]
pub unsafe extern "C" fn gca_shuffle(
    mut base: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
) {
    gca_sample(base, n, es, n);
}
#[no_mangle]
pub unsafe extern "C" fn gca_sample(
    mut base: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
    mut m: size_t,
) {
    let mut b = base as *mut ::core::ffi::c_char;
    let mut i: size_t = 0;
    let mut j: size_t = 0;
    i = 0 as size_t;
    while i < m {
        j = (i as ::core::ffi::c_double
            + n.wrapping_sub(i) as ::core::ffi::c_double * drand48()) as size_t;
        gca_swapm(
            b.offset(es.wrapping_mul(i) as isize) as *mut ::core::ffi::c_void,
            b.offset(es.wrapping_mul(j) as isize) as *mut ::core::ffi::c_void,
            es,
        );
        i = i.wrapping_add(1);
    }
}
#[no_mangle]
pub unsafe extern "C" fn gca_merge(
    mut _dst: *mut ::core::ffi::c_void,
    mut ndst: size_t,
    mut nsrc: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let mut dst = _dst as *mut ::core::ffi::c_char;
    let mut src = dst.offset(es.wrapping_mul(ndst) as isize);
    let mut end = dst.offset(es.wrapping_mul(ndst.wrapping_add(nsrc)) as isize);
    if !(nsrc == 0 || ndst == 0) {
        if !(call_compar(
            compar_id,
            src.offset(-(es as isize)) as *const ::core::ffi::c_void,
            src as *const ::core::ffi::c_void,
            arg,
        ) <= 0 as ::core::ffi::c_int)
        {
            if call_compar(
                compar_id,
                dst as *const ::core::ffi::c_void,
                end.offset(-(es as isize)) as *const ::core::ffi::c_void,
                arg,
            ) >= 0 as ::core::ffi::c_int
            {
                gca_cycle_left(dst as *mut ::core::ffi::c_void, ndst, es, ndst);
            } else if ndst.wrapping_add(nsrc) < 6 as size_t {
                gca_imerge(
                    dst as *mut ::core::ffi::c_void,
                    ndst,
                    nsrc,
                    es,
                    compar_id,
                    arg,
                );
            } else {
                gca_qsort(
                    dst as *mut ::core::ffi::c_void,
                    ndst.wrapping_add(nsrc),
                    es,
                    compar_id,
                    arg,
                );
            }
        }
    }
}
#[no_mangle]
pub unsafe extern "C" fn gca_bsearch(
    mut _ptr: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
    mut searchf_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) -> *mut ::core::ffi::c_void {
    if n == 0 as size_t {
        return NULL;
    }
    let mut ptr = _ptr as *mut ::core::ffi::c_char;
    let mut mptr = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut l: size_t = 0 as size_t;
    let mut r: size_t = n.wrapping_sub(1 as size_t);
    let mut mid: size_t = 0;
    let mut cmp: ::core::ffi::c_int = 0;
    loop {
        mid = l.wrapping_add(r.wrapping_sub(l).wrapping_div(2 as size_t));
        mptr = ptr.offset(es.wrapping_mul(mid) as isize);
        cmp = call_searchf(searchf_id, mptr as *const ::core::ffi::c_void, arg);
        if cmp == 0 as ::core::ffi::c_int {
            return mptr as *mut ::core::ffi::c_void
        } else if cmp > 0 as ::core::ffi::c_int {
            if mid == 0 {
                return NULL;
            }
            r = mid.wrapping_sub(1 as size_t);
        } else if cmp < 0 as ::core::ffi::c_int {
            if mid.wrapping_add(1 as size_t) == n {
                return NULL;
            }
            l = mid.wrapping_add(1 as size_t);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn gca_lsearch(
    mut base: *mut ::core::ffi::c_void,
    mut n: size_t,
    mut es: size_t,
    mut searchf_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) -> *mut ::core::ffi::c_void {
    let mut b = base as *mut ::core::ffi::c_char;
    let mut end = b.offset(es.wrapping_mul(n) as isize);
    while b < end {
        if call_searchf(searchf_id, b as *const ::core::ffi::c_void, arg)
            == 0 as ::core::ffi::c_int
        {
            return b as *mut ::core::ffi::c_void;
        }
        b = b.offset(1);
    }
    return NULL;
}
#[no_mangle]
pub unsafe extern "C" fn gca_qpart(
    mut base: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) -> size_t {
    if nel <= 1 as size_t {
        return 0 as size_t;
    }
    let vla = es as usize;
    let mut pivot: Vec<::core::ffi::c_char> = ::std::vec::from_elem(0, vla);
    let mut b = base as *mut ::core::ffi::c_char;
    let mut pl = b;
    let mut pr = b.offset(es.wrapping_mul(nel.wrapping_sub(1 as size_t)) as isize);
    memcpy(
        pivot.as_mut_ptr() as *mut ::core::ffi::c_void,
        b as *const ::core::ffi::c_void,
        es,
    );
    while pl < pr {
        while pl < pr {
            if call_compar(
                compar_id,
                pr as *const ::core::ffi::c_void,
                pivot.as_mut_ptr() as *const ::core::ffi::c_void,
                arg,
            ) < 0 as ::core::ffi::c_int
            {
                memcpy(
                    pl as *mut ::core::ffi::c_void,
                    pr as *const ::core::ffi::c_void,
                    es,
                );
                pl = pl.offset(es as isize);
                break;
            } else {
                pr = pr.offset(-(es as isize));
            }
        }
        while pl < pr {
            if call_compar(
                compar_id,
                pl as *const ::core::ffi::c_void,
                pivot.as_mut_ptr() as *const ::core::ffi::c_void,
                arg,
            ) > 0 as ::core::ffi::c_int
            {
                memcpy(
                    pr as *mut ::core::ffi::c_void,
                    pl as *const ::core::ffi::c_void,
                    es,
                );
                pr = pr.offset(-(es as isize));
                break;
            } else {
                pl = pl.offset(es as isize);
            }
        }
    }
    memcpy(
        pl as *mut ::core::ffi::c_void,
        pivot.as_mut_ptr() as *const ::core::ffi::c_void,
        es,
    );
    return 0 as size_t;
}
#[no_mangle]
pub unsafe extern "C" fn gca_qsort(
    mut base: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let mut b = base as *mut ::core::ffi::c_char;
    if nel < 6 as size_t {
        gca_isortr(base, 0 as size_t, nel, es, compar_id, arg);
    } else {
        let mut pivot = gca_median3(
            b as *mut ::core::ffi::c_void,
            b.offset(es.wrapping_mul(nel.wrapping_div(2 as size_t)) as isize)
                as *mut ::core::ffi::c_void,
            b.offset(es.wrapping_mul(nel.wrapping_sub(1 as size_t)) as isize)
                as *mut ::core::ffi::c_void,
            compar_id,
            arg,
        ) as *mut ::core::ffi::c_char;
        gca_swapm(b as *mut ::core::ffi::c_void, pivot as *mut ::core::ffi::c_void, es);
        let mut pidx = gca_qpart(b as *mut ::core::ffi::c_void, nel, es, compar_id, arg);
        gca_qsort(b as *mut ::core::ffi::c_void, pidx, es, compar_id, arg);
        gca_qsort(
            b.offset(es.wrapping_mul(pidx.wrapping_add(1 as size_t)) as isize)
                as *mut ::core::ffi::c_void,
            nel.wrapping_sub(pidx.wrapping_add(1 as size_t)),
            es,
            compar_id,
            arg,
        );
    };
}
#[no_mangle]
pub unsafe extern "C" fn gca_qselect(
    mut base: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut kidx: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) -> *mut ::core::ffi::c_void {
    let mut b = base as *mut ::core::ffi::c_char;
    let mut pidx: size_t = 0;
    let mut l: size_t = 0 as size_t;
    let mut r: size_t = nel.wrapping_sub(1 as size_t);
    if kidx < nel {} else {
        __assert_fail(
            b"kidx < nel\0" as *const u8 as *const ::core::ffi::c_char,
            b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
            250 as ::core::ffi::c_uint,
            __ASSERT_FUNCTION.as_ptr(),
        );
    }
    'c_4626: {
        if kidx < nel {} else {
            __assert_fail(
                b"kidx < nel\0" as *const u8 as *const ::core::ffi::c_char,
                b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                250 as ::core::ffi::c_uint,
                __ASSERT_FUNCTION.as_ptr(),
            );
        }
    };
    if nel <= 1 as size_t {
        return b as *mut ::core::ffi::c_void;
    }
    loop {
        let mut pivot = gca_median3(
            b.offset(es.wrapping_mul(l) as isize) as *mut ::core::ffi::c_void,
            b
                .offset(
                    es
                        .wrapping_mul(
                            l
                                .wrapping_add(
                                    r
                                        .wrapping_sub(l)
                                        .wrapping_add(1 as size_t)
                                        .wrapping_div(2 as size_t),
                                ),
                        ) as isize,
                ) as *mut ::core::ffi::c_void,
            b.offset(es.wrapping_mul(r) as isize) as *mut ::core::ffi::c_void,
            compar_id,
            arg,
        ) as *mut ::core::ffi::c_char;
        gca_swapm(
            b.offset(es.wrapping_mul(l) as isize) as *mut ::core::ffi::c_void,
            pivot as *mut ::core::ffi::c_void,
            es,
        );
        pidx = l
            .wrapping_add(
                gca_qpart(
                    b.offset(es.wrapping_mul(l) as isize) as *mut ::core::ffi::c_void,
                    r.wrapping_sub(l).wrapping_add(1 as size_t),
                    es,
                    compar_id,
                    arg,
                ),
            );
        if pidx > kidx {
            r = pidx.wrapping_sub(1 as size_t);
        } else {
            if !(pidx < kidx) {
                break;
            }
            l = pidx.wrapping_add(1 as size_t);
        }
    }
    return b.offset(es.wrapping_mul(kidx) as isize) as *mut ::core::ffi::c_void;
}
#[no_mangle]
pub unsafe extern "C" fn gca_heap_pushup(
    mut heap: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let mut chi: size_t = 0;
    let mut pi: size_t = 0;
    let vla = es as usize;
    let mut tmp: Vec<::core::ffi::c_char> = ::std::vec::from_elem(0, vla);
    let mut b = heap as *mut ::core::ffi::c_char;
    memcpy(
        tmp.as_mut_ptr() as *mut ::core::ffi::c_void,
        b.offset(es.wrapping_mul(nel.wrapping_sub(1 as size_t)) as isize)
            as *const ::core::ffi::c_void,
        es,
    );
    chi = nel.wrapping_sub(1 as size_t);
    while chi > 0 as size_t {
        pi = chi.wrapping_sub(1 as size_t).wrapping_div(2 as size_t);
        if call_compar(
            compar_id,
            b.offset(es.wrapping_mul(pi) as isize) as *const ::core::ffi::c_void,
            tmp.as_mut_ptr() as *const ::core::ffi::c_void,
            arg,
        ) >= 0 as ::core::ffi::c_int
        {
            break;
        }
        memcpy(
            b.offset(es.wrapping_mul(chi) as isize) as *mut ::core::ffi::c_void,
            b.offset(es.wrapping_mul(pi) as isize) as *const ::core::ffi::c_void,
            es,
        );
        chi = pi;
    }
    memcpy(
        b.offset(es.wrapping_mul(chi) as isize) as *mut ::core::ffi::c_void,
        tmp.as_mut_ptr() as *const ::core::ffi::c_void,
        es,
    );
}
#[no_mangle]
pub unsafe extern "C" fn gca_heap_pushdwn(
    mut heap: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let vla = es as usize;
    let mut tmp: Vec<::core::ffi::c_char> = ::std::vec::from_elem(0, vla);
    let mut b = heap as *mut ::core::ffi::c_char;
    let mut last = b.offset(es.wrapping_mul(nel.wrapping_sub(1 as size_t)) as isize);
    let mut p = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut ch = ::core::ptr::null_mut::<::core::ffi::c_char>();
    memcpy(
        tmp.as_mut_ptr() as *mut ::core::ffi::c_void,
        last as *const ::core::ffi::c_void,
        es,
    );
    p = b;
    ch = b.offset(es as isize);
    while ch < last {
        ch = if ch.offset(es as isize) < last
            && call_compar(
                compar_id,
                ch as *const ::core::ffi::c_void,
                ch.offset(es as isize) as *const ::core::ffi::c_void,
                arg,
            ) < 0 as ::core::ffi::c_int
        {
            ch.offset(es as isize)
        } else {
            ch
        };
        if call_compar(
            compar_id,
            tmp.as_mut_ptr() as *const ::core::ffi::c_void,
            ch as *const ::core::ffi::c_void,
            arg,
        ) >= 0 as ::core::ffi::c_int
        {
            break;
        }
        memcpy(p as *mut ::core::ffi::c_void, ch as *const ::core::ffi::c_void, es);
        p = ch;
        ch = ch.offset(es as isize);
    }
    memcpy(
        p as *mut ::core::ffi::c_void,
        tmp.as_mut_ptr() as *const ::core::ffi::c_void,
        es,
    );
}
#[no_mangle]
pub unsafe extern "C" fn gca_heap_make(
    mut heap: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    let mut n: size_t = 0;
    n = 2 as size_t;
    while n <= nel {
        gca_heap_pushup(heap, n, es, compar_id, arg);
        n = n.wrapping_add(1);
    }
}
#[no_mangle]
pub unsafe extern "C" fn gca_heap_sort(
    mut heap: *mut ::core::ffi::c_void,
    mut nel: size_t,
    mut es: size_t,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) {
    if nel <= 1 as size_t {
        return;
    }
    let mut b = heap as *mut ::core::ffi::c_char;
    let mut end = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut n: size_t = 0;
    n = nel.wrapping_sub(1 as size_t);
    end = b.offset(es.wrapping_mul(n) as isize);
    while n > 1 as size_t {
        gca_swapm(b as *mut ::core::ffi::c_void, end as *mut ::core::ffi::c_void, es);
        gca_heap_pushdwn(heap, n, es, compar_id, arg);
        n = n.wrapping_sub(1);
        end = end.offset(-(es as isize));
    }
    gca_swapm(
        b as *mut ::core::ffi::c_void,
        b.offset(es as isize) as *mut ::core::ffi::c_void,
        es,
    );
}
#[no_mangle]
pub unsafe extern "C" fn gca_median3(
    mut p0: *mut ::core::ffi::c_void,
    mut p1: *mut ::core::ffi::c_void,
    mut p2: *mut ::core::ffi::c_void,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) -> *mut ::core::ffi::c_void {
    if call_compar(compar_id, p0, p1, arg) > 0 as ::core::ffi::c_int {
        let mut _tmp = p0 as *mut ::core::ffi::c_void;
        p0 = p1;
        p1 = _tmp as *mut ::core::ffi::c_void;
    }
    if call_compar(compar_id, p1, p2, arg) > 0 as ::core::ffi::c_int {
        let mut _tmp_0 = p1 as *mut ::core::ffi::c_void;
        p1 = p2;
        p2 = _tmp_0 as *mut ::core::ffi::c_void;
        if call_compar(compar_id, p0, p1, arg) > 0 as ::core::ffi::c_int {
            let mut _tmp_1 = p0 as *mut ::core::ffi::c_void;
            p0 = p1;
            p1 = _tmp_1 as *mut ::core::ffi::c_void;
        }
    }
    return p1;
}
#[no_mangle]
pub unsafe extern "C" fn gca_median5(
    mut p0: *mut ::core::ffi::c_void,
    mut p1: *mut ::core::ffi::c_void,
    mut p2: *mut ::core::ffi::c_void,
    mut p3: *mut ::core::ffi::c_void,
    mut p4: *mut ::core::ffi::c_void,
    mut compar_id: ::core::ffi::c_int,
    mut arg: *mut ::core::ffi::c_void,
) -> *mut ::core::ffi::c_void {
    if call_compar(compar_id, p0, p1, arg) > 0 as ::core::ffi::c_int {
        let mut _tmp = p0 as *mut ::core::ffi::c_void;
        p0 = p1;
        p1 = _tmp as *mut ::core::ffi::c_void;
    }
    if call_compar(compar_id, p2, p3, arg) > 0 as ::core::ffi::c_int {
        let mut _tmp_0 = p2 as *mut ::core::ffi::c_void;
        p2 = p3;
        p3 = _tmp_0 as *mut ::core::ffi::c_void;
    }
    if call_compar(compar_id, p0, p2, arg) < 0 as ::core::ffi::c_int {
        p0 = p4;
        if call_compar(compar_id, p0, p1, arg) > 0 as ::core::ffi::c_int {
            let mut _tmp_1 = p0 as *mut ::core::ffi::c_void;
            p0 = p1;
            p1 = _tmp_1 as *mut ::core::ffi::c_void;
        }
    } else {
        p2 = p4;
        if call_compar(compar_id, p2, p3, arg) > 0 as ::core::ffi::c_int {
            let mut _tmp_2 = p2 as *mut ::core::ffi::c_void;
            p2 = p3;
            p3 = _tmp_2 as *mut ::core::ffi::c_void;
        }
    }
    if call_compar(compar_id, p0, p2, arg) < 0 as ::core::ffi::c_int {
        return if call_compar(compar_id, p1, p2, arg) < 0 as ::core::ffi::c_int {
            p1
        } else {
            p2
        }
    } else {
        return if call_compar(compar_id, p3, p0, arg) < 0 as ::core::ffi::c_int {
            p3
        } else {
            p0
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn gca_itr_reset(
    mut p: *mut size_t,
    mut n: size_t,
) -> *mut size_t {
    if p.is_null() {
        p = malloc(n.wrapping_mul(::core::mem::size_of::<size_t>() as size_t))
            as *mut size_t;
    }
    if !p.is_null() && n != 0 {
        *p.offset(0 as ::core::ffi::c_int as isize) = SIZE_MAX as size_t;
    }
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn gca_itr_next(
    mut pp: *mut *mut size_t,
    mut n: size_t,
    mut init: *mut size_t,
) -> *mut size_t {
    let mut i: size_t = 0;
    let mut j: size_t = 0;
    let mut p = *pp;
    if n == 0 {
        return ::core::ptr::null_mut::<size_t>();
    }
    if (*pp).is_null() {
        *pp = malloc(n.wrapping_mul(::core::mem::size_of::<size_t>() as size_t))
            as *mut size_t;
        p = *pp;
        *p.offset(0 as ::core::ffi::c_int as isize) = SIZE_MAX as size_t;
    }
    if *p.offset(0 as ::core::ffi::c_int as isize) == SIZE_MAX as size_t {
        if !init.is_null() {
            memcpy(
                p as *mut ::core::ffi::c_void,
                init as *const ::core::ffi::c_void,
                n.wrapping_mul(::core::mem::size_of::<size_t>() as size_t),
            );
        } else {
            i = 0 as size_t;
            while i < n {
                *p.offset(i as isize) = i;
                i = i.wrapping_add(1);
            }
        }
        return p;
    }
    i = n.wrapping_sub(1 as size_t);
    while i > 0 as size_t
        && *p.offset(i.wrapping_sub(1 as size_t) as isize) >= *p.offset(i as isize)
    {
        i = i.wrapping_sub(1);
    }
    if i == 0 {
        return ::core::ptr::null_mut::<size_t>();
    }
    j = i;
    while j.wrapping_add(1 as size_t) < n
        && *p.offset(i.wrapping_sub(1 as size_t) as isize)
            < *p.offset(j.wrapping_add(1 as size_t) as isize)
    {
        j = j.wrapping_add(1);
    }
    let mut _tmp: size_t = *p.offset(i.wrapping_sub(1 as size_t) as isize) as size_t;
    *p.offset(i.wrapping_sub(1 as size_t) as isize) = *p.offset(j as isize);
    *p.offset(j as isize) = _tmp as size_t;
    gca_reverse(
        p.offset(i as isize) as *mut ::core::ffi::c_void,
        n.wrapping_sub(i),
        ::core::mem::size_of::<size_t>() as size_t,
    );
    return p;
}
