//! bzip2 `blocksort` — the batch-7 stop (main 034): `fallbackSort` →
//! `fallbackQSort3` → `fallbackSimpleSort`, copied verbatim from the derived
//! substrate (c2rust-lib.rs 244–626) with the type aliases and externs the
//! three functions need. On the batch-7 composition `7dcffb1f` this program
//! fails `additive-family-preservation-invariant:unrestored:[(12, 2), (13, 2)]`
//! (the two `eclass#2`, the corpus's (137,2) / (138,2)); under `572eae87` both
//! `eclass` slices deliver.
pub(super) const BZIP2_BLOCKSORT: &str = r#"#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type Int32 = std::os::raw::c_int;
pub type UInt32 = std::os::raw::c_uint;
pub type UChar = std::os::raw::c_uchar;
#[repr(C)] pub struct FILE { _p: i32 }
extern "C" { fn fprintf(stream: *mut FILE, fmt: *const std::os::raw::c_char, ...) -> Int32; static mut __stderrp: *mut FILE; }
pub unsafe extern "C" fn BZ2_bz__AssertH__fail(mut errcode: Int32) { std::process::abort() }
    #[inline]
    unsafe extern "C" fn fallbackSimpleSort(mut fmap: *mut UInt32,
        mut eclass: *mut UInt32, mut lo: Int32, mut hi: Int32) {
        let mut i: Int32 = 0;
        let mut j: Int32 = 0;
        let mut tmp: Int32 = 0;
        let mut ec_tmp: UInt32 = 0;
        if lo == hi { return }
        if hi - lo > 3 as std::os::raw::c_int {
            i = hi - 4 as std::os::raw::c_int;
            while i >= lo {
                tmp = *fmap.offset(i as isize) as Int32;
                ec_tmp = *eclass.offset(tmp as isize);
                j = i + 4 as std::os::raw::c_int;
                while j <= hi &&
                        ec_tmp > *eclass.offset(*fmap.offset(j as isize) as isize) {
                    *fmap.offset((j - 4 as std::os::raw::c_int) as isize) =
                        *fmap.offset(j as isize);
                    j += 4 as std::os::raw::c_int
                }
                *fmap.offset((j - 4 as std::os::raw::c_int) as isize) =
                    tmp as UInt32;
                i -= 1
            }
        }
        i = hi - 1 as std::os::raw::c_int;
        while i >= lo {
            tmp = *fmap.offset(i as isize) as Int32;
            ec_tmp = *eclass.offset(tmp as isize);
            j = i + 1 as std::os::raw::c_int;
            while j <= hi &&
                    ec_tmp > *eclass.offset(*fmap.offset(j as isize) as isize) {
                *fmap.offset((j - 1 as std::os::raw::c_int) as isize) =
                    *fmap.offset(j as isize);
                j += 1
            }
            *fmap.offset((j - 1 as std::os::raw::c_int) as isize) =
                tmp as UInt32;
            i -= 1
        };
    }
    unsafe extern "C" fn fallbackQSort3(mut fmap: *mut UInt32,
        mut eclass: *mut UInt32, mut loSt: Int32, mut hiSt: Int32) {
        let mut unLo: Int32 = 0;
        let mut unHi: Int32 = 0;
        let mut ltLo: Int32 = 0;
        let mut gtHi: Int32 = 0;
        let mut n: Int32 = 0;
        let mut m: Int32 = 0;
        let mut sp: Int32 = 0;
        let mut lo: Int32 = 0;
        let mut hi: Int32 = 0;
        let mut med: UInt32 = 0;
        let mut r: UInt32 = 0;
        let mut r3: UInt32 = 0;
        let mut stackLo: [Int32; 100] = [0; 100];
        let mut stackHi: [Int32; 100] = [0; 100];
        r = 0 as std::os::raw::c_int as UInt32;
        sp = 0 as std::os::raw::c_int;
        stackLo[sp as usize] = loSt;
        stackHi[sp as usize] = hiSt;
        sp += 1;
        while sp > 0 as std::os::raw::c_int {
            if !(sp < 100 as std::os::raw::c_int - 1 as std::os::raw::c_int) {
                BZ2_bz__AssertH__fail(1004 as std::os::raw::c_int);
            }
            sp -= 1;
            lo = stackLo[sp as usize];
            hi = stackHi[sp as usize];
            if hi - lo < 10 as std::os::raw::c_int {
                fallbackSimpleSort(fmap, eclass, lo, hi);
            } else {
                r =
                    r.wrapping_mul(7621 as std::os::raw::c_int as
                                    std::os::raw::c_uint).wrapping_add(1 as std::os::raw::c_int
                                as
                                std::os::raw::c_uint).wrapping_rem(32768 as
                                std::os::raw::c_int as std::os::raw::c_uint);
                r3 =
                    r.wrapping_rem(3 as std::os::raw::c_int as
                            std::os::raw::c_uint);
                if r3 == 0 as std::os::raw::c_int as std::os::raw::c_uint {
                    med = *eclass.offset(*fmap.offset(lo as isize) as isize)
                } else if r3 ==
                        1 as std::os::raw::c_int as std::os::raw::c_uint {
                    med =
                        *eclass.offset(*fmap.offset((lo + hi >>
                                                        1 as std::os::raw::c_int) as isize) as isize)
                } else {
                    med = *eclass.offset(*fmap.offset(hi as isize) as isize)
                }
                ltLo = lo;
                unLo = ltLo;
                gtHi = hi;
                unHi = gtHi;
                loop {
                    while !(unLo > unHi) {
                        n =
                            *eclass.offset(*fmap.offset(unLo as isize) as isize) as
                                    Int32 - med as Int32;
                        if n == 0 as std::os::raw::c_int {
                            let mut zztmp: Int32 = *fmap.offset(unLo as isize) as Int32;
                            *fmap.offset(unLo as isize) = *fmap.offset(ltLo as isize);
                            *fmap.offset(ltLo as isize) = zztmp as UInt32;
                            ltLo += 1;
                            unLo += 1
                        } else {
                            if n > 0 as std::os::raw::c_int { break; }
                            unLo += 1
                        }
                    }
                    while !(unLo > unHi) {
                        n =
                            *eclass.offset(*fmap.offset(unHi as isize) as isize) as
                                    Int32 - med as Int32;
                        if n == 0 as std::os::raw::c_int {
                            let mut zztmp_0: Int32 =
                                *fmap.offset(unHi as isize) as Int32;
                            *fmap.offset(unHi as isize) = *fmap.offset(gtHi as isize);
                            *fmap.offset(gtHi as isize) = zztmp_0 as UInt32;
                            gtHi -= 1;
                            unHi -= 1
                        } else {
                            if n < 0 as std::os::raw::c_int { break; }
                            unHi -= 1
                        }
                    }
                    if unLo > unHi { break; }
                    let mut zztmp_1: Int32 =
                        *fmap.offset(unLo as isize) as Int32;
                    *fmap.offset(unLo as isize) = *fmap.offset(unHi as isize);
                    *fmap.offset(unHi as isize) = zztmp_1 as UInt32;
                    unLo += 1;
                    unHi -= 1
                }
                if gtHi < ltLo { continue; }
                n =
                    if ltLo - lo < unLo - ltLo {
                        (ltLo) - lo
                    } else { (unLo) - ltLo };
                let mut yyp1: Int32 = lo;
                let mut yyp2: Int32 = unLo - n;
                let mut yyn: Int32 = n;
                while yyn > 0 as std::os::raw::c_int {
                    let mut zztmp_2: Int32 =
                        *fmap.offset(yyp1 as isize) as Int32;
                    *fmap.offset(yyp1 as isize) = *fmap.offset(yyp2 as isize);
                    *fmap.offset(yyp2 as isize) = zztmp_2 as UInt32;
                    yyp1 += 1;
                    yyp2 += 1;
                    yyn -= 1
                }
                m =
                    if hi - gtHi < gtHi - unHi {
                        (hi) - gtHi
                    } else { (gtHi) - unHi };
                let mut yyp1_0: Int32 = unLo;
                let mut yyp2_0: Int32 = hi - m + 1 as std::os::raw::c_int;
                let mut yyn_0: Int32 = m;
                while yyn_0 > 0 as std::os::raw::c_int {
                    let mut zztmp_3: Int32 =
                        *fmap.offset(yyp1_0 as isize) as Int32;
                    *fmap.offset(yyp1_0 as isize) =
                        *fmap.offset(yyp2_0 as isize);
                    *fmap.offset(yyp2_0 as isize) = zztmp_3 as UInt32;
                    yyp1_0 += 1;
                    yyp2_0 += 1;
                    yyn_0 -= 1
                }
                n = lo + unLo - ltLo - 1 as std::os::raw::c_int;
                m = hi - (gtHi - unHi) + 1 as std::os::raw::c_int;
                if n - lo > hi - m {
                    stackLo[sp as usize] = lo;
                    stackHi[sp as usize] = n;
                    sp += 1;
                    stackLo[sp as usize] = m;
                    stackHi[sp as usize] = hi;
                    sp += 1
                } else {
                    stackLo[sp as usize] = m;
                    stackHi[sp as usize] = hi;
                    sp += 1;
                    stackLo[sp as usize] = lo;
                    stackHi[sp as usize] = n;
                    sp += 1
                }
            }
        };
    }
    unsafe extern "C" fn fallbackSort(mut fmap: *mut UInt32,
        mut eclass: *mut UInt32, mut bhtab: *mut UInt32, mut nblock: Int32,
        mut verb: Int32) {
        let mut ftab: [Int32; 257] = [0; 257];
        let mut ftabCopy: [Int32; 256] = [0; 256];
        let mut H: Int32 = 0;
        let mut i: Int32 = 0;
        let mut j: Int32 = 0;
        let mut k: Int32 = 0;
        let mut l: Int32 = 0;
        let mut r: Int32 = 0;
        let mut cc: Int32 = 0;
        let mut cc1: Int32 = 0;
        let mut nNotDone: Int32 = 0;
        let mut nBhtab: Int32 = 0;
        let mut eclass8: *mut UChar = eclass as *mut UChar;
        if verb >= 4 as std::os::raw::c_int {
            fprintf(__stderrp,
                b"        bucket sorting ...\n\x00" as *const u8 as
                    *const std::os::raw::c_char);
        }
        i = 0 as std::os::raw::c_int;
        while i < 257 as std::os::raw::c_int {
            ftab[i as usize] = 0 as std::os::raw::c_int;
            i += 1
        }
        i = 0 as std::os::raw::c_int;
        while i < nblock {
            ftab[*eclass8.offset(i as isize) as usize] += 1;
            i += 1
        }
        i = 0 as std::os::raw::c_int;
        while i < 256 as std::os::raw::c_int {
            ftabCopy[i as usize] = ftab[i as usize];
            i += 1
        }
        i = 1 as std::os::raw::c_int;
        while i < 257 as std::os::raw::c_int {
            ftab[i as usize] += ftab[(i - 1 as std::os::raw::c_int) as usize];
            i += 1
        }
        i = 0 as std::os::raw::c_int;
        while i < nblock {
            j = *eclass8.offset(i as isize) as Int32;
            k = ftab[j as usize] - 1 as std::os::raw::c_int;
            ftab[j as usize] = k;
            *fmap.offset(k as isize) = i as UInt32;
            i += 1
        }
        nBhtab =
            2 as std::os::raw::c_int + nblock / 32 as std::os::raw::c_int;
        i = 0 as std::os::raw::c_int;
        while i < nBhtab {
            *bhtab.offset(i as isize) = 0 as std::os::raw::c_int as UInt32;
            i += 1
        }
        i = 0 as std::os::raw::c_int;
        while i < 256 as std::os::raw::c_int {
            *bhtab.offset((ftab[i as usize] >> 5 as std::os::raw::c_int) as
                            isize) |=
                (1 as std::os::raw::c_int as UInt32) <<
                    (ftab[i as usize] & 31 as std::os::raw::c_int);
            i += 1
        }
        i = 0 as std::os::raw::c_int;
        while i < 32 as std::os::raw::c_int {
            *bhtab.offset((nblock + 2 as std::os::raw::c_int * i >>
                                    5 as std::os::raw::c_int) as isize) |=
                (1 as std::os::raw::c_int as UInt32) <<
                    (nblock + 2 as std::os::raw::c_int * i &
                            31 as std::os::raw::c_int);
            *bhtab.offset((nblock + 2 as std::os::raw::c_int * i +
                                        1 as std::os::raw::c_int >> 5 as std::os::raw::c_int) as
                            isize) &=
                !((1 as std::os::raw::c_int as UInt32) <<
                            (nblock + 2 as std::os::raw::c_int * i +
                                        1 as std::os::raw::c_int & 31 as std::os::raw::c_int));
            i += 1
        }
        H = 1 as std::os::raw::c_int;
        loop {
            if verb >= 4 as std::os::raw::c_int {
                fprintf(__stderrp,
                    b"        depth %6d has \x00" as *const u8 as
                        *const std::os::raw::c_char, H);
            }
            j = 0 as std::os::raw::c_int;
            i = 0 as std::os::raw::c_int;
            while i < nblock {
                if *bhtab.offset((i >> 5 as std::os::raw::c_int) as isize) &
                            (1 as std::os::raw::c_int as UInt32) <<
                                (i & 31 as std::os::raw::c_int) != 0 {
                    j = i
                }
                k =
                    (*fmap.offset(i as
                                            isize)).wrapping_sub(H as std::os::raw::c_uint) as Int32;
                if k < 0 as std::os::raw::c_int { k += nblock }
                *eclass.offset(k as isize) = j as UInt32;
                i += 1
            }
            nNotDone = 0 as std::os::raw::c_int;
            r = -(1 as std::os::raw::c_int);
            loop {
                k = r + 1 as std::os::raw::c_int;
                while *bhtab.offset((k >> 5 as std::os::raw::c_int) as isize)
                                &
                                (1 as std::os::raw::c_int as UInt32) <<
                                    (k & 31 as std::os::raw::c_int) != 0 &&
                        k & 0x1f as std::os::raw::c_int != 0 {
                    k += 1
                }
                if *bhtab.offset((k >> 5 as std::os::raw::c_int) as isize) &
                            (1 as std::os::raw::c_int as UInt32) <<
                                (k & 31 as std::os::raw::c_int) != 0 {
                    while *bhtab.offset((k >> 5 as std::os::raw::c_int) as
                                        isize) == 0xffffffff as std::os::raw::c_uint {
                        k += 32 as std::os::raw::c_int
                    }
                    while *bhtab.offset((k >> 5 as std::os::raw::c_int) as
                                            isize) &
                                (1 as std::os::raw::c_int as UInt32) <<
                                    (k & 31 as std::os::raw::c_int) != 0 {
                        k += 1
                    }
                }
                l = k - 1 as std::os::raw::c_int;
                if l >= nblock { break; }
                while *bhtab.offset((k >> 5 as std::os::raw::c_int) as isize)
                                &
                                (1 as std::os::raw::c_int as UInt32) <<
                                    (k & 31 as std::os::raw::c_int) == 0 &&
                        k & 0x1f as std::os::raw::c_int != 0 {
                    k += 1
                }
                if *bhtab.offset((k >> 5 as std::os::raw::c_int) as isize) &
                            (1 as std::os::raw::c_int as UInt32) <<
                                (k & 31 as std::os::raw::c_int) == 0 {
                    while *bhtab.offset((k >> 5 as std::os::raw::c_int) as
                                        isize) == 0 as std::os::raw::c_int as std::os::raw::c_uint {
                        k += 32 as std::os::raw::c_int
                    }
                    while *bhtab.offset((k >> 5 as std::os::raw::c_int) as
                                            isize) &
                                (1 as std::os::raw::c_int as UInt32) <<
                                    (k & 31 as std::os::raw::c_int) == 0 {
                        k += 1
                    }
                }
                r = k - 1 as std::os::raw::c_int;
                if r >= nblock { break; }
                if r > l {
                    nNotDone += r - l + 1 as std::os::raw::c_int;
                    fallbackQSort3(fmap, eclass, l, r);
                    cc = -(1 as std::os::raw::c_int);
                    i = l;
                    while i <= r {
                        cc1 =
                            *eclass.offset(*fmap.offset(i as isize) as isize) as Int32;
                        if cc != cc1 {
                            *bhtab.offset((i >> 5 as std::os::raw::c_int) as isize) |=
                                (1 as std::os::raw::c_int as UInt32) <<
                                    (i & 31 as std::os::raw::c_int);
                            cc = cc1
                        }
                        i += 1
                    }
                }
            }
            if verb >= 4 as std::os::raw::c_int {
                fprintf(__stderrp,
                    b"%6d unresolved strings\n\x00" as *const u8 as
                        *const std::os::raw::c_char, nNotDone);
            }
            H *= 2 as std::os::raw::c_int;
            if H > nblock || nNotDone == 0 as std::os::raw::c_int { break; }
        }
        if verb >= 4 as std::os::raw::c_int {
            fprintf(__stderrp,
                b"        reconstructing block ...\n\x00" as *const u8 as
                    *const std::os::raw::c_char);
        }
        j = 0 as std::os::raw::c_int;
        i = 0 as std::os::raw::c_int;
        while i < nblock {
            while ftabCopy[j as usize] == 0 as std::os::raw::c_int { j += 1 }
            ftabCopy[j as usize] -= 1;
            *eclass8.offset(*fmap.offset(i as isize) as isize) = j as UChar;
            i += 1
        }
        if !(j < 256 as std::os::raw::c_int) {
            BZ2_bz__AssertH__fail(1005 as std::os::raw::c_int);
        };
    }
"#;
