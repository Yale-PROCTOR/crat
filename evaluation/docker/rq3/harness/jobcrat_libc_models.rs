//! Harness-side C-library models for the Miri runs. Miri shims part of libc (malloc/free, memcpy, strlen, open /
//! read / write / close, ...). The functions below are the ones the corpus
//! calls that it does not model. Each is a specification implementation of
//! the C function, written against Miri-supported primitives (the `libc`
//! crate's read / write / open / lseek / close / malloc / free).
//!
//! They model the C library the input also uses; they are never part of the
//! emitted program, and the allocator line is never added here. Every model
//! is listed in `models.tsv` beside the census's receipts.
#![allow(non_upper_case_globals, clippy::missing_safety_doc, dead_code, unknown_lints, dangerous_implicit_autorefs)]

use core::ffi::{c_char, c_double, c_int, c_long, c_longlong, c_uint, c_ulong, c_ulonglong, c_void};

// ---------------------------------------------------------------- FILE
/// The model's FILE: a file descriptor with sticky EOF / error bits and one
/// pushed-back byte. Output is unbuffered (write(2) per call).
#[repr(C)]
pub struct CFile {
    fd: c_int,
    eof: bool,
    err: bool,
    unget: c_int,
    owned: bool,
}

static mut STDIN_F: CFile = CFile { fd: 0, eof: false, err: false, unget: -1, owned: false };
static mut STDOUT_F: CFile = CFile { fd: 1, eof: false, err: false, unget: -1, owned: false };
static mut STDERR_F: CFile = CFile { fd: 2, eof: false, err: false, unget: -1, owned: false };

#[no_mangle]
pub static mut stdin: *mut CFile = unsafe { &raw mut STDIN_F };
#[no_mangle]
pub static mut stdout: *mut CFile = unsafe { &raw mut STDOUT_F };
#[no_mangle]
pub static mut stderr: *mut CFile = unsafe { &raw mut STDERR_F };

unsafe fn write_all(fd: c_int, mut buf: &[u8]) -> bool {
    while !buf.is_empty() {
        let n = libc::write(fd, buf.as_ptr() as *const c_void, buf.len());
        if n <= 0 {
            return false;
        }
        buf = &buf[n as usize..];
    }
    true
}

unsafe fn file_write(f: *mut CFile, bytes: &[u8]) -> bool {
    if !write_all((*f).fd, bytes) {
        (*f).err = true;
        return false;
    }
    true
}

unsafe fn file_getc(f: *mut CFile) -> c_int {
    if (*f).unget >= 0 {
        let c = (*f).unget;
        (*f).unget = -1;
        return c;
    }
    let mut b = 0u8;
    let n = libc::read((*f).fd, &mut b as *mut u8 as *mut c_void, 1);
    if n == 1 {
        b as c_int
    } else {
        if n == 0 { (*f).eof = true } else { (*f).err = true }
        -1
    }
}

unsafe fn cstr<'a>(p: *const c_char) -> &'a [u8] {
    core::ffi::CStr::from_ptr(p).to_bytes()
}

#[no_mangle]
pub unsafe extern "C" fn fopen(path: *const c_char, mode: *const c_char) -> *mut CFile {
    let m = cstr(mode);
    let plus = m.contains(&b'+');
    let flags = match m.first() {
        Some(b'r') => if plus { libc::O_RDWR } else { libc::O_RDONLY },
        Some(b'w') => (if plus { libc::O_RDWR } else { libc::O_WRONLY }) | libc::O_CREAT | libc::O_TRUNC,
        Some(b'a') => (if plus { libc::O_RDWR } else { libc::O_WRONLY }) | libc::O_CREAT | libc::O_APPEND,
        _ => return core::ptr::null_mut(),
    };
    let fd = libc::open(path, flags, 0o644 as c_uint);
    if fd < 0 {
        return core::ptr::null_mut();
    }
    Box::into_raw(Box::new(CFile { fd, eof: false, err: false, unget: -1, owned: true }))
}

#[no_mangle]
pub unsafe extern "C" fn fdopen(fd: c_int, _mode: *const c_char) -> *mut CFile {
    Box::into_raw(Box::new(CFile { fd, eof: false, err: false, unget: -1, owned: true }))
}

#[no_mangle]
pub unsafe extern "C" fn fclose(f: *mut CFile) -> c_int {
    let r = libc::close((*f).fd);
    if (*f).owned {
        drop(Box::from_raw(f));
    }
    if r == 0 { 0 } else { -1 }
}

#[no_mangle]
pub unsafe extern "C" fn fflush(_f: *mut CFile) -> c_int { 0 }

#[no_mangle]
pub unsafe extern "C" fn fileno(f: *mut CFile) -> c_int { (*f).fd }

#[no_mangle]
pub unsafe extern "C" fn feof(f: *mut CFile) -> c_int { (*f).eof as c_int }

#[no_mangle]
pub unsafe extern "C" fn ferror(f: *mut CFile) -> c_int { (*f).err as c_int }

#[no_mangle]
pub unsafe extern "C" fn fread(ptr: *mut c_void, size: c_ulong, n: c_ulong, f: *mut CFile) -> c_ulong {
    let total = (size * n) as usize;
    if total == 0 {
        return 0;
    }
    let buf = core::slice::from_raw_parts_mut(ptr as *mut u8, total);
    let mut got = 0usize;
    if (*f).unget >= 0 {
        buf[0] = (*f).unget as u8;
        (*f).unget = -1;
        got = 1;
    }
    while got < total {
        let r = libc::read((*f).fd, buf[got..].as_mut_ptr() as *mut c_void, total - got);
        if r <= 0 {
            if r == 0 { (*f).eof = true } else { (*f).err = true }
            break;
        }
        got += r as usize;
    }
    (got / size as usize) as c_ulong
}

#[no_mangle]
pub unsafe extern "C" fn fwrite(ptr: *const c_void, size: c_ulong, n: c_ulong, f: *mut CFile) -> c_ulong {
    let total = (size * n) as usize;
    if total == 0 {
        return 0;
    }
    if file_write(f, core::slice::from_raw_parts(ptr as *const u8, total)) { n } else { 0 }
}

#[no_mangle]
pub unsafe extern "C" fn fgetc(f: *mut CFile) -> c_int { file_getc(f) }
#[no_mangle]
pub unsafe extern "C" fn getc(f: *mut CFile) -> c_int { file_getc(f) }
#[no_mangle]
pub unsafe extern "C" fn _IO_getc(f: *mut CFile) -> c_int { file_getc(f) }

#[no_mangle]
pub unsafe extern "C" fn ungetc(c: c_int, f: *mut CFile) -> c_int {
    if c < 0 {
        return -1;
    }
    (*f).unget = c & 0xff;
    (*f).eof = false;
    c & 0xff
}

#[no_mangle]
pub unsafe extern "C" fn fgets(s: *mut c_char, n: c_int, f: *mut CFile) -> *mut c_char {
    if n <= 0 {
        return core::ptr::null_mut();
    }
    let mut i = 0isize;
    while (i as c_int) < n - 1 {
        let c = file_getc(f);
        if c < 0 {
            break;
        }
        *s.offset(i) = c as c_char;
        i += 1;
        if c == b'\n' as c_int {
            break;
        }
    }
    if i == 0 {
        return core::ptr::null_mut();
    }
    *s.offset(i) = 0;
    s
}

#[no_mangle]
pub unsafe extern "C" fn fputc(c: c_int, f: *mut CFile) -> c_int {
    if file_write(f, &[c as u8]) { c & 0xff } else { -1 }
}
#[no_mangle]
pub unsafe extern "C" fn putc(c: c_int, f: *mut CFile) -> c_int { fputc(c, f) }
#[no_mangle]
pub unsafe extern "C" fn _IO_putc(c: c_int, f: *mut CFile) -> c_int { fputc(c, f) }
#[no_mangle]
pub unsafe extern "C" fn putchar(c: c_int) -> c_int { fputc(c, stdout) }

#[no_mangle]
pub unsafe extern "C" fn fputs(s: *const c_char, f: *mut CFile) -> c_int {
    if file_write(f, cstr(s)) { 1 } else { -1 }
}

#[no_mangle]
pub unsafe extern "C" fn puts(s: *const c_char) -> c_int {
    if file_write(stdout, cstr(s)) && file_write(stdout, b"\n") { 1 } else { -1 }
}

#[no_mangle]
pub unsafe extern "C" fn fseek(f: *mut CFile, off: c_long, whence: c_int) -> c_int {
    (*f).unget = -1;
    (*f).eof = false;
    if libc::lseek((*f).fd, off as libc::off_t, whence) < 0 { -1 } else { 0 }
}

#[no_mangle]
pub unsafe extern "C" fn ftell(f: *mut CFile) -> c_long {
    let p = libc::lseek((*f).fd, 0, libc::SEEK_CUR) as c_long;
    if (*f).unget >= 0 { p - 1 } else { p }
}

#[no_mangle]
pub unsafe extern "C" fn rewind(f: *mut CFile) {
    fseek(f, 0, libc::SEEK_SET);
    (*f).err = false;
}

// ---------------------------------------------------------------- printf
/// The next C-variadic argument, as the conversion's length modifier reads it.
enum Len { Hh, H, None, L, Ll, Z, J, T, BigL }

unsafe fn format(fmt: *const c_char, ap: &mut core::ffi::VaList<'_>) -> Vec<u8> {
    let f = cstr(fmt);
    let mut out = Vec::new();
    let mut i = 0;
    while i < f.len() {
        if f[i] != b'%' {
            out.push(f[i]);
            i += 1;
            continue;
        }
        i += 1;
        if i < f.len() && f[i] == b'%' {
            out.push(b'%');
            i += 1;
            continue;
        }
        let (mut left, mut plus, mut space, mut alt, mut zero) = (false, false, false, false, false);
        while i < f.len() {
            match f[i] {
                b'-' => left = true,
                b'+' => plus = true,
                b' ' => space = true,
                b'#' => alt = true,
                b'0' => zero = true,
                _ => break,
            }
            i += 1;
        }
        let mut width: Option<usize> = None;
        if i < f.len() && f[i] == b'*' {
            let w: c_int = ap.next_arg();
            if w < 0 { left = true; width = Some((-w) as usize) } else { width = Some(w as usize) }
            i += 1;
        } else {
            let mut w = 0usize;
            let mut any = false;
            while i < f.len() && f[i].is_ascii_digit() { w = w * 10 + (f[i] - b'0') as usize; i += 1; any = true; }
            if any { width = Some(w) }
        }
        let mut prec: Option<usize> = None;
        if i < f.len() && f[i] == b'.' {
            i += 1;
            if i < f.len() && f[i] == b'*' {
                let p: c_int = ap.next_arg();
                prec = if p < 0 { None } else { Some(p as usize) };
                i += 1;
            } else {
                let mut p = 0usize;
                while i < f.len() && f[i].is_ascii_digit() { p = p * 10 + (f[i] - b'0') as usize; i += 1; }
                prec = Some(p);
            }
        }
        let len = if f[i..].starts_with(b"hh") { i += 2; Len::Hh }
            else if f[i..].starts_with(b"ll") { i += 2; Len::Ll }
            else { match f.get(i) {
                Some(b'h') => { i += 1; Len::H }
                Some(b'l') => { i += 1; Len::L }
                Some(b'z') => { i += 1; Len::Z }
                Some(b'j') => { i += 1; Len::J }
                Some(b't') => { i += 1; Len::T }
                Some(b'L') => { i += 1; Len::BigL }
                _ => Len::None,
            } };
        let conv = f[i];
        i += 1;
        let mut body: Vec<u8>;
        let mut sign: &[u8] = b"";
        let mut prefix: &[u8] = b"";
        let mut numeric = true;
        match conv {
            b'd' | b'i' => {
                let v: i64 = match len {
                    Len::Hh => ap.next_arg::<c_int>() as i8 as i64,
                    Len::H => ap.next_arg::<c_int>() as i16 as i64,
                    Len::L | Len::Ll | Len::Z | Len::J | Len::T => ap.next_arg::<c_longlong>(),
                    _ => ap.next_arg::<c_int>() as i64,
                };
                if v < 0 { sign = b"-" } else if plus { sign = b"+" } else if space { sign = b" " }
                body = v.unsigned_abs().to_string().into_bytes();
                if let Some(p) = prec { if p == 0 && v == 0 { body.clear() } while body.len() < p { body.insert(0, b'0') } }
            }
            b'u' | b'x' | b'X' | b'o' => {
                let v: u64 = match len {
                    Len::Hh => ap.next_arg::<c_uint>() as u8 as u64,
                    Len::H => ap.next_arg::<c_uint>() as u16 as u64,
                    Len::L | Len::Ll | Len::Z | Len::J | Len::T => ap.next_arg::<c_ulonglong>(),
                    _ => ap.next_arg::<c_uint>() as u64,
                };
                body = match conv {
                    b'u' => v.to_string(),
                    b'x' => format!("{v:x}"),
                    b'X' => format!("{v:X}"),
                    _ => format!("{v:o}"),
                }.into_bytes();
                if let Some(p) = prec { if p == 0 && v == 0 { body.clear() } while body.len() < p { body.insert(0, b'0') } }
                if alt && v != 0 {
                    match conv { b'x' => prefix = b"0x", b'X' => prefix = b"0X", b'o' if body.first() != Some(&b'0') => body.insert(0, b'0'), _ => {} }
                }
            }
            b'c' => {
                numeric = false;
                body = vec![ap.next_arg::<c_int>() as u8];
            }
            b's' => {
                numeric = false;
                let p: *const c_char = ap.next_arg();
                let s: &[u8] = if p.is_null() { b"(null)" } else { cstr(p) };
                body = match prec { Some(n) if n < s.len() => s[..n].to_vec(), _ => s.to_vec() };
            }
            b'p' => {
                numeric = false;
                let p: *const c_void = ap.next_arg();
                body = if p.is_null() { b"(nil)".to_vec() } else { format!("0x{:x}", p as usize).into_bytes() };
            }
            b'n' => {
                let p: *mut c_int = ap.next_arg();
                *p = out.len() as c_int;
                continue;
            }
            b'f' | b'F' | b'e' | b'E' | b'g' | b'G' | b'a' | b'A' => {
                let v: c_double = if matches!(len, Len::BigL) { ap.next_arg::<c_double>() } else { ap.next_arg::<c_double>() };
                if v.is_sign_negative() && !(v.is_nan()) { sign = b"-" } else if plus { sign = b"+" } else if space { sign = b" " }
                body = float(v.abs(), conv, prec.unwrap_or(6), alt).into_bytes();
                if !v.is_finite() { zero = false }
            }
            _ => { numeric = false; body = vec![b'%', conv]; }
        }
        let content = sign.len() + prefix.len() + body.len();
        let pad = width.unwrap_or(0).saturating_sub(content);
        let zero_pad = zero && !left && numeric && (prec.is_none() || matches!(conv, b'f' | b'F' | b'e' | b'E' | b'g' | b'G'));
        if !left && !zero_pad { out.extend(std::iter::repeat_n(b' ', pad)) }
        out.extend_from_slice(sign);
        out.extend_from_slice(prefix);
        if zero_pad { out.extend(std::iter::repeat_n(b'0', pad)) }
        out.extend_from_slice(&body);
        if left { out.extend(std::iter::repeat_n(b' ', pad)) }
    }
    out
}

/// C's %f / %e / %g of a non-negative value (the sign is handled by the caller).
fn float(v: f64, conv: u8, prec: usize, alt: bool) -> String {
    let upper = conv.is_ascii_uppercase();
    if v.is_nan() { return if upper { "NAN".into() } else { "nan".into() } }
    if v.is_infinite() { return if upper { "INF".into() } else { "inf".into() } }
    let s = match conv.to_ascii_lowercase() {
        b'f' => { let s = format!("{:.*}", prec, v); if alt && prec == 0 { s + "." } else { s } }
        b'e' => exp_form(v, prec, alt),
        b'g' => {
            let p = if prec == 0 { 1 } else { prec };
            let e = exp_form(v, p - 1, false);
            let x: i32 = e[e.find('e').unwrap() + 1..].parse().unwrap();
            let mut s = if (x as i64) < p as i64 && x >= -4 {
                format!("{:.*}", (p as i64 - 1 - x as i64) as usize, v)
            } else { e };
            if !alt {
                if let Some(epos) = s.find('e') {
                    let (m, ex) = s.split_at(epos);
                    let m = if m.contains('.') { m.trim_end_matches('0').trim_end_matches('.') } else { m };
                    s = format!("{m}{ex}");
                } else if s.contains('.') {
                    s = s.trim_end_matches('0').trim_end_matches('.').to_string();
                }
            }
            s
        }
        _ => format!("{v:e}"),
    };
    if upper { s.to_uppercase() } else { s }
}

fn exp_form(v: f64, prec: usize, alt: bool) -> String {
    let s = format!("{:.*e}", prec, v);
    let (m, e) = s.split_at(s.find('e').unwrap());
    let x: i32 = e[1..].parse().unwrap();
    let m = if alt && prec == 0 { format!("{m}.") } else { m.to_string() };
    format!("{m}e{}{:02}", if x < 0 { '-' } else { '+' }, x.abs())
}

#[no_mangle]
pub unsafe extern "C" fn printf(fmt: *const c_char, mut args: ...) -> c_int {
    let b = format(fmt, &mut args);
    if file_write(stdout, &b) { b.len() as c_int } else { -1 }
}

#[no_mangle]
pub unsafe extern "C" fn fprintf(f: *mut CFile, fmt: *const c_char, mut args: ...) -> c_int {
    let b = format(fmt, &mut args);
    if file_write(f, &b) { b.len() as c_int } else { -1 }
}

#[no_mangle]
pub unsafe extern "C" fn sprintf(s: *mut c_char, fmt: *const c_char, mut args: ...) -> c_int {
    let b = format(fmt, &mut args);
    core::ptr::copy_nonoverlapping(b.as_ptr(), s as *mut u8, b.len());
    *s.add(b.len()) = 0;
    b.len() as c_int
}

unsafe fn bounded(s: *mut c_char, n: c_ulong, b: &[u8]) -> c_int {
    if n > 0 {
        let k = b.len().min(n as usize - 1);
        core::ptr::copy_nonoverlapping(b.as_ptr(), s as *mut u8, k);
        *s.add(k) = 0;
    }
    b.len() as c_int
}

#[no_mangle]
pub unsafe extern "C" fn snprintf(s: *mut c_char, n: c_ulong, fmt: *const c_char, mut args: ...) -> c_int {
    let b = format(fmt, &mut args);
    bounded(s, n, &b)
}

#[no_mangle]
pub unsafe extern "C" fn vsnprintf(s: *mut c_char, n: c_ulong, fmt: *const c_char, mut ap: core::ffi::VaList<'_>) -> c_int {
    let b = format(fmt, &mut ap);
    bounded(s, n, &b)
}

#[no_mangle]
pub unsafe extern "C" fn perror(s: *const c_char) {
    let e = *libc::__errno_location();
    let msg = std::io::Error::from_raw_os_error(e).to_string();
    let mut b = Vec::new();
    if !s.is_null() && *s != 0 { b.extend_from_slice(cstr(s)); b.extend_from_slice(b": "); }
    b.extend_from_slice(msg.split(" (os error").next().unwrap_or("").as_bytes());
    b.push(b'\n');
    file_write(stderr, &b);
}

// ---------------------------------------------------------------- scanf
unsafe fn scan(input: &mut dyn FnMut(bool) -> c_int, fmt: *const c_char, ap: &mut core::ffi::VaList<'_>) -> c_int {
    // input(false) peeks, input(true) consumes; -1 at end.
    let f = cstr(fmt);
    let mut i = 0;
    let mut assigned = 0;
    let mut consumed = 0usize;
    let mut any_input = false;
    while i < f.len() {
        let c = f[i];
        if c.is_ascii_whitespace() {
            while input(false) >= 0 && (input(false) as u8).is_ascii_whitespace() { input(true); consumed += 1; }
            i += 1;
            continue;
        }
        if c != b'%' {
            if input(false) != c as c_int { break }
            input(true); consumed += 1; i += 1;
            continue;
        }
        i += 1;
        if f[i] == b'%' {
            if input(false) != b'%' as c_int { break }
            input(true); consumed += 1; i += 1;
            continue;
        }
        let suppress = f[i] == b'*';
        if suppress { i += 1 }
        let mut width = 0usize;
        while f[i].is_ascii_digit() { width = width * 10 + (f[i] - b'0') as usize; i += 1; }
        let mut longs = 0;
        let mut short = 0;
        loop { match f[i] { b'l' => { longs += 1; i += 1 } b'h' => { short += 1; i += 1 } b'z' | b'j' | b't' | b'L' => { longs = 2; i += 1 } _ => break } }
        let conv = f[i];
        i += 1;
        if conv != b'c' && conv != b'[' && conv != b'n' {
            while input(false) >= 0 && (input(false) as u8).is_ascii_whitespace() { input(true); consumed += 1; }
        }
        if conv == b'n' {
            if !suppress { let p: *mut c_int = ap.next_arg(); *p = consumed as c_int; }
            continue;
        }
        if input(false) < 0 { if !any_input { return -1 } break }
        let maxw = if width == 0 { usize::MAX } else { width };
        let mut tok = Vec::new();
        match conv {
            b'c' => {
                let n = if width == 0 { 1 } else { width };
                while tok.len() < n && input(false) >= 0 { tok.push(input(true) as u8) }
                consumed += tok.len();
                if !suppress { let p: *mut c_char = ap.next_arg(); core::ptr::copy_nonoverlapping(tok.as_ptr(), p as *mut u8, tok.len()); assigned += 1; }
            }
            b's' => {
                while tok.len() < maxw && input(false) >= 0 && !(input(false) as u8).is_ascii_whitespace() { tok.push(input(true) as u8) }
                consumed += tok.len();
                if tok.is_empty() { break }
                if !suppress { let p: *mut c_char = ap.next_arg(); core::ptr::copy_nonoverlapping(tok.as_ptr(), p as *mut u8, tok.len()); *p.add(tok.len()) = 0; assigned += 1; }
            }
            b'[' => {
                let neg = f[i] == b'^';
                if neg { i += 1 }
                let start = i;
                if f[i] == b']' { i += 1 }
                while f[i] != b']' { i += 1 }
                let set = &f[start..i];
                i += 1;
                let inset = |b: u8| { let mut k = 0; let mut hit = false; while k < set.len() { if k + 2 < set.len() && set[k + 1] == b'-' { if set[k] <= b && b <= set[k + 2] { hit = true } k += 3 } else { if set[k] == b { hit = true } k += 1 } } hit != neg };
                while tok.len() < maxw && input(false) >= 0 && inset(input(false) as u8) { tok.push(input(true) as u8) }
                consumed += tok.len();
                if tok.is_empty() { break }
                if !suppress { let p: *mut c_char = ap.next_arg(); core::ptr::copy_nonoverlapping(tok.as_ptr(), p as *mut u8, tok.len()); *p.add(tok.len()) = 0; assigned += 1; }
            }
            b'd' | b'i' | b'u' | b'x' | b'X' | b'o' => {
                let base = match conv { b'x' | b'X' => 16, b'o' => 8, _ => 10 };
                if tok.len() < maxw && matches!(input(false), 43 | 45) { tok.push(input(true) as u8) }
                while tok.len() < maxw && input(false) >= 0 && (input(false) as u8 as char).is_digit(base) { tok.push(input(true) as u8) }
                consumed += tok.len();
                let digits = std::str::from_utf8(&tok).unwrap_or("");
                let v = i128::from_str_radix(digits.trim_start_matches('+'), base);
                let Ok(v) = v else { break };
                if !suppress {
                    if longs > 0 { let p: *mut c_longlong = ap.next_arg(); if longs == 1 { *(p as *mut c_long) = v as c_long } else { *p = v as c_longlong } }
                    else if short == 1 { let p: *mut i16 = ap.next_arg(); *p = v as i16 }
                    else if short >= 2 { let p: *mut i8 = ap.next_arg(); *p = v as i8 }
                    else { let p: *mut c_int = ap.next_arg(); *p = v as c_int }
                    assigned += 1;
                }
            }
            b'f' | b'e' | b'g' | b'E' | b'G' | b'a' => {
                while tok.len() < maxw && input(false) >= 0 && matches!(input(false) as u8, b'0'..=b'9' | b'.' | b'e' | b'E' | b'+' | b'-' | b'x' | b'X' | b'a'..=b'f' | b'A'..=b'F' | b'n' | b'i') { tok.push(input(true) as u8) }
                consumed += tok.len();
                let Ok(v) = std::str::from_utf8(&tok).unwrap_or("").parse::<f64>() else { break };
                if !suppress {
                    if longs > 0 { let p: *mut c_double = ap.next_arg(); *p = v } else { let p: *mut f32 = ap.next_arg(); *p = v as f32 }
                    assigned += 1;
                }
            }
            _ => break,
        }
        any_input = true;
    }
    assigned
}

#[no_mangle]
pub unsafe extern "C" fn sscanf(s: *const c_char, fmt: *const c_char, mut args: ...) -> c_int {
    let b = cstr(s);
    let mut pos = 0usize;
    let mut input = |take: bool| -> c_int { if pos < b.len() { let c = b[pos] as c_int; if take { pos += 1 } c } else { -1 } };
    scan(&mut input, fmt, &mut args)
}

#[no_mangle]
pub unsafe extern "C" fn fscanf(f: *mut CFile, fmt: *const c_char, mut args: ...) -> c_int {
    let mut input = |take: bool| -> c_int {
        let c = file_getc(f);
        if !take && c >= 0 { (*f).unget = c }
        c
    };
    scan(&mut input, fmt, &mut args)
}

// ---------------------------------------------------------------- string
#[no_mangle]
pub unsafe extern "C" fn strcmp(a: *const c_char, b: *const c_char) -> c_int {
    let (a, b) = (cstr(a), cstr(b));
    for k in 0.. {
        let (x, y) = (*a.get(k).unwrap_or(&0), *b.get(k).unwrap_or(&0));
        if x != y || x == 0 { return x as c_int - y as c_int }
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn strncmp(a: *const c_char, b: *const c_char, n: c_ulong) -> c_int {
    for k in 0..n as usize {
        let (x, y) = (*a.add(k) as u8, *b.add(k) as u8);
        if x != y || x == 0 { return x as c_int - y as c_int }
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn strcasecmp(a: *const c_char, b: *const c_char) -> c_int {
    let mut k = 0;
    loop {
        let (x, y) = ((*a.add(k) as u8).to_ascii_lowercase(), (*b.add(k) as u8).to_ascii_lowercase());
        if x != y || x == 0 { return x as c_int - y as c_int }
        k += 1;
    }
}

#[no_mangle]
pub unsafe extern "C" fn strncasecmp(a: *const c_char, b: *const c_char, n: c_ulong) -> c_int {
    for k in 0..n as usize {
        let (x, y) = ((*a.add(k) as u8).to_ascii_lowercase(), (*b.add(k) as u8).to_ascii_lowercase());
        if x != y || x == 0 { return x as c_int - y as c_int }
    }
    0
}

// strcpy: Miri's built-in shim (a model here would clash with it)
unsafe fn strcpy(d: *mut c_char, s: *const c_char) -> *mut c_char {
    let n = cstr(s).len();
    core::ptr::copy_nonoverlapping(s, d, n + 1);
    d
}

#[no_mangle]
pub unsafe extern "C" fn strncpy(d: *mut c_char, s: *const c_char, n: c_ulong) -> *mut c_char {
    let mut k = 0usize;
    while k < n as usize && *s.add(k) != 0 { *d.add(k) = *s.add(k); k += 1 }
    while k < n as usize { *d.add(k) = 0; k += 1 }
    d
}

#[no_mangle]
pub unsafe extern "C" fn strcat(d: *mut c_char, s: *const c_char) -> *mut c_char {
    strcpy(d.add(cstr(d).len()), s);
    d
}

#[no_mangle]
pub unsafe extern "C" fn strncat(d: *mut c_char, s: *const c_char, n: c_ulong) -> *mut c_char {
    let end = d.add(cstr(d).len());
    let mut k = 0usize;
    while k < n as usize && *s.add(k) != 0 { *end.add(k) = *s.add(k); k += 1 }
    *end.add(k) = 0;
    d
}

#[no_mangle]
pub unsafe extern "C" fn strchr(s: *const c_char, c: c_int) -> *mut c_char {
    let mut p = s;
    loop {
        if *p as u8 == c as u8 { return p as *mut c_char }
        if *p == 0 { return core::ptr::null_mut() }
        p = p.add(1);
    }
}

#[no_mangle]
pub unsafe extern "C" fn strrchr(s: *const c_char, c: c_int) -> *mut c_char {
    let mut last = core::ptr::null_mut();
    let mut p = s;
    loop {
        if *p as u8 == c as u8 { last = p as *mut c_char }
        if *p == 0 { return last }
        p = p.add(1);
    }
}

#[no_mangle]
pub unsafe extern "C" fn strstr(h: *const c_char, n: *const c_char) -> *mut c_char {
    let (hb, nb) = (cstr(h), cstr(n));
    if nb.is_empty() { return h as *mut c_char }
    match hb.windows(nb.len()).position(|w| w == nb) {
        Some(k) => h.add(k) as *mut c_char,
        None => core::ptr::null_mut(),
    }
}

#[no_mangle]
pub unsafe extern "C" fn strdup(s: *const c_char) -> *mut c_char {
    let n = cstr(s).len();
    let d = libc::malloc(n + 1) as *mut c_char;
    if !d.is_null() { core::ptr::copy_nonoverlapping(s, d, n + 1) }
    d
}

static mut STRTOK_NEXT: *mut c_char = core::ptr::null_mut();

#[no_mangle]
pub unsafe extern "C" fn strtok(s: *mut c_char, delim: *const c_char) -> *mut c_char {
    let d = cstr(delim);
    let mut p = if s.is_null() { STRTOK_NEXT } else { s };
    if p.is_null() { return p }
    while *p != 0 && d.contains(&(*p as u8)) { p = p.add(1) }
    if *p == 0 { STRTOK_NEXT = core::ptr::null_mut(); return core::ptr::null_mut() }
    let tok = p;
    while *p != 0 && !d.contains(&(*p as u8)) { p = p.add(1) }
    if *p != 0 { *p = 0; STRTOK_NEXT = p.add(1) } else { STRTOK_NEXT = core::ptr::null_mut() }
    tok
}

#[no_mangle]
pub unsafe extern "C" fn strerror(e: c_int) -> *mut c_char {
    static mut BUF: [u8; 128] = [0; 128];
    let m = std::io::Error::from_raw_os_error(e).to_string();
    let m = m.split(" (os error").next().unwrap_or("").as_bytes();
    let n = m.len().min(127);
    let buf = &raw mut BUF;
    (*buf)[..n].copy_from_slice(&m[..n]);
    (*buf)[n] = 0;
    buf as *mut c_char
}

// ---------------------------------------------------------------- numbers
unsafe fn parse_int(s: *const c_char, end: *mut *mut c_char, base: c_int) -> (i128, bool) {
    let b = cstr(s);
    let mut k = 0;
    while k < b.len() && b[k].is_ascii_whitespace() { k += 1 }
    let neg = k < b.len() && b[k] == b'-';
    if k < b.len() && (b[k] == b'-' || b[k] == b'+') { k += 1 }
    let mut base = base as u32;
    if (base == 0 || base == 16) && b[k..].starts_with(b"0x") || b[k..].starts_with(b"0X") && (base == 0 || base == 16) { k += 2; base = 16 }
    else if base == 0 && b.get(k) == Some(&b'0') { base = 8 }
    else if base == 0 { base = 10 }
    let start = k;
    let mut v: i128 = 0;
    while k < b.len() && (b[k] as char).is_digit(base) { v = v.saturating_mul(base as i128).saturating_add((b[k] as char).to_digit(base).unwrap() as i128); k += 1 }
    if !end.is_null() { *end = (if k == start { s } else { s.add(k) }) as *mut c_char }
    (if neg { -v } else { v }, k != start)
}

#[no_mangle]
pub unsafe extern "C" fn strtol(s: *const c_char, end: *mut *mut c_char, base: c_int) -> c_long {
    let (v, _) = parse_int(s, end, base);
    v.clamp(c_long::MIN as i128, c_long::MAX as i128) as c_long
}
#[no_mangle]
pub unsafe extern "C" fn strtoul(s: *const c_char, end: *mut *mut c_char, base: c_int) -> c_ulong {
    parse_int(s, end, base).0 as c_ulong
}
#[no_mangle]
pub unsafe extern "C" fn strtoumax(s: *const c_char, end: *mut *mut c_char, base: c_int) -> u64 {
    parse_int(s, end, base).0 as u64
}
#[no_mangle]
pub unsafe extern "C" fn atoi(s: *const c_char) -> c_int { parse_int(s, core::ptr::null_mut(), 10).0 as c_int }
#[no_mangle]
pub unsafe extern "C" fn atoll(s: *const c_char) -> c_longlong { parse_int(s, core::ptr::null_mut(), 10).0 as c_longlong }

#[no_mangle]
pub unsafe extern "C" fn atof(s: *const c_char) -> c_double {
    let b = cstr(s);
    let t = std::str::from_utf8(b).unwrap_or("").trim_start();
    let mut end = 0;
    for k in 1..=t.len() { if t[..k].parse::<f64>().is_ok() || t[..k] == *"-" || t[..k] == *"+" || t[..k] == *"." || t[..k].ends_with('e') || t[..k].ends_with('E') || t[..k].ends_with("e-") || t[..k].ends_with("e+") { end = k } else { break } }
    let mut v = 0.0;
    for k in (1..=end).rev() { if let Ok(x) = t[..k].parse::<f64>() { v = x; break } }
    v
}

#[no_mangle]
pub unsafe extern "C" fn abs(x: c_int) -> c_int { x.wrapping_abs() }

// rand: glibc's TYPE_3 additive generator (random_r), so sequences match the C build
static mut RSTATE: [i32; 34] = [0; 34];
static mut RIDX: usize = 0;
static mut RSEEDED: bool = false;

#[no_mangle]
pub unsafe extern "C" fn srand(seed: c_uint) {
    let r = &raw mut RSTATE;
    let r = &mut *r;
    r[0] = if seed == 0 { 1 } else { seed as i32 };
    for k in 1..31 {
        let hi = (r[k - 1] as i64) / 127773;
        let lo = (r[k - 1] as i64) % 127773;
        let mut w = 16807 * lo - 2836 * hi;
        if w < 0 { w += 2147483647 }
        r[k] = w as i32;
    }
    // glibc keeps a 34-entry history then discards 310 outputs
    let mut o = vec![0i32; 344];
    o[..31].copy_from_slice(&r[..31]);
    for k in 31..34 { o[k] = o[k - 31] }
    for k in 34..344 { o[k] = o[k - 31].wrapping_add(o[k - 3]) }
    let mut h = [0i32; 34];
    h.copy_from_slice(&o[310..344]);
    *r = h;
    RIDX = 0;
    RSEEDED = true;
}

#[no_mangle]
pub unsafe extern "C" fn rand() -> c_int {
    if !RSEEDED { srand(1) }
    let r = &raw mut RSTATE;
    let r = &mut *r;
    // o[k] = o[k-31] + o[k-3]; keep a ring of 34
    let k = RIDX;
    let v = r[(k + 34 - 31) % 34].wrapping_add(r[(k + 34 - 3) % 34]);
    r[k % 34] = v;
    RIDX = (k + 1) % 34;
    ((v as u32) >> 1) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn time(t: *mut libc::time_t) -> libc::time_t {
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0) as libc::time_t;
    if !t.is_null() { *t = now }
    now
}

#[no_mangle]
pub unsafe extern "C" fn clock() -> libc::clock_t {
    static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    START.get_or_init(std::time::Instant::now).elapsed().as_micros() as libc::clock_t
}

// ---------------------------------------------------------------- ctype
static mut CTYPE_B: [u16; 384] = [0; 384];
static mut CTYPE_B_PTR: *const u16 = core::ptr::null();
static mut CTYPE_LOWER: [i32; 384] = [0; 384];
static mut CTYPE_LOWER_PTR: *const i32 = core::ptr::null();
static mut CTYPE_UPPER: [i32; 384] = [0; 384];
static mut CTYPE_UPPER_PTR: *const i32 = core::ptr::null();

unsafe fn ctype_init() {
    if !CTYPE_B_PTR.is_null() { return }
    let b = &mut *(&raw mut CTYPE_B);
    let lo = &mut *(&raw mut CTYPE_LOWER);
    let up = &mut *(&raw mut CTYPE_UPPER);
    for i in 0..384usize {
        let c = i as i32 - 128;
        lo[i] = c;
        up[i] = c;
        if !(0..128).contains(&c) { continue }
        let ch = c as u8;
        let mut m = 0u16;
        if ch.is_ascii_uppercase() { m |= 0x100 }
        if ch.is_ascii_lowercase() { m |= 0x200 }
        if ch.is_ascii_alphabetic() { m |= 0x400 }
        if ch.is_ascii_digit() { m |= 0x800 }
        if ch.is_ascii_hexdigit() { m |= 0x1000 }
        if matches!(ch, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r') { m |= 0x2000 }
        if (0x20..0x7f).contains(&ch) { m |= 0x4000 }
        if (0x21..0x7f).contains(&ch) { m |= 0x8000 }
        if ch == b' ' || ch == b'\t' { m |= 0x1 }
        if ch < 0x20 || ch == 0x7f { m |= 0x2 }
        if ch.is_ascii_punctuation() { m |= 0x4 }
        if ch.is_ascii_alphanumeric() { m |= 0x8 }
        b[i] = m;
        lo[i] = ch.to_ascii_lowercase() as i32;
        up[i] = ch.to_ascii_uppercase() as i32;
    }
    CTYPE_B_PTR = (&raw const CTYPE_B as *const u16).add(128);
    CTYPE_LOWER_PTR = (&raw const CTYPE_LOWER as *const i32).add(128);
    CTYPE_UPPER_PTR = (&raw const CTYPE_UPPER as *const i32).add(128);
}

#[no_mangle]
pub unsafe extern "C" fn __ctype_b_loc() -> *mut *const u16 { ctype_init(); &raw mut CTYPE_B_PTR }
#[no_mangle]
pub unsafe extern "C" fn __ctype_tolower_loc() -> *mut *const i32 { ctype_init(); &raw mut CTYPE_LOWER_PTR }
#[no_mangle]
pub unsafe extern "C" fn __ctype_toupper_loc() -> *mut *const i32 { ctype_init(); &raw mut CTYPE_UPPER_PTR }
#[no_mangle]
pub unsafe extern "C" fn tolower(c: c_int) -> c_int { if (0..128).contains(&c) { (c as u8).to_ascii_lowercase() as c_int } else { c } }
#[no_mangle]
pub unsafe extern "C" fn toupper(c: c_int) -> c_int { if (0..128).contains(&c) { (c as u8).to_ascii_uppercase() as c_int } else { c } }

// signal: Miri's own shim (std's SIGPIPE setup); a model here would clash with it.


// harness platform model: macOS ctype (`_DefaultRuneLocale.__runetype`, `__maskrune`) for a
// translation made on macOS (bzip2). Only `__runetype` (byte offset 60) is read by the tree.
#[repr(C)]
pub struct JobcratRuneLocaleModel { head: [u8; 60], runetype: [u32; 256], rest: [u8; 8192] }
const fn jobcrat_macos_runetype() -> [u32; 256] {
    let mut t = [0u32; 256];
    let mut c = 0usize;
    while c < 128 {
        let b = c as u8;
        let mut m = 0u32;
        let upper = b >= b'A' && b <= b'Z';
        let lower = b >= b'a' && b <= b'z';
        let digit = b >= b'0' && b <= b'9';
        let space = b == b' ' || (b >= 9 && b <= 13);
        let print = b >= 0x20 && b < 0x7f;
        let graph = b > 0x20 && b < 0x7f;
        if upper || lower { m |= 0x100 }          // _CTYPE_A
        if b < 0x20 || b == 0x7f { m |= 0x200 }   // _CTYPE_C
        if digit { m |= 0x400 }                   // _CTYPE_D
        if graph { m |= 0x800 }                   // _CTYPE_G
        if lower { m |= 0x1000 }                  // _CTYPE_L
        if graph && !(upper || lower || digit) { m |= 0x2000 } // _CTYPE_P
        if space { m |= 0x4000 }                  // _CTYPE_S
        if upper { m |= 0x8000 }                  // _CTYPE_U
        if digit || (b >= b'a' && b <= b'f') || (b >= b'A' && b <= b'F') { m |= 0x10000 } // _CTYPE_X
        if b == b' ' || b == b'\t' { m |= 0x20000 } // _CTYPE_B
        if print { m |= 0x40000 }                 // _CTYPE_R
        t[c] = m;
        c += 1;
    }
    t
}
#[no_mangle]
pub static mut _DefaultRuneLocale: JobcratRuneLocaleModel =
    JobcratRuneLocaleModel { head: [0; 60], runetype: jobcrat_macos_runetype(), rest: [0; 8192] };
#[no_mangle]
pub unsafe extern "C" fn __maskrune(c: c_int, mask: c_ulong) -> c_int {
    if (0..256).contains(&c) { (jobcrat_macos_runetype()[c as usize] as c_ulong & mask) as c_int } else { 0 }
}

// macOS stdio names (a macOS translation's `__stdoutp` / `__stderrp` / `__stdinp`)
#[no_mangle]
pub static mut __stdinp: *mut CFile = unsafe { &raw mut STDIN_F };
#[no_mangle]
pub static mut __stdoutp: *mut CFile = unsafe { &raw mut STDOUT_F };
#[no_mangle]
pub static mut __stderrp: *mut CFile = unsafe { &raw mut STDERR_F };

// ---------------------------------------------------------------- asserts
#[no_mangle]
pub unsafe extern "C" fn __assert_fail(expr: *const c_char, file: *const c_char, line: c_uint, func: *const c_char) -> ! {
    let s = |p: *const c_char| String::from_utf8_lossy(cstr(p)).into_owned();
    eprintln!("{}: {}: {}: Assertion `{}' failed.", "program", s(file), line, s(expr));
    let _ = func;
    std::process::abort()
}

#[no_mangle]
pub unsafe extern "C" fn __assert_rtn(func: *const c_char, file: *const c_char, line: c_int, expr: *const c_char) -> ! {
    let s = |p: *const c_char| if p.is_null() { String::new() } else { String::from_utf8_lossy(cstr(p)).into_owned() };
    eprintln!("Assertion failed: ({}), function {}, file {}, line {}.", s(expr), s(func), s(file), line);
    std::process::abort()
}

// ---------------------------------------------------------------- setjmp / longjmp
/// Miri supports neither. The model makes `setjmp` return 0 (its first return, the only one a run
/// without a library error takes) and stops the run at the first `longjmp` with a named report,
/// so the Miri receipt states its coverage as "up to the first longjmp" (libzahl: the first
/// `assert_nr`, or a library error). The native runs use the C library's real setjmp / longjmp.
#[no_mangle]
pub unsafe extern "C" fn _setjmp(_env: *mut c_void) -> c_int {
    0
}

#[no_mangle]
pub unsafe extern "C" fn longjmp(_env: *mut c_void, _val: c_int) -> ! {
    eprintln!("longjmp-reached: the harness models setjmp as a single return; the Miri run ends here");
    std::process::abort()
}

// memmove and the libm functions Miri has no shim for, over Rust's own
// float methods (Miri evaluates them) and an overlapping copy. Declared harness models.
#[no_mangle]
pub unsafe extern "C" fn memmove(d: *mut c_void, s: *const c_void, n: c_ulong) -> *mut c_void {
    core::ptr::copy(s as *const u8, d as *mut u8, n as usize);
    d
}
#[no_mangle]
pub extern "C" fn exp(x: f64) -> f64 { x.exp() }
#[no_mangle]
pub extern "C" fn log(x: f64) -> f64 { x.ln() }
#[no_mangle]
pub extern "C" fn log10(x: f64) -> f64 { x.log10() }
#[no_mangle]
pub extern "C" fn pow(x: f64, y: f64) -> f64 { x.powf(y) }
#[no_mangle]
pub extern "C" fn sqrt(x: f64) -> f64 { x.sqrt() }
#[no_mangle]
pub extern "C" fn fabs(x: f64) -> f64 { x.abs() }
#[no_mangle]
pub extern "C" fn floor(x: f64) -> f64 { x.floor() }
#[no_mangle]
pub extern "C" fn ceil(x: f64) -> f64 { x.ceil() }
#[no_mangle]
pub extern "C" fn round(x: f64) -> f64 { x.round() }
#[no_mangle]
pub extern "C" fn sin(x: f64) -> f64 { x.sin() }
#[no_mangle]
pub extern "C" fn cos(x: f64) -> f64 { x.cos() }
#[no_mangle]
pub extern "C" fn fmod(x: f64, y: f64) -> f64 { x % y }

// ht's demo reads words with scanf; the same scanner as fscanf, on stdin
#[no_mangle]
pub unsafe extern "C" fn scanf(fmt: *const c_char, mut args: ...) -> c_int {
    let f = stdin;
    let mut input = |take: bool| -> c_int {
        let c = file_getc(f);
        if !take && c >= 0 { (*f).unget = c }
        c
    };
    scan(&mut input, fmt, &mut args)
}

// glibc's versioned stat entry points (`__xstat`, `__lxstat`, `__fxstat`, ver = _STAT_VER), which
// the translation calls where the C source calls stat / lstat / fstat; Miri shims the unversioned
// ones (libtree's runs reach them)
#[no_mangle]
pub unsafe extern "C" fn __xstat(_ver: libc::c_int, path: *const libc::c_char, buf: *mut libc::stat) -> libc::c_int {
    libc::stat(path, buf)
}
#[no_mangle]
pub unsafe extern "C" fn __lxstat(_ver: libc::c_int, path: *const libc::c_char, buf: *mut libc::stat) -> libc::c_int {
    libc::lstat(path, buf)
}
#[no_mangle]
pub unsafe extern "C" fn __fxstat(_ver: libc::c_int, fd: libc::c_int, buf: *mut libc::stat) -> libc::c_int {
    libc::fstat(fd, buf)
}
