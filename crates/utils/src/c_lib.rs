pub static PEEK: &str = r#"
fn peek<R: std::io::BufRead>(mut stream: R, err: Option<&mut i32>, eof: Option<&mut i32>) -> u8 {
    match stream.fill_buf() {
        Ok([c, ..]) => return *c,
        Ok([]) => {
            if let Some(eof) = eof {
                *eof = 1;
            }
        }
        Err(_) => {
            if let Some(err) = err {
                *err = 1;
            }
        }
    }
    0xff
}
"#;

pub static PARSE_INTEGER: &str = r#"
#[inline]
fn parse_integer<R: std::io::BufRead>(
    mut stream: R,
    mut base: u32,
    signed: bool,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> (Option<u64>, bool) {
    let width_reached = |len: usize| width.is_some_and(|w| len >= w);

    while peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()).is_ascii_whitespace() {
        stream.consume(1);
    }

    let mut len = 0;
    let mut negative = false;
    let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
    if c == b'+' {
        stream.consume(1);
        len += 1;
    } else if c == b'-' {
        negative = true;
        stream.consume(1);
        len += 1;
    }
    if width_reached(len) {
        return (None, false);
    }

    let mut num = String::new();
    if base == 0 || base == 16 {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == b'0' {
            stream.consume(1);
            len += 1;
            let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
            if c == b'x' || c == b'X' {
                base = 16;
                stream.consume(1);
                len += 1;
            } else {
                num.push('0');
                if base == 0 {
                    base = 8;
                }
            }
        } else if base == 0 {
            base = 10;
        }
    }

    while !width_reached(len) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if (base <= 10 && (b'0'..b'0' + (base as u8)).contains(&c))
            || (base > 10
                && ((b'0'..=b'9').contains(&c)
                    || (b'a'..b'a' + (base - 10) as u8).contains(&c)
                    || (b'A'..b'A' + (base - 10) as u8).contains(&c)))
        {
            num.push(c as char);
            stream.consume(1);
            len += 1;
        } else {
            break;
        }
    }

    if num.is_empty() {
        return (None, false);
    }

    match u64::from_str_radix(&num, base) {
        Ok(v) => {
            if !signed {
                (Some(if negative { v.wrapping_neg() } else { v }), false)
            } else if !negative {
                if v > i64::MAX as u64 {
                    (Some(i64::MAX as u64), true)
                } else {
                    (Some(v), false)
                }
            } else if v > (i64::MIN as u64).wrapping_neg() {
                (Some(i64::MIN as u64), true)
            } else {
                (Some(v.wrapping_neg()), false)
            }
        }
        Err(_) => {
            if !signed {
                (Some(u64::MAX), true)
            } else if !negative {
                (Some(i64::MAX as u64), true)
            } else {
                (Some(i64::MIN as u64), true)
            }
        }
    }
}
"#;

pub static PARSE_FLOAT: &str = r#"
#[inline]
fn parse_float<R: std::io::BufRead, F: num_traits::Float + num_traits::Num>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> (Option<F>, bool) {
    let mut neg = false;
    while peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()).is_ascii_whitespace() {
        stream.consume(1);
    }
    let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
    if c == b'+' {
        stream.consume(1);
    } else if c == b'-' {
        neg = true;
        stream.consume(1);
    }

    let mut i = 0;
    let len = width.unwrap_or(8).min(8);
    let infinity = b"infinity";
    while i < len {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c | 32 == infinity[i] {
            stream.consume(1);
            i += 1;
        } else {
            break;
        }
    }
    if i == 3 || i == 8 {
        peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        let v = if neg {
            F::neg_infinity()
        } else {
            F::infinity()
        };
        return (Some(v), false);
    } else if i > 0 {
        return (None, false);
    }

    let mut i = 0;
    let len = width.unwrap_or(3).min(3);
    let nan = b"nan";
    while i < len {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c | 32 == nan[i] {
            stream.consume(1);
            i += 1;
        } else {
            break;
        }
    }
    if i == 3 {
        peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        return (Some(F::nan()), false);
    } else if i > 0 {
        return (None, false);
    }

    let mut v = Vec::new();
    if neg {
        v.push(b'-');
    }

    if peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) == b'0' {
        stream.consume(1);
        v.push(b'0');
        if peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) | 32 == b'x' {
            stream.consume(1);
            panic!();
        }
    }

    let mut dot_seen = false;
    let mut is_nonzero = false;
    loop {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == b'0' {
        } else if (b'1'..=b'9').contains(&c) {
            is_nonzero = true;
        } else if c == b'.' && !dot_seen {
            dot_seen = true;
        } else {
            break;
        }
        v.push(c);
        stream.consume(1);
    }

    if !v.iter().any(|c| c.is_ascii_digit()) {
        return (None, false);
    }

    if peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) | 32 == b'e' {
        v.push(b'e');
        stream.consume(1);

        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == b'+' || c == b'-' {
            v.push(c);
            stream.consume(1);
        }

        loop {
            let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
            if c.is_ascii_digit() {
                v.push(c);
                stream.consume(1);
            } else {
                break;
            }
        }

        while !v.last().unwrap().is_ascii_digit() {
            v.pop();
        }
    }

    let s = std::str::from_utf8(&v).unwrap();
    let f = match F::from_str_radix(s, 10) {
        Ok(f) => f,
        Err(_) => panic!(),
    };
    let erange = f.is_infinite() || is_nonzero && f.is_zero();
    (Some(f), erange)
}
"#;

pub static IS_EOF: &str = r#"
fn is_eof<R: std::io::BufRead>(mut stream: R, mut err: Option<&mut i32>, mut eof: Option<&mut i32>, consume_whitespace: bool) -> bool {
    if consume_whitespace {
        while peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()).is_ascii_whitespace() {
            stream.consume(1);
        }
    }
    peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) == 0xff
}
"#;

pub static PARSE_DECIMAL: &str = r#"
fn parse_decimal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, 10, true, width, err.as_deref_mut(), eof.as_deref_mut()).0
}
"#;

pub static PARSE_F64: &str = r#"
fn parse_f64<R: std::io::BufRead>(
    stream: R,
    width: Option<usize>,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> Option<f64> {
    parse_float(
        stream,
        width,
        err,
        eof,
    ).0
}
"#;

pub static XU8: &str = r#"
pub(crate) struct Xu8(pub(crate) u8);
impl std::fmt::LowerHex for Xu8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub static XU16: &str = r#"
pub(crate) struct Xu16(pub(crate) u16);
impl std::fmt::LowerHex for Xu16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub static XU32: &str = r#"
pub(crate) struct Xu32(pub(crate) u32);
impl std::fmt::LowerHex for Xu32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub static XU64: &str = r#"
pub(crate) struct Xu64(pub(crate) u64);
impl std::fmt::LowerHex for Xu64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub static GF64: &str = r#"
pub(crate) struct Gf64(pub(crate) f64);
impl std::fmt::Display for Gf64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = self.0;
        if v.is_nan() {
            return f.write_str("nan");
        }
        if v.is_infinite() {
            return f.write_str(if v.is_sign_negative() { "-inf" } else { "inf" });
        }
        let sign = if v.is_sign_negative() { "-" } else { "" };
        let abs = v.abs();
        let p = match f.precision() {
            Some(0) => 1,
            Some(n) => n,
            None => 6,
        };
        let x = if abs == 0.0 {
            0
        } else {
            abs.log10().floor() as i32
        };
        let s = if x >= -4 && x < p as i32 {
            let frac_prec = (p as i32 - (x + 1)).max(0) as usize;
            let mut s = std::fmt::format(format_args!("{abs:.frac_prec$}"));
            if !f.alternate() && s.contains('.') {
                while s.ends_with('0') {
                    s.pop();
                }
                if s.ends_with('.') {
                    s.pop();
                }
            }
            s
        } else {
            let exp_prec = p.saturating_sub(1);
            let s_full = std::fmt::format(format_args!("{abs:.exp_prec$e}"));
            let idx = s_full.find('e').unwrap();
            let mut mant = s_full[..idx].to_string();
            let exp = &s_full[idx + 1..];
            if !f.alternate() && mant.contains('.') {
                while mant.ends_with('0') {
                    mant.pop();
                }
                if mant.ends_with('.') {
                    mant.pop();
                }
            }
            let (sign_e, digits) = if let Some(digits) = exp.strip_prefix('-') {
                ('-', digits)
            } else {
                (
                    '+',
                    if let Some(digits) = exp.strip_prefix('+') {
                        digits
                    } else {
                        exp
                    },
                )
            };
            let digits = if digits.len() < 2 {
                std::fmt::format(format_args!("0{digits}"))
            } else {
                digits.to_string()
            };
            std::fmt::format(format_args!("{mant}e{sign_e}{digits}"))
        };
        f.write_str(sign)?;
        f.write_str(&s)
    }
}
"#;
