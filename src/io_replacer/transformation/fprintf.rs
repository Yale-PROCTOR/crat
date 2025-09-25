use std::fmt::Write as _;

#[derive(Debug)]
pub(super) struct RustFormat {
    pub(super) format: String,
    pub(super) casts: Vec<&'static str>,
    pub(super) width_args: Vec<usize>,
}

pub(super) fn to_rust_format(mut remaining: &[u8]) -> RustFormat {
    let mut format = String::new();
    let mut casts = vec![];
    let mut width_count = 0;
    let mut width_args = vec![];
    loop {
        let res = parse_format(remaining);
        for c in String::from_utf8_lossy(res.prefix).chars() {
            match c {
                '{' => format.push_str("{{"),
                '}' => format.push_str("}}"),
                '\n' => format.push_str("\\n"),
                '\r' => format.push_str("\\r"),
                '\t' => format.push_str("\\t"),
                '\\' => format.push_str("\\\\"),
                '\0' => {}
                '\"' => format.push_str("\\\""),
                _ => {
                    if c.is_ascii_alphanumeric() || c.is_ascii_graphic() || c == ' ' {
                        format.push(c);
                    } else {
                        write!(format, "\\u{{{:x}}}", c as u32).unwrap();
                    }
                }
            }
        }
        if let Some(cs) = res.conversion_spec {
            let mut fmt = String::new();
            let mut conv = String::new();
            let mut minus = false;
            for flag in cs.flags {
                match flag {
                    FlagChar::Apostrophe => todo!(),
                    FlagChar::Minus => minus = true,
                    FlagChar::Plus => fmt.push('+'),
                    FlagChar::Space => todo!(),
                    FlagChar::Hash => fmt.push('#'),
                    FlagChar::Zero => fmt.push('0'),
                }
            }
            if let Some(width) = cs.width {
                if minus {
                    fmt.insert(0, '<');
                } else {
                    fmt.insert(0, '>');
                }
                match width {
                    Width::Asterisk => {
                        write!(fmt, "width{width_count}$").unwrap();
                        width_count += 1;
                        width_args.push(casts.len());
                        casts.push("usize");
                    }
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            if let Some(precision) = cs.precision {
                fmt.push('.');
                match precision {
                    Width::Asterisk => {
                        fmt.push('*');
                        casts.push("usize");
                    }
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            match cs.conversion {
                Conversion::Int | Conversion::Unsigned | Conversion::Char | Conversion::Str => {}
                Conversion::Octal => fmt.push('o'),
                Conversion::Hexadecimal => fmt.push('x'),
                Conversion::HexadecimalUpper => fmt.push('X'),
                Conversion::Double => {
                    if cs.precision.is_none() {
                        fmt.push_str(".6");
                    }
                }
                Conversion::DoubleExp => fmt.push('e'),
                Conversion::DoubleAuto => {}
                Conversion::DoubleHex => {}
                Conversion::Pointer => fmt.push_str("#x"),
                Conversion::Num | Conversion::C | Conversion::S => unimplemented!(),
                Conversion::Percent => conv = "%".to_string(),
            }
            if conv.is_empty() {
                conv.push('{');
                if !fmt.is_empty() {
                    conv.push(':');
                    conv.push_str(&fmt);
                }
                conv.push('}');
            }
            format.push_str(&conv);
            if let Some(cast) = cs.conversion.ty(cs.length) {
                casts.push(cast);
            }
        }
        if let Some(rem) = res.remaining {
            remaining = rem;
        } else {
            break;
        }
    }
    RustFormat {
        format,
        casts,
        width_args,
    }
}

struct ParseResult<'a> {
    prefix: &'a [u8],
    conversion_spec: Option<ConversionSpec>,
    remaining: Option<&'a [u8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Percent,
    Flag,
    Width,
    Period,
    Precision,
    Length,
    H,
    L,
    Conversion,
}

fn err(s: &[u8], i: Option<usize>) -> ! {
    panic!("{}", String::from_utf8_lossy(&s[i.unwrap()..]));
}

fn parse_format(s: &[u8]) -> ParseResult<'_> {
    let mut start_idx = None;
    let mut state = State::Percent;
    let mut flags = vec![];
    let mut width = None;
    let mut precision = None;
    let mut length = None;
    let mut conversion = None;
    for (i, c) in s.iter().enumerate() {
        if state == State::Percent {
            if *c == b'%' {
                start_idx = Some(i);
                state = State::Flag;
            }
        } else if (b'1'..=b'9').contains(c) || (*c == b'0' && state != State::Flag) {
            match state {
                State::Flag => {
                    width = Some(Width::Decimal((c - b'0') as usize));
                    state = State::Width;
                }
                State::Width => {
                    let Some(Width::Decimal(n)) = &mut width else { unreachable!() };
                    *n = *n * 10 + (c - b'0') as usize;
                }
                State::Precision => match &mut precision {
                    None => precision = Some(Width::Decimal((c - b'0') as usize)),
                    Some(Width::Decimal(n)) => *n = *n * 10 + (c - b'0') as usize,
                    _ => unreachable!(),
                },
                _ => err(s, start_idx),
            }
        } else if let Some(flag) = FlagChar::from_u8(*c) {
            flags.push(flag);
        } else if *c == b'*' {
            match state {
                State::Flag => {
                    width = Some(Width::Asterisk);
                    state = State::Period;
                }
                State::Precision => {
                    precision = Some(Width::Asterisk);
                    state = State::Length;
                }
                _ => err(s, start_idx),
            }
        } else if *c == b'.' {
            if matches!(state, State::Flag | State::Width | State::Period) {
                state = State::Precision;
            } else {
                err(s, start_idx);
            }
        } else if let Some(len) = LengthMod::from_u8(*c) {
            match len {
                LengthMod::Short => match state {
                    State::Flag
                    | State::Width
                    | State::Period
                    | State::Precision
                    | State::Length => {
                        state = State::H;
                    }
                    State::H => {
                        length = Some(LengthMod::Char);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                LengthMod::Long => match state {
                    State::Flag
                    | State::Width
                    | State::Period
                    | State::Precision
                    | State::Length => {
                        state = State::L;
                    }
                    State::L => {
                        length = Some(LengthMod::LongLong);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                _ => {
                    length = Some(len);
                    state = State::Conversion;
                }
            }
        } else if let Some(conv) = Conversion::from_u8(*c) {
            match state {
                State::Flag
                | State::Width
                | State::Period
                | State::Precision
                | State::Length
                | State::Conversion => {
                    conversion = Some((conv, i));
                    break;
                }
                State::H => {
                    length = Some(LengthMod::Short);
                    conversion = Some((conv, i));
                    break;
                }
                State::L => {
                    length = Some(LengthMod::Long);
                    conversion = Some((conv, i));
                    break;
                }
                _ => unreachable!(),
            }
        } else {
            err(s, start_idx);
        }
    }

    if let Some(start_idx) = start_idx {
        if let Some((conversion, last_idx)) = conversion {
            ParseResult {
                prefix: &s[..start_idx],
                conversion_spec: Some(ConversionSpec {
                    flags,
                    width,
                    precision,
                    length,
                    conversion,
                }),
                remaining: Some(&s[last_idx + 1..]),
            }
        } else {
            err(s, Some(start_idx));
        }
    } else {
        ParseResult {
            prefix: s,
            conversion_spec: None,
            remaining: None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FlagChar {
    Apostrophe,
    Minus,
    Plus,
    Space,
    Hash,
    Zero,
}

impl std::fmt::Display for FlagChar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Apostrophe => write!(f, "'"),
            Self::Minus => write!(f, "-"),
            Self::Plus => write!(f, "+"),
            Self::Space => write!(f, " "),
            Self::Hash => write!(f, "#"),
            Self::Zero => write!(f, "0"),
        }
    }
}

impl FlagChar {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'\'' => Some(Self::Apostrophe),
            b'-' => Some(Self::Minus),
            b'+' => Some(Self::Plus),
            b' ' => Some(Self::Space),
            b'#' => Some(Self::Hash),
            b'0' => Some(Self::Zero),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Width {
    Asterisk,
    Decimal(usize),
}

impl std::fmt::Display for Width {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Width::Asterisk => write!(f, "*"),
            Width::Decimal(n) => write!(f, "{n}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LengthMod {
    Char,
    Short,
    Long,
    LongLong,
    IntMax,
    Size,
    PtrDiff,
    LongDouble,
}

impl std::fmt::Display for LengthMod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Char => write!(f, "hh"),
            Self::Short => write!(f, "h"),
            Self::Long => write!(f, "l"),
            Self::LongLong => write!(f, "ll"),
            Self::IntMax => write!(f, "j"),
            Self::Size => write!(f, "z"),
            Self::PtrDiff => write!(f, "t"),
            Self::LongDouble => write!(f, "L"),
        }
    }
}

impl LengthMod {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'h' => Some(Self::Short),
            b'l' => Some(Self::Long),
            b'j' => Some(Self::IntMax),
            b'z' => Some(Self::Size),
            b't' => Some(Self::PtrDiff),
            b'L' => Some(Self::LongDouble),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Conversion {
    Int,
    Octal,
    Unsigned,
    Hexadecimal,
    HexadecimalUpper,
    Double,
    DoubleExp,
    DoubleAuto,
    DoubleHex,
    Char,
    Str,
    Pointer,
    Num,
    C,
    S,
    Percent,
}

impl std::fmt::Display for Conversion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => write!(f, "d"),
            Self::Octal => write!(f, "o"),
            Self::Unsigned => write!(f, "u"),
            Self::Hexadecimal => write!(f, "x"),
            Self::HexadecimalUpper => write!(f, "X"),
            Self::Double => write!(f, "f"),
            Self::DoubleExp => write!(f, "e"),
            Self::DoubleAuto => write!(f, "g"),
            Self::DoubleHex => write!(f, "a"),
            Self::Char => write!(f, "c"),
            Self::Str => write!(f, "s"),
            Self::Pointer => write!(f, "p"),
            Self::Num => write!(f, "n"),
            Self::C => write!(f, "C"),
            Self::S => write!(f, "S"),
            Self::Percent => write!(f, "%"),
        }
    }
}

impl Conversion {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'd' | b'i' => Some(Self::Int),
            b'o' => Some(Self::Octal),
            b'u' => Some(Self::Unsigned),
            b'x' => Some(Self::Hexadecimal),
            b'X' => Some(Self::HexadecimalUpper),
            b'f' | b'F' => Some(Self::Double),
            b'e' | b'E' => Some(Self::DoubleExp),
            b'g' | b'G' => Some(Self::DoubleAuto),
            b'a' | b'A' => Some(Self::DoubleHex),
            b'c' => Some(Self::Char),
            b's' => Some(Self::Str),
            b'p' => Some(Self::Pointer),
            b'n' => Some(Self::Num),
            b'C' => Some(Self::C),
            b'S' => Some(Self::S),
            b'%' => Some(Self::Percent),
            _ => None,
        }
    }

    fn ty(self, length: Option<LengthMod>) -> Option<&'static str> {
        use LengthMod::*;
        let t = match self {
            Self::Int => match length {
                None => "i32",
                Some(Char) => "i8",
                Some(Short) => "i16",
                Some(Long | LongLong | IntMax | Size) => "i64",
                Some(PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Octal | Self::Unsigned => match length {
                None => "u32",
                Some(Char) => "u8",
                Some(Short) => "u16",
                Some(Long | LongLong | IntMax | Size | PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Hexadecimal | Self::HexadecimalUpper => match length {
                None => "crate::stdio::Xu32",
                Some(Char) => "crate::stdio::Xu8",
                Some(Short) => "crate::stdio::Xu16",
                Some(Long | LongLong | IntMax | Size | PtrDiff) => "crate::stdio::Xu64",
                Some(LongDouble) => panic!(),
            },
            Self::Double | Self::DoubleExp => match length {
                None | Some(Long) => "f64",
                Some(LongDouble) => "f128::f128",
                _ => panic!(),
            },
            Self::DoubleAuto => match length {
                None | Some(Long) => "crate::stdio::Gf64",
                _ => panic!(),
            },
            Self::DoubleHex => match length {
                None | Some(Long) => "crate::stdio::Af64",
                _ => panic!(),
            },
            Self::Char => "u8 as char",
            Self::Str => match length {
                None => "&str",
                Some(Long) => "String",
                _ => panic!(),
            },
            Self::Pointer => "usize",
            Self::C | Self::S => panic!(),
            Self::Num | Self::Percent => return None,
        };
        Some(t)
    }
}

#[derive(Debug, Clone)]
struct ConversionSpec {
    flags: Vec<FlagChar>,
    width: Option<Width>,
    precision: Option<Width>,
    length: Option<LengthMod>,
    conversion: Conversion,
}

impl std::fmt::Display for ConversionSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%")?;
        for flag in &self.flags {
            write!(f, "{flag}")?;
        }
        if let Some(width) = self.width {
            write!(f, "{width}")?;
        }
        if let Some(precision) = self.precision {
            write!(f, ".{precision}")?;
        }
        if let Some(length) = self.length {
            write!(f, "{length}")?;
        }
        write!(f, "{}", self.conversion)
    }
}
