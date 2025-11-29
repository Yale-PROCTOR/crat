pub fn parse_specs(mut remaining: &[u8]) -> Vec<ConversionSpec> {
    let mut specs = vec![];
    loop {
        let res = parse_format(remaining);
        if let Some(rem) = res.remaining {
            remaining = rem;
            specs.push(res.conversion_spec.unwrap());
        } else {
            break specs;
        }
    }
}

pub struct ParseResult<'a> {
    pub prefix: &'a [u8],
    pub conversion_spec: Option<ConversionSpec>,
    pub remaining: Option<&'a [u8]>,
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

pub fn parse_format(s: &[u8]) -> ParseResult<'_> {
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
pub enum FlagChar {
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
pub enum Width {
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
pub enum LengthMod {
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
pub enum Conversion {
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

    pub fn ty(self, length: Option<LengthMod>) -> Option<&'static str> {
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
                None => "crate::c_lib::Xu32",
                Some(Char) => "crate::c_lib::Xu8",
                Some(Short) => "crate::c_lib::Xu16",
                Some(Long | LongLong | IntMax | Size | PtrDiff) => "crate::c_lib::Xu64",
                Some(LongDouble) => panic!(),
            },
            Self::Double | Self::DoubleExp => match length {
                None | Some(Long) => "f64",
                Some(LongDouble) => "f128::f128",
                _ => panic!(),
            },
            Self::DoubleAuto => match length {
                None | Some(Long) => "crate::c_lib::Gf64",
                _ => panic!(),
            },
            Self::DoubleHex => match length {
                None | Some(Long) => "crate::c_lib::Af64",
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
pub struct ConversionSpec {
    pub flags: Vec<FlagChar>,
    pub width: Option<Width>,
    pub precision: Option<Width>,
    pub length: Option<LengthMod>,
    pub conversion: Conversion,
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
