pub fn parse_specs(mut remaining: &[u8]) -> Vec<ConversionSpec> {
    let mut specs = vec![];
    loop {
        let res = parse_format(remaining);
        if let Some(rem) = res.remaining {
            remaining = rem;
            let mut conversion_spec = res.conversion_spec.unwrap();
            conversion_spec.leading_space = res.prefix.iter().any(u8::is_ascii_whitespace);
            specs.push(conversion_spec);
        } else {
            if res.prefix.iter().any(u8::is_ascii_whitespace)
                && let Some(last) = specs.last_mut()
            {
                last.trailing_space = true;
            }
            break specs;
        }
    }
}

struct ParseResult<'a> {
    #[allow(unused)]
    prefix: &'a [u8],
    conversion_spec: Option<ConversionSpec>,
    remaining: Option<&'a [u8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Percent,
    Asterisk,
    Width,
    H,
    L,
    Conversion,
    Circumflex,
    ScanSet,
}

fn err(s: &[u8], i: Option<usize>) -> ! {
    panic!("{}", String::from_utf8_lossy(&s[i.unwrap()..]));
}

fn parse_format(s: &[u8]) -> ParseResult<'_> {
    let mut start_idx = None;
    let mut state = State::Percent;
    let mut assign = true;
    let mut width = None;
    let mut length = None;
    let mut conversion = None;
    for (i, c) in s.iter().enumerate() {
        if state == State::Percent {
            if *c == b'%' {
                start_idx = Some(i);
                state = State::Asterisk;
            }
        } else if matches!(state, State::Circumflex | State::ScanSet) {
            if *c == b'^' {
                if state == State::Circumflex {
                    let Some((Conversion::ScanSet(ScanSet { negative, .. }), _)) = &mut conversion
                    else {
                        unreachable!()
                    };
                    *negative = true;
                    state = State::ScanSet;
                } else {
                    // C7.21.6.2: only a LEADING `^` negates a scanset; any
                    // later one is an ordinary member. This arm used to
                    // `err()` — which is `panic!`, not a recoverable error —
                    // and aborted the whole analysis on the `%[^? | ^#]` at
                    // `benchmarks/rs-crown/urlparser/src/test.rs:404`.
                    //
                    // Reachable only where the old parser panicked, so this
                    // cannot alter an execution that previously completed. That
                    // is asserted over the corpus rather than argued — see
                    // `the_fix_only_changes_executions_that_previously_panicked`.
                    let Some((Conversion::ScanSet(ScanSet { chars, .. }), _)) = &mut conversion
                    else {
                        unreachable!()
                    };
                    chars.push(*c);
                }
            } else if *c == b']' {
                if state == State::ScanSet {
                    let Some((_, old_i)) = &mut conversion else { unreachable!() };
                    *old_i = i;
                    break;
                } else {
                    err(s, start_idx);
                }
            } else {
                state = State::ScanSet;
                let Some((Conversion::ScanSet(ScanSet { chars, .. }), _)) = &mut conversion else {
                    unreachable!()
                };
                chars.push(*c);
            }
        } else if c.is_ascii_digit() {
            match state {
                State::Asterisk => {
                    width = Some((c - b'0') as usize);
                    state = State::Width;
                }
                State::Width => {
                    let Some(n) = width.as_mut() else { unreachable!() };
                    *n = *n * 10 + (c - b'0') as usize;
                }
                _ => err(s, start_idx),
            }
        } else if *c == b'*' {
            if state == State::Asterisk {
                assign = false;
                state = State::Width;
            } else {
                err(s, start_idx);
            }
        } else if let Some(len) = LengthMod::from_u8(*c) {
            match len {
                LengthMod::Short => match state {
                    State::Asterisk | State::Width => {
                        state = State::H;
                    }
                    State::H => {
                        length = Some(LengthMod::Char);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                LengthMod::Long => match state {
                    State::Asterisk | State::Width => {
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
                State::Asterisk | State::Width | State::Conversion => {}
                State::H => length = Some(LengthMod::Short),
                State::L => length = Some(LengthMod::Long),
                _ => err(s, start_idx),
            }
            let is_set = conv.is_set();
            conversion = Some((conv, i));
            if is_set {
                state = State::Circumflex;
            } else {
                break;
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
                    assign,
                    width,
                    length,
                    conversion,
                    leading_space: false,
                    trailing_space: false,
                }),
                remaining: Some(&s[last_idx + 1..]),
            }
        } else {
            err(s, Some(start_idx))
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScanSet {
    pub negative: bool,
    pub chars: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conversion {
    Int10,
    Int0,
    Octal,
    Unsigned,
    Hexadecimal,
    Double,
    Str,
    ScanSet(ScanSet),
    Seq,
    Pointer,
    Num,
    C,
    S,
    Percent,
}

impl std::fmt::Display for Conversion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int10 => write!(f, "d"),
            Self::Int0 => write!(f, "i"),
            Self::Octal => write!(f, "o"),
            Self::Unsigned => write!(f, "u"),
            Self::Hexadecimal => write!(f, "x"),
            Self::Double => write!(f, "g"),
            Self::Str => write!(f, "s"),
            Self::ScanSet(ScanSet { negative, chars }) => {
                write!(f, "[")?;
                if *negative {
                    write!(f, "^")?;
                }
                for c in chars {
                    if let Some(s) = crate::escape(*c) {
                        write!(f, "{s}")?;
                    } else {
                        write!(f, "{}", *c as char)?;
                    }
                }
                write!(f, "]")
            }
            Self::Seq => write!(f, "c"),
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
            b'd' => Some(Self::Int10),
            b'i' => Some(Self::Int0),
            b'o' => Some(Self::Octal),
            b'u' => Some(Self::Unsigned),
            b'x' => Some(Self::Hexadecimal),
            b'a' | b'e' | b'f' | b'g' => Some(Self::Double),
            b's' => Some(Self::Str),
            b'[' => Some(Self::ScanSet(ScanSet {
                negative: false,
                chars: vec![],
            })),
            b'c' => Some(Self::Seq),
            b'p' => Some(Self::Pointer),
            b'n' => Some(Self::Num),
            b'C' => Some(Self::C),
            b'S' => Some(Self::S),
            b'%' => Some(Self::Percent),
            _ => None,
        }
    }

    #[inline]
    fn is_set(&self) -> bool {
        matches!(self, Self::ScanSet { .. })
    }

    fn ty(&self, length: Option<LengthMod>) -> ConvTy {
        use LengthMod::*;
        let ty = match self {
            Self::Int10 | Self::Int0 => match length {
                None => "i32",
                Some(Char) => "i8",
                Some(Short) => "i16",
                Some(Long | LongLong | IntMax | Size) => "i64",
                Some(PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Octal | Self::Unsigned | Self::Hexadecimal => match length {
                None => "u32",
                Some(Char) => "u8",
                Some(Short) => "u16",
                Some(Long | LongLong | IntMax | Size | PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Double => match length {
                None => "f32",
                Some(Long) => "f64",
                Some(LongDouble) => "f128::f128",
                _ => panic!(),
            },
            Self::Str | Self::ScanSet { .. } => return ConvTy::String,
            Self::Seq => match length {
                None => "i8",
                Some(Long) => unimplemented!(),
                _ => panic!(),
            },
            Self::Pointer | Self::C | Self::S | Self::Num | Self::Percent => {
                unimplemented!()
            }
        };
        ConvTy::Scalar(ty)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ConvTy {
    Scalar(&'static str),
    String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConversionSpec {
    pub assign: bool,
    pub width: Option<usize>,
    pub length: Option<LengthMod>,
    pub conversion: Conversion,
    pub leading_space: bool,
    pub trailing_space: bool,
}

impl std::fmt::Display for ConversionSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%")?;
        if !self.assign {
            write!(f, "*")?;
        }
        if let Some(width) = self.width {
            write!(f, "{width}")?;
        }
        if let Some(length) = self.length {
            write!(f, "{length}")?;
        }
        write!(f, "{}", self.conversion)
    }
}

impl ConversionSpec {
    pub fn ty(&self) -> ConvTy {
        self.conversion.ty(self.length)
    }

    pub fn num_ty(&self) -> Option<&'static str> {
        if self.conversion != Conversion::Num || !self.assign || self.width.is_some() {
            return None;
        }

        use LengthMod::*;
        match self.length {
            None => Some("i32"),
            Some(Char) => Some("i8"),
            Some(Short) => Some("i16"),
            Some(Long | LongLong | IntMax | PtrDiff) => Some("i64"),
            Some(Size) => Some("usize"),
            Some(LongDouble) => None,
        }
    }
}

#[cfg(test)]
fn test_helper(s: &str) -> ConversionSpec {
    let res = parse_format(s.as_bytes());
    let empty: &[u8] = &[];
    assert_eq!(res.prefix, empty, "{:?}", s);
    assert_eq!(res.remaining, Some(empty), "{:?}", s);
    res.conversion_spec.expect(s)
}

#[cfg(test)]
#[test]
fn test_scanf_parse() {
    assert_eq!(
        test_helper("%d"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::Int10,
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%ld"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Long),
            conversion: Conversion::Int10,
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%hhd"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Char),
            conversion: Conversion::Int10,
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%10s"),
        ConversionSpec {
            assign: true,
            width: Some(10),
            length: None,
            conversion: Conversion::Str,
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%*s"),
        ConversionSpec {
            assign: false,
            width: None,
            length: None,
            conversion: Conversion::Str,
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%zn"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Size),
            conversion: Conversion::Num,
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%[abcd]"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::ScanSet(ScanSet {
                negative: false,
                chars: vec![b'a', b'b', b'c', b'd']
            }),
            leading_space: false,
            trailing_space: false,
        }
    );
    assert_eq!(
        test_helper("%[^\n]"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::ScanSet(ScanSet {
                negative: true,
                chars: vec![b'\n']
            }),
            leading_space: false,
            trailing_space: false,
        }
    );

    let specs = parse_specs(b"%d %3[A-Z] ");
    assert_eq!(specs.len(), 2);
    assert!(!specs[0].leading_space);
    assert!(!specs[0].trailing_space);
    assert!(specs[1].leading_space);
    assert!(specs[1].trailing_space);
}


// ---------------------------------------------------------------------------
// F-1 (2026-08-06) — the scanset non-leading-`^` fix, and its gates
// ---------------------------------------------------------------------------

/// **The pre-F1 `parse_format`, copied VERBATIM as a test-only oracle.**
///
/// Not a second canonicalizer: never compiled into the crate, no caller
/// outside this module's differential. It exists so the safety property the
/// F-1 licence rests on — *the fix can only change executions that today
/// panic* — is ASSERTED over the corpus rather than argued from the diff.
///
/// **Verbatim, and that is load-bearing.** The first attempt was a narrowed
/// re-implementation that modelled only the scanset accept/reject decision
/// and deferred everything else to *accept*. It marked printf formats as
/// accepted-by-the-old-parser when the old parser would have rejected them,
/// and the differential reported false regressions. An oracle that
/// approximates the thing it oracles is not one.
///
/// The ONLY difference from the live parser is the `else { err(..) }` arm on
/// a non-leading `^` — which is exactly the fix.
#[cfg(test)]
fn oracle_parse_format_pre_f1(s: &[u8]) -> ParseResult<'_> {
    let mut start_idx = None;
    let mut state = State::Percent;
    let mut assign = true;
    let mut width = None;
    let mut length = None;
    let mut conversion = None;
    for (i, c) in s.iter().enumerate() {
        if state == State::Percent {
            if *c == b'%' {
                start_idx = Some(i);
                state = State::Asterisk;
            }
        } else if matches!(state, State::Circumflex | State::ScanSet) {
            if *c == b'^' {
                if state == State::Circumflex {
                    let Some((Conversion::ScanSet(ScanSet { negative, .. }), _)) = &mut conversion
                    else {
                        unreachable!()
                    };
                    *negative = true;
                    state = State::ScanSet;
                } else {
                    err(s, start_idx);
                }
            } else if *c == b']' {
                if state == State::ScanSet {
                    let Some((_, old_i)) = &mut conversion else { unreachable!() };
                    *old_i = i;
                    break;
                } else {
                    err(s, start_idx);
                }
            } else {
                state = State::ScanSet;
                let Some((Conversion::ScanSet(ScanSet { chars, .. }), _)) = &mut conversion else {
                    unreachable!()
                };
                chars.push(*c);
            }
        } else if c.is_ascii_digit() {
            match state {
                State::Asterisk => {
                    width = Some((c - b'0') as usize);
                    state = State::Width;
                }
                State::Width => {
                    let Some(n) = width.as_mut() else { unreachable!() };
                    *n = *n * 10 + (c - b'0') as usize;
                }
                _ => err(s, start_idx),
            }
        } else if *c == b'*' {
            if state == State::Asterisk {
                assign = false;
                state = State::Width;
            } else {
                err(s, start_idx);
            }
        } else if let Some(len) = LengthMod::from_u8(*c) {
            match len {
                LengthMod::Short => match state {
                    State::Asterisk | State::Width => {
                        state = State::H;
                    }
                    State::H => {
                        length = Some(LengthMod::Char);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                LengthMod::Long => match state {
                    State::Asterisk | State::Width => {
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
                State::Asterisk | State::Width | State::Conversion => {}
                State::H => length = Some(LengthMod::Short),
                State::L => length = Some(LengthMod::Long),
                _ => err(s, start_idx),
            }
            let is_set = conv.is_set();
            conversion = Some((conv, i));
            if is_set {
                state = State::Circumflex;
            } else {
                break;
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
                    assign,
                    width,
                    length,
                    conversion,
                    leading_space: false,
                    trailing_space: false,
                }),
                remaining: Some(&s[last_idx + 1..]),
            }
        } else {
            err(s, Some(start_idx))
        }
    } else {
        ParseResult {
            prefix: s,
            conversion_spec: None,
            remaining: None,
        }
    }
}

#[cfg(test)]
fn oracle_parse_specs_pre_f1(mut remaining: &[u8]) -> Vec<ConversionSpec> {
    let mut specs = vec![];
    loop {
        let res = oracle_parse_format_pre_f1(remaining);
        if let Some(rem) = res.remaining {
            remaining = rem;
            let mut cs = res.conversion_spec.unwrap();
            cs.leading_space = res.prefix.iter().any(u8::is_ascii_whitespace);
            specs.push(cs);
        } else {
            if res.prefix.iter().any(u8::is_ascii_whitespace)
                && let Some(last) = specs.last_mut()
            {
                last.trailing_space = true;
            }
            break specs;
        }
    }
}

/// Every `%`-bearing byte-string literal in the frozen corpus.
///
/// Deliberately **over-approximate** — it sweeps in `printf` formats too. That
/// is safe and strictly stronger: the differential asserts only over inputs the
/// OLD parser accepts, so a wider input set can only add cases.
#[cfg(test)]
fn harvest_corpus_format_literals() -> Vec<(String, String)> {
    fn walk(dir: &std::path::Path, out: &mut Vec<(String, String)>) {
        let Ok(rd) = std::fs::read_dir(dir) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "rs") {
                let Ok(text) = std::fs::read_to_string(&p) else { continue };
                let prog = p
                    .strip_prefix(corpus_root())
                    .ok()
                    .and_then(|r| r.components().next().map(|c| c.as_os_str().to_string_lossy().into_owned()))
                    .unwrap_or_default();
                // `b"...\0"` literals, the shape C2Rust emits for format strings.
                for (idx, _) in text.match_indices("b\"") {
                    let rest = &text[idx + 2..];
                    let Some(end) = rest.find('"') else { continue };
                    let lit = &rest[..end];
                    if lit.contains('%') {
                        out.push((prog.clone(), lit.replace("\\0", "")));
                    }
                }
            }
        }
    }
    let mut out = Vec::new();
    walk(corpus_root(), &mut out);
    out.sort();
    out.dedup();
    out
}

#[cfg(test)]
fn corpus_root() -> &'static std::path::Path {
    std::path::Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../../benchmarks/rs-crown"))
}

/// **G1 — the differential.** Everything the old parser accepted parses
/// identically under the fixed parser.
///
/// This is the assertion the license rests on. It also reports H1's three
/// censuses, so both F-2 sub-shapes get corpus-presence numbers regardless of
/// how the differential lands.
#[test]
fn the_fix_only_changes_executions_that_previously_panicked() {
    let harvest = harvest_corpus_format_literals();
    // The probe rule: a differential over an empty harvest proves nothing.
    assert!(
        !harvest.is_empty(),
        "no format literals harvested from {} — the differential would pass \
         vacuously",
        corpus_root().display()
    );

    let mut rejected: Vec<(String, String)> = Vec::new();
    let mut agreed = 0usize;
    for (prog, lit) in &harvest {
        let bytes = lit.as_bytes();
        // Rejection IS a panic in the old parser, so the oracle runs caught.
        let Ok(before) = std::panic::catch_unwind(|| oracle_parse_specs_pre_f1(bytes)) else {
            rejected.push((prog.clone(), lit.clone()));
            continue;
        };
        let after = std::panic::catch_unwind(|| parse_specs(bytes));
        let Ok(after) = after else {
            panic!("F-1 REGRESSION: {prog} {lit:?} parsed before the fix and panics after")
        };
        assert_eq!(
            before, after,
            "F-1 REGRESSION: {prog} {lit:?} parses DIFFERENTLY after the fix"
        );
        agreed += 1;
    }

    // H1(i) population, H1(ii) rejection census.
    println!("H1(i)  harvested %-bearing literals: {}", harvest.len());
    println!("H1(i)  old-parser ACCEPTED (differential population): {agreed}");
    println!("H1(ii) old-parser REJECTIONS: {}", rejected.len());
    for (prog, lit) in &rejected {
        println!("H1(ii)   {prog}: {lit:?}");
    }

    // H1(iii) syntactic counts, independent of any parser.
    let n_bracket_first = harvest.iter().filter(|(_, l)| l.contains("%[]")).count();
    let n_caret_bracket = harvest.iter().filter(|(_, l)| l.contains("%[^]")).count();
    println!("H1(iii) `%[]`-first shapes (F-2a, panics):        {n_bracket_first}");
    println!("H1(iii) `%[^]`-first shapes (F-2b, silent):       {n_caret_bracket}");
}

/// **G2 — the urlparser regression.** Exact parse, not merely "does not panic".
///
/// *Mutation-tested (Rider 4):* restoring `err(s, start_idx)` in the
/// non-leading-`^` arm fails this.
#[test]
fn f1_urlparser_scanset_parses_with_the_caret_as_an_ordinary_member() {
    let specs = parse_specs(b"%[^? | ^#]");
    assert_eq!(specs.len(), 1, "one conversion: {specs:?}");
    let Conversion::ScanSet(set) = &specs[0].conversion else {
        panic!("not a scanset: {specs:?}")
    };
    assert!(set.negative, "the LEADING `^` still negates: {specs:?}");
    assert_eq!(
        set.chars, b"? | ^#",
        "the non-leading `^` is an ordinary member, and every other byte is \
         preserved in order: {specs:?}"
    );
}

/// **The two F-2 shapes, witnessed — one panics, one MISPARSES SILENTLY.**
///
/// Pinned because they are categorically different and the difference decides
/// what a licence may cover. The F-1 micro-plan claimed both panicked; measured
/// (reviewer amendment H2), `%[^]abc]` **completes**, yielding an empty negated
/// set — so repairing it would change an execution that succeeds today, which
/// is outside any licence scoped to panics.
///
/// Both remain unfixed. This test is their record, not their repair.
#[test]
fn the_f2_scanset_shapes_behave_as_witnessed() {
    assert!(
        std::panic::catch_unwind(|| parse_specs(b"%[]abc]")).is_err(),
        "F-2a: `]` in the first position still panics — unfixed by design"
    );
    let quiet = std::panic::catch_unwind(|| parse_specs(b"%[^]abc]"))
        .expect("F-2b completes rather than panicking");
    let Conversion::ScanSet(set) = &quiet[0].conversion else {
        panic!("not a scanset: {quiet:?}")
    };
    assert!(set.negative && set.chars.is_empty(), "F-2b: empty negated set — the silent misparse: {quiet:?}");
}
