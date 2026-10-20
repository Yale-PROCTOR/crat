#!/usr/bin/env python3
"""Pass C, "oracle extents": a Miri-copy-only harness edit that gives every slice whose length the
translation fabricated (FALLBACK_SLICE_EXTENT) its real extent, so that Miri checks the true bound.
Never in the emitted program.

1. The registry. The program's calls of malloc / calloc / realloc / free / strdup / strndup /
   posix_memalign (and their function-pointer values) go to harness wrappers that call the real
   function and record (base address, size) with `addr()` (no integer-to-pointer cast); realloc
   moves the entry, free removes it. The libc symbols themselves are not defined, so std's own
   allocations never enter. The harness's argv strings are registered by the harness's main.
2. The substitution. Every construction whose length argument is `FALLBACK_SLICE_EXTENT`
   (`from_raw_parts(_mut)`, `slice_from_raw_parts(_mut)`, `SliceCursor::from_raw_parts`) becomes
       { let __jobcrat_bK = <base>; CALLEE(__jobcrat_bK, crate::jobcrat_miri_extent(__jobcrat_bK, K, hint)) }
   `jobcrat_miri_extent` returns the TRUE remaining extent (base + size - p) / size_of::<T>() of the
   allocation holding p: first the static hint (a byte-string literal's own length; the place of
   a `&PLACE` / `PLACE.as_ptr()` base: its address and size, used only if p lies inside it), then
   the registry; otherwise it keeps FALLBACK_SLICE_EXTENT, prints `jobcrat-miri-unresolved site=K`
   once, and the construction stays class (d).
"""
import re

ALLOC_NAMES = ("malloc", "calloc", "realloc", "free", "strdup", "strndup", "posix_memalign")
CALLEES = re.compile(r"(?:^|::)(from_raw_parts|from_raw_parts_mut|slice_from_raw_parts|slice_from_raw_parts_mut)$")


def mask(text):
    """`text` with the contents of string / char literals and comments blanked (same length),
    so that parens, commas and names are only matched in code."""
    out = list(text)
    i, n = 0, len(text)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "
    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth += 1; j += 2
                elif text.startswith("*/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif (c == "r" or text.startswith("br", i)) and re.match(r"b?r#*\"", text[i:i + 12]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            m = re.match(r"b?r(#*)\"", text[i:])
            close = "\"" + m.group(1)
            j = text.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            blank(i + m.end(), j - len(close))
            i = j
        elif c == "\"" or (c == "b" and text.startswith("b\"", i) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_"))):
            j = i + (2 if c == "b" else 1)
            start = j
            while j < n and text[j] != "\"":
                j += 2 if text[j] == "\\" else 1
            blank(start, j)
            i = j + 1
        elif c == "'" or (c == "b" and text.startswith("b'", i) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_"))):
            j = i + (2 if c == "b" else 1)
            m = re.match(r"(\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'", text[j:j + 12])
            if m:
                blank(j, j + m.end() - 1)
                i = j + m.end()
            else:
                i += 1  # a lifetime / label
        else:
            i += 1
    return "".join(out)


def _byte_len(lit):
    """The length of a Rust byte-string literal's contents."""
    n, i = 0, 0
    while i < len(lit):
        if lit[i] == "\\":
            nx = lit[i + 1]
            if nx == "x":
                i += 4
            elif nx == "\n":  # a line continuation: skips the newline and leading whitespace
                i += 2
                while i < len(lit) and lit[i] in " \t\n\r":
                    i += 1
                continue
            else:
                i += 2
            n += 1
        else:
            n += len(lit[i].encode())
            i += 1
    return n


LIT = re.compile(r'^\s*\(?\s*b"((?:[^"\\]|\\.|\\\n)*)"\s*\)?\s+as\s+\*const\s+u8(?:\s+as\s+\*(?:const|mut)\s+[\w:]+)*\s*$', re.S)
PLACE_ADDR = re.compile(r"^\s*&(?:mut\s+)?(?P<place>[\w.()\[\]* ]+?)\s+as\s+\*", re.S)
PLACE_AS_PTR = re.compile(r"^\s*(?P<place>[\w.()\[\]* ]+?)\s*\.\s*as_(?:mut_)?ptr\s*\(\s*\)", re.S)
SIMPLE_PLACE = re.compile(r"^(?:\(\*\s*\w+\)|\w+)(?:\s*\.\s*\w+|\s*\[\s*[\w ]+\s*\])*$")


def hint_for(arg0):
    """-> ('lit', bytes) | ('place', place) | None."""
    m = LIT.match(arg0)
    if m:
        return ("lit", _byte_len(m.group(1)))
    m = PLACE_ADDR.match(arg0)
    if m and SIMPLE_PLACE.match(m.group("place").strip()):
        return ("place", m.group("place").strip())
    m = PLACE_AS_PTR.match(arg0)
    if m and SIMPLE_PLACE.match(m.group("place").strip()):
        return ("slice", m.group("place").strip())
    return None


def substitute(text, first_site=0):
    """-> (new text, sites [(k, line, kind)], unhandled [(line, why)])."""
    mk = mask(text)
    occ = [m.start() for m in re.finditer(r"\bFALLBACK_SLICE_EXTENT\b", mk)]
    edits = {}   # open-paren pos -> (call_start, close_pos, callee_text, arg0_span, k, hint)
    sites, unhandled = [], []
    k = first_site
    import bisect
    nls = [m.start() for m in re.finditer("\n", text)]
    line_of = lambda pos: bisect.bisect_left(nls, pos) + 1
    for pos in occ:
        if re.search(r"const\s+$", mk[max(0, pos - 20):pos]):
            continue
        depth, j = 0, pos - 1
        while j >= 0:
            ch = mk[j]
            if ch in ")]}":
                depth += 1
            elif ch in "([{":
                if depth == 0:
                    break
                depth -= 1
            elif ch == ";" and depth == 0:
                j = -1
                break
            j -= 1
        # a parenthesised `(FALLBACK_SLICE_EXTENT)` is not the call: step out of it
        while j > 0 and mk[j] == "(" and re.fullmatch(r"\(\s*(?:crate::)?FALLBACK_SLICE_EXTENT\s*", mk[j:pos + len("FALLBACK_SLICE_EXTENT")]) \
                and not re.search(r"[\w:]\s*$", mk[max(0, j - 80):j]):
            depth, j = 0, j - 1
            while j >= 0:
                ch = mk[j]
                if ch in ")]}":
                    depth += 1
                elif ch in "([{":
                    if depth == 0:
                        break
                    depth -= 1
                elif ch == ";" and depth == 0:
                    j = -1
                    break
                j -= 1
        if j < 0 or mk[j] != "(":
            unhandled.append((line_of(pos), "not-a-call-argument"))
            continue
        w0 = max(0, j - 200)
        m = re.search(r"([\w:]+)\s*$", mk[w0:j])
        callee = m.group(1) if m else ""
        if callee and not CALLEES.search(callee):
            unhandled.append((line_of(pos), f"callee:{callee}"))
            continue
        # the matching close paren and the depth-0 commas
        depth, e, commas = 0, j + 1, []
        while e < len(mk):
            ch = mk[e]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth == 0:
                    break
                depth -= 1
            elif ch == "," and depth == 0:
                commas.append(e)
            e += 1
        bounds = [j + 1] + [c + 1 for c in commas] + [e]
        args = [(bounds[a], (commas[a] if a < len(commas) else e)) for a in range(len(bounds) - 1)]
        args = [(a, b) for a, b in args if text[a:b].strip()]
        second = text[args[1][0]:args[1][1]] if len(args) == 2 else ""
        plain = re.fullmatch(r"\s*\(?\s*(?:crate::)?FALLBACK_SLICE_EXTENT\s*\)?\s*(?:as\s+usize\s*)?", second)
        # brotli's byte views: `FALLBACK_SLICE_EXTENT * size_of::<X>()` over a `*mut u8` base
        scaled = re.fullmatch(r"\s*(?:crate::)?FALLBACK_SLICE_EXTENT\s*\*\s*(.+?)\s*", second, re.S)
        if len(args) != 2 or not (plain or scaled) or (not callee and not plain):
            unhandled.append((line_of(pos), f"args:{len(args)}"))
            continue
        hint = hint_for(text[args[0][0]:args[0][1]])
        # a tuple `(ptr, FALLBACK)` (binn's counted-void pair) has no callee: the call start is the paren
        edits[j] = (w0 + m.start(1) if callee else j, e, callee, args[0], k, hint, scaled.group(1) if scaled and not plain else None)
        sites.append((k, line_of(pos), hint[0] if hint else "registry"))
        k += 1

    starts = sorted(edits)

    def render(a, b):
        out, i = [], a
        for p in starts:
            cs, ce, callee, (x0, x1), kk, hint, scale = edits[p]
            if cs < i or ce >= b:
                continue
            out.append(text[i:cs])
            base = render(x0, x1).strip()
            pre, post = "", ""
            if hint and hint[0] == "place":
                pre = f"let __jobcrat_h{kk} = Some(crate::jobcrat_miri_place(core::ptr::addr_of!({hint[1]}))); "
            elif hint and hint[0] == "slice":
                pre = f"let __jobcrat_h{kk} = Some(crate::jobcrat_miri_slice(&({hint[1]})[..])); "
            elif hint and hint[0] == "lit":
                post = f"let __jobcrat_h{kk} = Some((crate::JobcratMiriPtr::jobcrat_addr(&__jobcrat_b{kk}), {hint[1]}usize)); "
            else:
                pre = f"let __jobcrat_h{kk}: Option<(usize, usize)> = None; "
            ext = f"crate::jobcrat_miri_extent(&__jobcrat_b{kk}, {kk}, __jobcrat_h{kk})"
            if scale:
                ext = f"({ext} / ({scale}) * ({scale}))"
            out.append(f"{{ {pre}let __jobcrat_b{kk} = {base}; {post}{callee}(__jobcrat_b{kk}, {ext}) }}")
            i = ce + 1
        out.append(text[i:b])
        return "".join(out)

    return render(0, len(text)), sites, unhandled


def redirect_allocations(text):
    """The program's allocation calls and function-pointer values -> the harness wrappers.
    A name the program defines itself (a `fn` with a body) is left alone."""
    mk = mask(text)
    own = {n for n in ALLOC_NAMES if re.search(r"\bfn\s+" + n + r"\s*\([^;{]*\)[^;{]*\{", mk)}
    counts = {}
    edits = []
    for m in re.finditer(r"(?<![\w.])(?:libc::)?(" + "|".join(ALLOC_NAMES) + r")\b(\s*\(|\s+as\s+unsafe\s+extern\b)", mk):
        name = m.group(1)
        if name in own:
            continue
        before = mk[max(0, m.start() - 12):m.start()]
        if re.search(r"\bfn\s+$", before) or re.search(r"(?<!libc)::$", before):
            continue
        value = "as" in m.group(2)
        repl = f"crate::jobcrat_miri_{name}{'_c' if value else ''}"
        edits.append((m.start(), m.start(1) + len(name), repl))
        key = f"{name}{' (fn value)' if value else ''}"
        counts[key] = counts.get(key, 0) + 1
    out, i = [], 0
    for a, b, r in edits:
        out.append(text[i:a]); out.append(r); i = b
    out.append(text[i:])
    return "".join(out), counts, sorted(own)


def _item_spans(mk):
    """Spans of `static` / `const` items and `const fn` bodies: a non-const call is refused there."""
    spans = []
    def close_from(i, opener):
        depth = 0
        for j in range(i, len(mk)):
            c = mk[j]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
                if opener == "{" and depth == 0 and c == "}":
                    return j
            elif c == ";" and depth == 0 and opener == ";":
                return j
        return len(mk)
    for m in re.finditer(r"(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?(?:static|const)\s+(?:mut\s+)?\w+\s*:", mk):
        spans.append((m.start(), close_from(m.end(), ";")))
    for m in re.finditer(r"\bconst\s+(?:unsafe\s+)?(?:extern\s+\"C\"\s+)?fn\b", mk):
        b = mk.find("{", m.end())
        if b >= 0:
            spans.append((m.start(), close_from(b, "{")))
    return sorted(spans)


def register_literals(text):
    """`b"..." as *const u8` in code (not in a static / const item or a const fn) ->
    `crate::jobcrat_miri_lit(b"...") as *const u8`: the literal's static extent enters the registry
    each time the program evaluates it, so a literal handed down to a callee resolves there."""
    import bisect
    mk = mask(text)
    spans = _item_spans(mk)
    starts = [a for a, _ in spans]
    out, i, n = [], 0, 0
    for m in re.finditer(r'(?<![\w])b"(?:[^"\\]|\\.|\\\n)*"(?=\s+as\s+\*const\s+u8\b)', text, re.S):
        a = m.start()
        if mk[a:a + 2] != 'b"':
            continue
        k = bisect.bisect_right(starts, a) - 1
        if k >= 0 and spans[k][0] <= a <= spans[k][1]:
            continue
        out.append(text[i:a]); out.append("crate::jobcrat_miri_lit(" + m.group(0) + ")"); i = m.end(); n += 1
    out.append(text[i:])
    return "".join(out), n


SCALARS = {"u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
           "f32", "f64", "bool", "char", "size_t", "ssize_t", "off_t", "time_t"}


def register_local_arrays(text):
    """After each `let [mut] X: [T; N] = ...;` in code (not a const item / const fn), register X's
    extent: a pointer into a local array handed down to a callee then resolves there. Pass C runs
    with -Zmiri-address-reuse-rate=0, so an entry left behind by a dead frame never covers a new
    allocation."""
    import bisect
    mk = mask(text)
    spans = _item_spans(mk)
    starts = [a for a, _ in spans]
    edits = []
    # also a STRUCT local (`let x: S = ..` or `let x = S { .. }`): a pointer into
    # one of its array fields (libtree's `small_vec_u64_t::buf`, its `p` a self-pointer) resolves
    # to the struct's own extent
    pats = (r"\blet\s+(?:mut\s+)?(\w+)\s*:\s*\[",
            r"\blet\s+(?:mut\s+)?(\w+)\s*:\s*(?:crate::)?(?:[a-z_]\w*::)*[A-Za-z_]\w*\s*=",
            r"\blet\s+(?:mut\s+)?(\w+)\s*=\s*(?:crate::)?(?:[a-z_]\w*::)*[A-Za-z_]\w*\s*\{")
    found = sorted({m.start(): m for pat in pats for m in re.finditer(pat, mk)}.values(), key=lambda m: m.start())
    for m in found:
        k = bisect.bisect_right(starts, m.start()) - 1
        if k >= 0 and spans[k][0] <= m.start() <= spans[k][1]:
            continue
        depth, j = 0, m.end() - 1
        while j < len(mk):
            c = mk[j]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == ";" and depth == 0:
                break
            elif c == "=" and depth == 0 and mk[j + 1] != "=" and mk[j - 1] not in "=!<>":
                pass
            j += 1
        if j >= len(mk) or (m.re.pattern == pats[0] and "=" not in mk[m.end():j]):
            continue  # a declaration without an initializer is assigned later; its address is the same
        if m.re.pattern == pats[1]:
            ty = re.search(r":\s*([\w:]+)\s*=$", mk[m.start():m.end()])
            last = ty.group(1).split("::")[-1] if ty else ""
            if last in SCALARS or last.startswith("c_") or last.endswith("size_t") or re.fullmatch(r"u?int\d+_t", last):
                continue
        edits.append((j + 1, f" crate::jobcrat_miri_oracle::register_place(core::ptr::addr_of!({m.group(1)}));"))
    out, i = [], 0
    for pos, ins in edits:
        out.append(text[i:pos]); out.append(ins); i = pos
    out.append(text[i:])
    return "".join(out), len(edits)


ARGV_REGISTER = ("    for a in args.iter() { crate::jobcrat_miri_oracle::register(a.as_ptr().addr(), a.as_bytes_with_nul().len()); }"
                 "  // harness, pass C: the argv strings' extents\n")

RUNTIME = r'''
// harness, pass C (NOT the emitted program): the oracle-extent registry
#[allow(dead_code, static_mut_refs)]
pub mod jobcrat_miri_oracle {
    pub static mut REG: Vec<(usize, usize)> = Vec::new();
    pub static mut REPORTED: Vec<u32> = Vec::new();
    pub fn register(base: usize, size: usize) {
        unsafe {
            let end = base + size.max(1);
            REG.retain(|&(b, n)| b + n.max(1) <= base || end <= b);
            REG.push((base, size));
        }
    }
    pub fn unregister(base: usize) { unsafe { REG.retain(|e| e.0 != base) } }
    pub fn register_place<P>(p: *const P) { register(p.addr(), core::mem::size_of::<P>()) }
    pub fn lookup(a: usize) -> Option<(usize, usize)> {
        unsafe {
            REG.iter().copied().find(|&(b, n)| b <= a && a < b + n)
                .or_else(|| REG.iter().copied().find(|&(b, n)| a == b + n))
        }
    }
    pub fn unresolved(site: u32) {
        unsafe {
            if !REPORTED.contains(&site) {
                REPORTED.push(site);
                eprintln!("jobcrat-miri-unresolved site={}", site);
            }
        }
    }
}
pub trait JobcratMiriPtr {
    fn jobcrat_addr(&self) -> usize;
    fn jobcrat_elem(&self) -> usize;
    fn jobcrat_void(&self) -> *mut libc::c_void;
}
impl<T> JobcratMiriPtr for *const T {
    fn jobcrat_addr(&self) -> usize { self.addr() }
    fn jobcrat_elem(&self) -> usize { core::mem::size_of::<T>() }
    fn jobcrat_void(&self) -> *mut libc::c_void { *self as *mut libc::c_void }
}
impl<T> JobcratMiriPtr for *mut T {
    fn jobcrat_addr(&self) -> usize { self.addr() }
    fn jobcrat_elem(&self) -> usize { core::mem::size_of::<T>() }
    fn jobcrat_void(&self) -> *mut libc::c_void { *self as *mut libc::c_void }
}
// a base that is a reference coerced to the raw parameter at the call: its address, no retag
impl<T> JobcratMiriPtr for &T {
    fn jobcrat_addr(&self) -> usize { (&raw const **self).addr() }
    fn jobcrat_elem(&self) -> usize { core::mem::size_of::<T>() }
    fn jobcrat_void(&self) -> *mut libc::c_void { (&raw const **self) as *mut libc::c_void }
}
impl<T> JobcratMiriPtr for &mut T {
    fn jobcrat_addr(&self) -> usize { (&raw const **self).addr() }
    fn jobcrat_elem(&self) -> usize { core::mem::size_of::<T>() }
    fn jobcrat_void(&self) -> *mut libc::c_void { (&raw const **self) as *mut libc::c_void }
}
pub fn jobcrat_miri_slice<T>(s: &[T]) -> (usize, usize) { (s.as_ptr().addr(), core::mem::size_of_val(s)) }
// harness, pass C: a byte-string literal evaluated in the program registers its static extent
pub fn jobcrat_miri_lit<const N: usize>(s: &'static [u8; N]) -> &'static [u8; N] {
    jobcrat_miri_oracle::register(s.as_ptr().addr(), N);
    s
}
pub trait JobcratMiriSize: Copy { fn jobcrat_usize(self) -> usize; }
macro_rules! jobcrat_miri_size { ($($t:ty),*) => { $(impl JobcratMiriSize for $t { fn jobcrat_usize(self) -> usize { self as usize } })* } }
jobcrat_miri_size!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);
pub fn jobcrat_miri_place<P: ?Sized>(p: *const P) -> (usize, usize) {
    (p.addr(), unsafe { core::mem::size_of_val_raw(p) })
}
pub fn jobcrat_miri_extent<P: JobcratMiriPtr>(p: &P, site: u32, hint: Option<(usize, usize)>) -> usize {
    let (a, e) = (p.jobcrat_addr(), p.jobcrat_elem());
    if e == 0 { return crate::FALLBACK_SLICE_EXTENT; }
    if let Some((b, n)) = hint {
        if b <= a && a <= b + n { return (b + n - a) / e; }
    }
    match jobcrat_miri_oracle::lookup(a) {
        Some((b, n)) => (b + n - a) / e,
        None => { jobcrat_miri_oracle::unresolved(site); crate::FALLBACK_SLICE_EXTENT }
    }
}
pub unsafe fn jobcrat_miri_malloc<N: JobcratMiriSize>(n: N) -> *mut libc::c_void {
    let n = n.jobcrat_usize();
    let p = libc::malloc(n);
    if !p.is_null() { jobcrat_miri_oracle::register(p.addr(), n); }
    p
}
pub unsafe fn jobcrat_miri_calloc<N: JobcratMiriSize, M: JobcratMiriSize>(a: N, b: M) -> *mut libc::c_void {
    let (a, b) = (a.jobcrat_usize(), b.jobcrat_usize());
    let p = libc::calloc(a, b);
    if !p.is_null() { jobcrat_miri_oracle::register(p.addr(), a * b); }
    p
}
pub unsafe fn jobcrat_miri_realloc<P: JobcratMiriPtr, N: JobcratMiriSize>(p: P, n: N) -> *mut libc::c_void {
    let (old, n) = (p.jobcrat_void(), n.jobcrat_usize());
    let q = libc::realloc(old, n);
    if !q.is_null() {
        if !old.is_null() { jobcrat_miri_oracle::unregister(old.addr()); }
        jobcrat_miri_oracle::register(q.addr(), n);
    } else if n == 0 && !old.is_null() {
        jobcrat_miri_oracle::unregister(old.addr());
    }
    q
}
pub unsafe fn jobcrat_miri_free<P: JobcratMiriPtr>(p: P) {
    let p = p.jobcrat_void();
    if !p.is_null() { jobcrat_miri_oracle::unregister(p.addr()); }
    libc::free(p)
}
pub unsafe fn jobcrat_miri_strdup<P: JobcratMiriPtr>(s: P) -> *mut libc::c_char {
    extern "C" { fn strdup(_: *const libc::c_char) -> *mut libc::c_char; }
    let q = strdup(s.jobcrat_void() as *const libc::c_char);
    if !q.is_null() { jobcrat_miri_oracle::register(q.addr(), libc::strlen(q) + 1); }
    q
}
pub unsafe fn jobcrat_miri_strndup<P: JobcratMiriPtr, N: JobcratMiriSize>(s: P, n: N) -> *mut libc::c_char {
    extern "C" { fn strndup(_: *const libc::c_char, _: usize) -> *mut libc::c_char; }
    let q = strndup(s.jobcrat_void() as *const libc::c_char, n.jobcrat_usize());
    if !q.is_null() { jobcrat_miri_oracle::register(q.addr(), libc::strlen(q) + 1); }
    q
}
pub unsafe fn jobcrat_miri_posix_memalign<P: JobcratMiriPtr, A: JobcratMiriSize, N: JobcratMiriSize>(pp: P, a: A, n: N) -> libc::c_int {
    let pp = pp.jobcrat_void() as *mut *mut libc::c_void;
    let n = n.jobcrat_usize();
    let r = libc::posix_memalign(pp, a.jobcrat_usize(), n);
    if r == 0 { jobcrat_miri_oracle::register((*pp).addr(), n); }
    r
}
pub unsafe extern "C" fn jobcrat_miri_malloc_c(n: libc::c_ulong) -> *mut libc::c_void { jobcrat_miri_malloc(n) }
pub unsafe extern "C" fn jobcrat_miri_calloc_c(a: libc::c_ulong, b: libc::c_ulong) -> *mut libc::c_void { jobcrat_miri_calloc(a, b) }
pub unsafe extern "C" fn jobcrat_miri_realloc_c(p: *mut libc::c_void, n: libc::c_ulong) -> *mut libc::c_void { jobcrat_miri_realloc(p, n) }
pub unsafe extern "C" fn jobcrat_miri_free_c(p: *mut libc::c_void) { jobcrat_miri_free(p) }
'''


def apply(body):
    """-> (body, receipt lines). `body` is the Miri project's main.rs text (tree + driver + shim)."""
    if not re.search(r"const FALLBACK_SLICE_EXTENT: usize", mask(body)):
        # no fabricated-extent construction in the tree: nothing to substitute, the run is pass A's
        return body, ["pass C: the tree declares no FALLBACK_SLICE_EXTENT; unchanged"], [], []
    body, counts, own = redirect_allocations(body)
    body, sites, unhandled = substitute(body)
    body, nlit = register_literals(body)
    body, narr = register_local_arrays(body)
    body = "#![feature(layout_for_ptr)]\n" + body
    body = body.replace("    argv.push(core::ptr::null_mut());\n",
                        "    argv.push(core::ptr::null_mut());\n" + ARGV_REGISTER, 1)
    body += RUNTIME
    kinds = {}
    for _, _, kd in sites:
        kinds[kd] = kinds.get(kd, 0) + 1
    rec = [f"pass C: allocation calls redirected: {counts or '-'}; program-defined (left): {own or '-'}",
           f"pass C: fallback constructions substituted: {len(sites)} ({kinds}); unhandled: {len(unhandled)}",
           f"pass C: byte-string literals registered where evaluated: {nlit}",
           f"pass C: local arrays registered at their declaration: {narr}"]
    rec += [f"pass C: unhandled line {ln}: {why}" for ln, why in unhandled]
    return body, rec, sites, unhandled
