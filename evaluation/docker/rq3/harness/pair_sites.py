#!/usr/bin/env python3
"""RQ4's pair line (wave-6o relay 136 item 2, R774-4): of the raw-boundary pair sites (role
raw-view / primary, `<program>.raw-boundary-pairs.tsv`), how many the provided inputs EXECUTE, and
at how many both arguments denote one object.

A harness edit on a COPY of the emitted tree (never the emitted program): before each pair call site
the call becomes `{ crate::jobcrat_pair_note(K, &[ranges]); CALL }`, where each range is the
(address, size) an argument denotes (a raw pointer: its address and the pointee's size; a reference:
its address and the referent's size, a slice's whole length; `Option` of either), read without a
retag (`&raw const`). `jobcrat_pair_note` prints `jobcrat-pair site=K same=0|1` to stderr once per
(site, verdict): `same=1` when the raw-view argument's range overlaps a peer's (the pair receipt's
other members). Sites map onto the emitted calls by (caller, callee, ordinal of the call in the
caller's body), the input's order; an argument the scan cannot root in a variable is not checked
(reported); a site whose call is not found is `unmapped`.

usage: pair_sites.py instrument <census-dir> <program> <out-tree-dir>   -> writes the copy + sites.tsv
       pair_sites.py read <sites.tsv> <stderr files...>                -> executed / same-object
"""
import collections, csv, glob, os, re, shutil, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from miri_oracle import mask  # noqa: E402

RUNTIME = r'''
// harness (wave-6o relay 136 item 2; NOT the emitted program): the pair-site recorder
#[allow(dead_code)]
pub mod jobcrat_pair_rt {
    pub static mut SEEN: Vec<(u32, bool)> = Vec::new();
}
pub trait CratPairRange { fn jobcrat_pair_range(&self) -> (usize, usize); }
impl<T> CratPairRange for *const T {
    fn jobcrat_pair_range(&self) -> (usize, usize) { (self.addr(), core::mem::size_of::<T>().max(1)) }
}
impl<T> CratPairRange for *mut T {
    fn jobcrat_pair_range(&self) -> (usize, usize) { (self.addr(), core::mem::size_of::<T>().max(1)) }
}
impl<T: ?Sized> CratPairRange for &T {
    fn jobcrat_pair_range(&self) -> (usize, usize) {
        let p: *const T = &raw const **self;
        (p.addr(), unsafe { core::mem::size_of_val_raw(p) }.max(1))
    }
}
impl<T: ?Sized> CratPairRange for &mut T {
    fn jobcrat_pair_range(&self) -> (usize, usize) {
        let p: *const T = &raw const **self;
        (p.addr(), unsafe { core::mem::size_of_val_raw(p) }.max(1))
    }
}
impl<T: CratPairRange> CratPairRange for Option<T> {
    fn jobcrat_pair_range(&self) -> (usize, usize) { self.as_ref().map_or((0, 0), |p| p.jobcrat_pair_range()) }
}
impl<T, const N: usize> CratPairRange for [T; N] {
    fn jobcrat_pair_range(&self) -> (usize, usize) {
        let p: *const [T; N] = &raw const *self;
        (p.addr(), core::mem::size_of::<[T; N]>().max(1))
    }
}
pub fn jobcrat_pair_range<P: CratPairRange + ?Sized>(p: &P) -> (usize, usize) { p.jobcrat_pair_range() }
/// `ranges[0]` is the raw-view argument, the rest its peers; (0, 0) = null / unchecked
#[allow(static_mut_refs)]
pub fn jobcrat_pair_note(site: u32, ranges: &[(usize, usize)]) {
    let (a, n) = ranges[0];
    let same = a != 0 && ranges[1..].iter().any(|&(b, m)| b != 0 && a < b + m && b < a + n);
    unsafe {
        if !jobcrat_pair_rt::SEEN.contains(&(site, same)) {
            jobcrat_pair_rt::SEEN.push((site, same));
            eprintln!("jobcrat-pair site={} same={}", site, same as u8);
        }
    }
}
'''


def module_spans(mk):
    """[(fn name, module path tuple, body start, body end)] from the masked text."""
    out, stack, depth, i = [], [], 0, 0
    tok = re.compile(r"\bmod\s+(\w+)\s*\{|\bfn\s+(\w+)\b|[{};]")
    pending_fn = None
    fn_open = []
    for m in tok.finditer(mk):
        if m.group(1):
            depth += 1
            stack.append((m.group(1), depth))
        elif m.group(2):
            pending_fn = m.group(2)
        elif m.group(0) == ";":
            pending_fn = None
        elif m.group(0) == "{":
            depth += 1
            if pending_fn:
                fn_open.append((pending_fn, tuple(n for n, _ in stack), m.start(), depth))
                pending_fn = None
        else:
            if fn_open and fn_open[-1][3] == depth:
                name, mods, start, _ = fn_open.pop()
                out.append((name, mods, start, m.start()))
            if stack and stack[-1][1] == depth:
                stack.pop()
            depth -= 1
    return out


ROOT = re.compile(r"^[\s(&*]*(?:mut\s+)?[\s(*]*(?:core::ptr::from_(?:mut|ref)\(\s*&(?:mut\s+)?\*?\s*)?(\w+)\)*"
                  r"(?:\s*\.\s*(?:as_mut_ptr|as_ptr|as_deref_mut|as_deref|as_mut|as_ref)\(\s*\))*\)*"
                  r"(?:\s+as\s+\*(?:mut|const)\s+[\w:<>]+)*\s*\)*\s*$", re.S)


PURE_CALLS = {"from_ref", "from_mut", "from_raw_parts", "from_raw_parts_mut", "as_ptr", "as_mut_ptr", "offset", "add", "wrapping_add",
              "wrapping_sub", "wrapping_offset", "cast", "cast_mut", "cast_const", "Some"}


def root_of(arg):
    """A variable the argument is rooted in, else the argument itself when it is side-effect free
    (places, field loads, casts, pointer arithmetic, `from_ref` views): the native recorder may
    evaluate it a second time."""
    m = ROOT.match(arg)
    if m and not re.fullmatch(r"\d+|None|true|false", m.group(1)):
        return m.group(1)
    mk = mask(arg)
    if re.search(r"[{};?!]|(?<![=!<>])=(?!=)", mk) or not re.search(r"[A-Za-z_]", mk):
        return None
    if any(c not in PURE_CALLS for c in re.findall(r"(\w+)\s*\(", mk)):
        return None
    if re.fullmatch(r"\s*(None|0|\d+ as [\w:*\s]+)\s*", arg):
        return None
    return "(" + " ".join(arg.split()) + ")"


def split_args(mk, open_pos):
    depth, j, commas = 0, open_pos + 1, []
    while j < len(mk):
        c = mk[j]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                break
            depth -= 1
        elif c == "," and depth == 0:
            commas.append(j)
        j += 1
    bounds = [open_pos + 1] + [c + 1 for c in commas] + [j]
    return [(bounds[k], commas[k] if k < len(commas) else j) for k in range(len(bounds) - 1)], j


DROP = set()   # sites whose argument types the recorder does not cover (dropped after a compile check)


def instrument(census, program, out_dir):
    rows = []
    f = os.path.join(census, f"{program}.raw-boundary-pairs.tsv")
    for r in csv.DictReader(open(f), delimiter="\t"):
        if r["role"] in ("raw-view", "primary"):
            m = re.search(r":(\d+):(\d+):", r["site"])
            peers = sorted({int(x) for p in r["peer_receipts"].split(";") for x in re.findall(r"(\d+)/\d+", p.split(":")[0])}
                           - {int(r["argument_index"])})
            rows.append(dict(r, line=int(m.group(1)) if m else 0, col=int(m.group(2)) if m else 0, peers=peers))
    tree = os.path.join(census, "emitted-trees", program)
    if os.path.exists(out_dir):
        shutil.rmtree(out_dir)
    shutil.copytree(tree, out_dir)
    root = next(os.path.join(out_dir, f) for f in ("lib.rs", "c2rust-lib.rs") if os.path.exists(os.path.join(out_dir, f)))
    text = open(root).read()
    mk = mask(text)
    fns = module_spans(mk)
    groups = collections.defaultdict(list)
    for k, r in enumerate(rows):
        r["k"] = k
        groups[(r["caller"], r["callee"])].append(r)
    edits, sites = [], []
    for (caller, callee), rs in groups.items():
        cparts = caller.split("::")
        cname, cmods = cparts[-1], tuple(cparts[:-1])
        bodies = [(s, e) for (n, mods, s, e) in fns
                  if n in (cname, "__jobcrat_safe_" + cname) and mods[-len(cmods):] == cmods] if cmods else \
                 [(s, e) for (n, mods, s, e) in fns if n in (cname, "__jobcrat_safe_" + cname)]
        callee_name = callee.split("::")[-1]
        calls = []
        for s, e in bodies:
            for m in re.finditer(r"(?<![\w.])(?:[\w:]*::)?(?:__jobcrat_safe_)?" + re.escape(callee_name) + r"\s*\(", mk[s:e]):
                pre = mk[max(0, s + m.start() - 4):s + m.start()]
                if "fn " in pre:
                    continue
                calls.append(s + m.start())
        # a call through the exposure wrapper and its twin both name the callee: keep the twin's
        calls = sorted(set(calls))
        for r in rs:
            # the input's call ordinal of this site within (caller, callee)
            ordinal = sorted({(x["line"], x["col"]) for x in rs if x["argument_index"] == r["argument_index"]}).index((r["line"], r["col"]))
            if ordinal >= len(calls):
                sites.append((r["k"], r, "unmapped", "-"))
                continue
            cpos = calls[ordinal]
            open_pos = mk.index("(", cpos)
            args, close = split_args(mk, open_pos)
            idx = [int(r["argument_index"])] + r["peers"]
            if max(idx) >= len(args):
                sites.append((r["k"], r, "unmapped", "-"))
                continue
            roots = [root_of(text[a:b]) for a, b in (args[i] for i in idx)]
            if roots[0] is None or all(x is None for x in roots[1:]):
                sites.append((r["k"], r, "unchecked", ",".join(str(x) for x in roots)))
                continue
            roots = [None if (r["k"], j) in DROP else x for j, x in enumerate(roots)]
            if roots[0] is None or all(x is None for x in roots[1:]):
                sites.append((r["k"], r, "unchecked", "type"))
                continue
            ranges = ", ".join(f"crate::jobcrat_pair_range(&{x})" if x else "(0usize, 0usize)" for x in roots)
            edits.append((cpos, close + 1, f"{{ crate::jobcrat_pair_note({r['k']}, &[{ranges}]); ", " }"))
            sites.append((r["k"], r, "instrumented", ",".join(str(x) for x in roots)))
    # one wrapper per call: several sites at one call note in sequence
    by_call = collections.defaultdict(list)
    for a, b, pre, post in edits:
        by_call[(a, b)].append(pre)
    out, i = [], 0
    for (a, b) in sorted(by_call):
        if a < i:
            continue
        out.append(text[i:a]); out.append("".join(by_call[(a, b)]) + text[a:b] + " }" * len(by_call[(a, b)])); i = b
    out.append(text[i:])
    text = "".join(out)
    if "#![feature(layout_for_ptr)]" not in text:
        text = "#![feature(layout_for_ptr)]\n" + text
    open(root, "w").write(text + RUNTIME)
    with open(os.path.join(out_dir, "pair-sites.tsv"), "w") as t:
        t.write("k\tcaller\tcallee\targument_index\trole\tsite\tstate\troots\n")
        for k, r, state, roots in sorted(sites, key=lambda s: s[0]):
            t.write(f"{k}\t{r['caller']}\t{r['callee']}\t{r['argument_index']}\t{r['role']}\t{r['site']}\t{state}\t{roots}\n")
    return sites


def read(sites_tsv, stderrs):
    sites = list(csv.DictReader(open(sites_tsv), delimiter="\t"))
    seen = collections.defaultdict(set)
    for f in stderrs:
        for m in re.finditer(r"jobcrat-pair site=(\d+) same=([01])", open(f, errors="replace").read()):
            seen[int(m.group(1))].add(int(m.group(2)))
    st = collections.Counter(s["state"] for s in sites)
    executed = [s for s in sites if int(s["k"]) in seen]
    same = [s for s in sites if 1 in seen.get(int(s["k"]), set())]
    return dict(sites=len(sites), instrumented=st["instrumented"], unchecked=st["unchecked"], unmapped=st["unmapped"],
                executed=len(executed), same_object=len(same)), same


def checked(census, program, out_dir, rounds=4):
    """Instrument, type-check the copy (`--emit=metadata`), drop the sites at failing lines, repeat."""
    import runtime_census as rc, subprocess
    for _ in range(rounds):
        sites = instrument(census, program, out_dir)
        root = next(os.path.join(out_dir, f) for f in ("lib.rs", "c2rust-lib.rs") if os.path.exists(os.path.join(out_dir, f)))
        cmd = ["rustc", rc.TOOLCHAIN, "--edition", "2021", "--crate-type", "lib", "--emit=metadata", *rc.RUST_FLAGS,
               "-L", f"dependency={rc.DEPS}", *rc.externs(), root, "-o", os.path.join(out_dir, "check.rmeta")]
        p = subprocess.run(cmd, capture_output=True, text=True)
        if p.returncode == 0:
            return sites
        text = open(root).read().split("\n")
        bad = set()
        for m in re.finditer(r"--> [^:]+:(\d+):(\d+)", p.stderr):
            line, col = text[int(m.group(1)) - 1], int(m.group(2)) - 1
            # the note whose argument list holds the column, and the range there
            for n in re.finditer(r"jobcrat_pair_note\((\d+), &\[", line):
                end = line.find("]);", n.end())
                if n.end() <= col <= end:
                    starts = [x.start() for x in re.finditer(r"crate::jobcrat_pair_range\(|\(0usize, 0usize\)", line[n.end():end])]
                    j = max(i for i, st in enumerate(starts) if n.end() + st <= col)
                    bad.add((int(n.group(1)), j))
        if not bad:
            open(os.path.join(out_dir, "check.log"), "w").write(p.stderr)
            raise SystemExit(f"{program}: the instrumented copy fails outside the recorder (check.log)")
        DROP.update(bad)
    raise SystemExit(f"{program}: still failing after {rounds} rounds")


if __name__ == "__main__":
    if sys.argv[1] == "instrument":
        s = checked(sys.argv[2], sys.argv[3], sys.argv[4])
        print(collections.Counter(x[2] for x in s), "dropped(type):", len(DROP))
    else:
        print(read(sys.argv[2], sys.argv[3:])[0])
