#!/usr/bin/env python3
"""a1.py -- analysis-fanout relay 148, task A1: libzahl T2 (full_deref) input -> ours, site-level match and attribution.
Read-only on everything outside this directory. Single process, no compiler.
usage: python3 a1.py --write  (writes a1-sites.tsv, a1-per-function.tsv here); --dump lists the unmatched sites"""
import collections, csv, os, re, sys

R = "scratch/analysis-fanout/r148"
OUT = os.path.join(R, "out/a1-libzahl")
CEN = "scratch/main/batch60sp/libzahl.raw-boundary-%s.tsv"
sys.dont_write_bytecode = True
sys.path.insert(0, R)
import mir_sites as M  # noqa: E402  (parse_file, scan_type, LOCAL)

PROG = "libzahl"
LOC = re.compile(r"(?<![A-Za-z0-9_])_(\d+)\b")

_src_cache = {}


def span_text(span):
    m = re.match(r"(.+):(\d+):(\d+): (\d+):(\d+)$", span)
    if not m:
        return "?"
    f, l0, c0, l1, c1 = m.group(1), *map(int, m.groups()[1:])
    if f not in _src_cache:
        try:
            _src_cache[f] = open(f, encoding="utf-8").read().splitlines()
        except OSError:
            _src_cache[f] = []
    L = _src_cache[f]
    if not L or l0 > len(L):
        return "?"
    if l0 == l1:
        return L[l0 - 1][c0 - 1:c1 - 1]
    return " ".join([L[l0 - 1][c0 - 1:]] + L[l0:l1 - 1] + [L[l1 - 1][:c1 - 1]]).strip()


def strip_types(s):
    """drop field / cast type annotations: '(*_1).3: u64)' -> '(*_1).3)'; '_5 as *mut T (PtrToPtr)' -> '_5 as (PtrToPtr)'."""
    out, i = [], 0
    while i < len(s):
        mf = re.match(r"\.(\d+): ", s[i:])
        if mf:
            out.append("." + mf.group(1))
            j = M.scan_type(s, i + mf.end())
            if j < 0:
                out.append(s[i + mf.end():])
                break
            i = j
            continue
        ma = re.match(r" as [^;]*? \(((?:PointerCoercion|PointerExposeProvenance|PointerWithExposedProvenance)\([^)]*\)|[A-Za-z]+)\)", s[i:])
        if ma:
            out.append(" as (%s)" % ma.group(1))
            i += ma.end()
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


class Fn:
    def __init__(self, path):
        self.decl, self.debug, self.blocks = M.parse_file(path)
        self.defs = collections.defaultdict(list)   # local -> [(stmt, span, bb, idx)]
        self.uses = collections.defaultdict(list)   # local -> [(stmt, bb, idx)]
        for idx, (bb, cl, st, span) in enumerate(self.blocks):
            if M.NONUSE.match(st) or st.startswith("FakeRead"):
                continue
            md = re.match(r"^_(\d+) = (.*)$", st)
            if md:
                self.defs[int(md.group(1))].append((md.group(2), span, bb, idx))
                rhs = md.group(2)
            else:
                rhs = st
            for m in LOC.finditer(rhs):
                self.uses[int(m.group(1))].append((st, bb, idx))
        self.sig = next((l for l in open(path, encoding="utf-8").read().splitlines() if re.match(r"^(unsafe )?(extern \"C\" )?fn ", l) or l.startswith("fn ")), "")
        self.nargs = len(re.findall(r"_(\d+): ", self.sig.split("->")[0]))
        self._norm = {}

    def norm(self, local, depth=0):
        if local in self.debug:
            return self.debug[local]
        if 1 <= local <= self.nargs:
            return "arg%d" % local
        if local == 0:
            return "ret"
        if depth > 8:
            return "_"
        key = (local, depth)
        if key in self._norm:
            return self._norm[key]
        self._norm[key] = "_"   # cycle guard
        alts = sorted(set(self.norm_rhs(rhs, span, depth + 1) for rhs, span, _, _ in self.defs.get(local, []))) or ["?"]
        r = "{" + "|".join(alts) + "}"
        self._norm[key] = r
        return r

    def norm_rhs(self, rhs, span, depth):
        rhs = rhs.rstrip().rstrip(";")
        rhs = re.sub(r"\s*-> \[.*$", "", rhs)                      # call continuation
        rhs = re.sub(r"\s*-> (bb\d+|unwind.*)$", "", rhs)
        mc = re.match(r"^const \{alloc\d+: [^}]*\}$", rhs)
        if mc:
            return "static(%s)" % span_text(span)
        rhs = re.sub(r"const \{alloc\d+: [^}]*\}", "static(?)", rhs)
        # callee path -> last segment (drop generic impl prefixes)
        rhs = re.sub(r"(?:[A-Za-z_][\w]*::|<[^()]*?>::)+([A-Za-z_]\w*)(::<[^()]*>)?\(", r"\1(", rhs)
        rhs = re.sub(r"\b(move|copy) ", "", rhs)
        rhs = strip_types(rhs)
        return LOC.sub(lambda m: self.norm(int(m.group(1)), depth), rhs)

    def norm_place(self, place):
        """the site's place with its root replaced by R, index locals normalized, types dropped."""
        p = strip_types(place)
        first = [True]

        def rep(m):
            if first[0]:
                first[0] = False
                return "R"
            return self.norm(int(m.group(1)))
        # root is the first local token in the place text (prefixes are only '(' and '*')
        return LOC.sub(rep, p)


def dump_dir(side):
    return "%s/mir/%s/%s/dump" % (R, side, PROG)


def fn_file(side, fn):
    return os.path.join(dump_dir(side), "lib.%s.SimplifyCfg-promote-consts.after.mir" % fn.replace("::", "-"))


_fns = {}


def getfn(side, fn):
    k = (side, fn)
    if k not in _fns:
        p = fn_file(side, fn)
        _fns[k] = Fn(p) if os.path.exists(p) else None
    return _fns[k]


def load_sites(side):
    rows = [r for r in csv.DictReader(open("%s/sites/%s-%s.tsv" % (R, side, PROG)), delimiter="\t")
            if r["phase"] == "promoted" and r["full_deref"] == "1"]
    for r in rows:
        F = getfn(side, r["function"])
        loc = int(r["local"][1:])
        r["root"] = F.norm(loc)
        r["proj"] = F.norm_place(r["place"])
        r["key"] = r["root"] + " :: " + r["proj"]
    return rows


def callee_of(F, st):
    m = re.match(r"^(?:_\d+ = )?([\w:<>\[\] ,&*]+?)\((.*)\) -> ", st)
    if not m:
        return None, None
    return m.group(1), m.group(2)


def resolve_callee(caller_fn, cpath):
    """'zcmp::zsignum' inside src::zcmp::zcmp -> src::zcmp::zsignum; 'src::zinit::zinit' kept."""
    last = cpath.split("::")[-1]
    mod = caller_fn.rsplit("::", 1)[0]
    cands = [cpath, "src::" + cpath, mod + "::" + last, "src::%s::%s" % (cpath.split("::")[0], last)]
    for c in cands:
        if os.path.exists(fn_file("ours", c)):
            return c
    return cpath


def formal_type(side, fn, idx):
    F = getfn(side, fn)
    if F is None:
        return "?"
    return F.decl.get(idx + 1, "?")


def consumer(F, local, seen=None, hops=0):
    """follow a reference / raw temporary through reborrows, moves and casts to its consumer.
    returns (kind, stmt, detail): kind in call / decl / option / other."""
    seen = seen or set()
    if local in seen or hops > 6:
        return ("other", "", "cycle")
    seen.add(local)
    if local in F.debug and hops > 0:
        return ("decl", "", F.debug[local])
    for st, bb, idx in F.uses.get(local, []):
        md = re.match(r"^_(\d+) = (.*)$", st)
        rhs = md.group(2) if md else st
        if " -> " in rhs and "(" in rhs:
            cp, args = callee_of(F, st)
            if cp:
                toks = [a.strip() for a in split_args(args)]
                pos = next((i for i, a in enumerate(toks) if re.search(r"(?<![\w])_%d\b" % local, a)), None)
                return ("call", st, (cp, pos))
        if md:
            dst = int(md.group(1))
            if re.match(r"^(Option::<.*>::)?Some\(|^std::option::Option::<.*>::Some", rhs) or "Option" in rhs and "Some" in rhs:
                return ("option", st, F.debug.get(dst, "_%d" % dst))
            if re.match(r"^&(mut |raw (mut|const) )?\(\*_%d\)" % local, rhs) or re.match(r"^(move |copy )?_%d( as .*)?$" % local, rhs) \
                    or re.match(r"^&(mut )?\(\*_%d\)" % local, rhs):
                if dst in F.debug:
                    return ("decl", st, F.debug[dst])
                return consumer(F, dst, seen, hops + 1)
            if dst in F.debug:
                return ("decl", st, F.debug[dst])
            return ("other", st, "assign")
        return ("other", st, "use")
    return ("other", "", "no-use")


def split_args(s):
    out, d, cur = [], 0, ""
    for c in s:
        if c in "([<{":
            d += 1
        elif c in ")]>}":
            d -= 1
        if c == "," and d == 0:
            out.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur)
    return out


def main():
    inp, ours = load_sites("input"), load_sites("ours")
    by = collections.defaultdict(lambda: ([], []))
    for r in inp:
        by[r["function"]][0].append(r)
    for r in ours:
        by[r["function"]][1].append(r)
    added, removed, matched = [], [], 0
    for fn, (a, b) in by.items():
        ca = collections.Counter(r["key"] for r in a)
        cb = collections.Counter(r["key"] for r in b)
        left = dict(ca)
        for r in b:
            if left.get(r["key"], 0) > 0:
                left[r["key"]] -= 1
                matched += 1
            else:
                added.append(r)
        left = dict(cb)
        for r in a:
            if left.get(r["key"], 0) > 0:
                left[r["key"]] -= 1
            else:
                removed.append(r)
    print("input %d ours %d matched %d added %d removed %d net %+d" % (len(inp), len(ours), matched, len(added), len(removed), len(added) - len(removed)))
    return inp, ours, added, removed


if __name__ == "__main__" and "--dump" in sys.argv:
    inp, ours, added, removed = main()
    if True:
        for tag, L in (("ADD", added), ("REM", removed)):
            for r in L:
                print(tag, r["function"], "|", r["key"], "|", r["stmt"][:110])


def classify_added(r):
    F = getfn("ours", r["function"])
    st = r["stmt"]
    md = re.match(r"^_(\d+) = &(mut )?\(\*_(\d+)\)$", st.rstrip(";"))
    rawtemp = r["root"].startswith("{") and re.search(r"as_mut_ptr\(|&raw |as \(PtrToPtr\)|as \(PointerCoercion\(MutToConstPointer", r["root"]) is not None
    if md:
        dst = int(md.group(1))
        kind, cst, det = consumer(F, dst)
        if kind == "call":
            cp, pos = det
            callee = resolve_callee(r["function"], cp)
            ft_o = formal_type("ours", callee, pos) if pos is not None else "?"
            ft_i = formal_type("input", callee, pos) if pos is not None else "?"
            return ("v" if rawtemp else "i"), callee, pos, ft_i, ft_o, cst
        return {"decl": "ii", "option": "iv"}.get(kind, "vi"), str(det), None, "", "", cst
    return "vi", "", None, "", "", st


def patch_plus_lines():
    """b-side line numbers of '+' lines in the census's emitted.patch (substrate a/lib.rs -> emitted b/lib.rs)."""
    plus, bl = set(), None
    for line in open(CEN.replace("raw-boundary-%s.tsv", "raw-boundary-emitted.patch")):
        m = re.match(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", line)
        if m:
            bl = int(m.group(1))
            continue
        if bl is None or line.startswith(("---", "+++")) and bl is None:
            continue
        if line.startswith("+"):
            plus.add(bl)
            bl += 1
        elif line.startswith("-"):
            pass
        elif line.startswith(" ") or line == "\n":
            bl += 1
    return plus


def substrate_lines():
    """reconstruct the substrate a/lib.rs from the emitted b/lib.rs and the census patch (reverse application)."""
    b = open("scratch/main/batch60sp/emitted-trees/libzahl/lib.rs", encoding="utf-8").read().split("\n")
    a, bi = [], 0   # bi: 0-based index of next b line to copy
    hunk = False
    for line in open(CEN.replace("raw-boundary-%s.tsv", "raw-boundary-emitted.patch"), encoding="utf-8"):
        line = line.rstrip("\n")
        m = re.match(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", line)
        if m:
            start = int(m.group(1)) - 1
            a.extend(b[bi:start])
            bi = start
            hunk = True
            continue
        if not hunk:
            continue
        if line.startswith("+"):
            bi += 1
        elif line.startswith("-"):
            a.append(line[1:])
        elif line.startswith(" ") or line == "":
            a.append(b[bi])
            bi += 1
        elif line.startswith("\\"):
            continue
    a.extend(b[bi:])
    return a


INPUT_SRC = "crat/benchmarks/rs-crown/libzahl/src/%s.rs"
OURS_LIB = "scratch/main/batch60sp/emitted-trees/libzahl/lib.rs"
_SUB = None


def fn_text(lines, fn, nested):
    """the function's source text, whitespace removed. nested: lib.rs with `pub mod <m> {` wrappers."""
    _, mod, name = fn.split("::")
    i = 0
    if nested:
        i = next((k for k, l in enumerate(lines) if re.match(r"^\s*pub mod %s \{" % re.escape(mod), l)), None)
        if i is None:
            return ""
    k = next((k for k in range(i, len(lines)) if re.search(r"\bfn %s\s*\(" % re.escape(name), lines[k])), None)
    if k is None:
        return ""
    depth, out, started = 0, [], False
    for l in lines[k:]:
        out.append(l)
        for c in l:
            if c == "{":
                depth += 1
                started = True
            elif c == "}":
                depth -= 1
        if started and depth == 0:
            break
    return re.sub(r"\s+", "", "\n".join(out))


_ft = {}


def texts(fn):
    global _SUB
    if fn not in _ft:
        if _SUB is None:
            _SUB = substrate_lines()
        mod = fn.split("::")[1]
        try:
            il = open(INPUT_SRC % mod, encoding="utf-8").read().split("\n")
        except OSError:
            il = []
        ol = _src_cache.setdefault(OURS_LIB, open(OURS_LIB, encoding="utf-8").read().splitlines())
        _ft[fn] = (fn_text(il, fn, False), fn_text(_SUB, fn, True), fn_text(ol, fn, True))
    return _ft[fn]


def text_counts(fn, expr):
    e = re.sub(r"\s+", "", expr)
    if not e:
        return (0, 0, 0)
    return tuple(t.count(e) for t in texts(fn))


SUBJ = {}
for _r in csv.DictReader(open(CEN % "subjects"), delimiter="\t"):
    SUBJ[(_r["owner_fn"], int(_r["mir_local"]) if _r["mir_local"].isdigit() else -1)] = _r
SOUT = {r["subject_key"]: r for r in csv.DictReader(open(CEN % "subject-outcomes"), delimiter="\t")}


def subject_of(fn, local):
    s = SUBJ.get((fn, local))
    if not s:
        return "-", "-"
    o = SOUT.get(s["subject_key"], {})
    st = "%s/%s/%s" % (o.get("family", s["family"]), o.get("delivery", "?"), o.get("emitted_form", "?"))
    if o.get("delivery") != "realized-as-predicted":
        st += " reason=" + (s["reason"] or "-")
    return s["subject_key"], st


def base_local(F, local, depth=0):
    """the debug-named local a temporary root is derived from (first named local in its definition chain)."""
    if local in F.debug or depth > 8:
        return local
    for rhs, _, _, _ in F.defs.get(local, []):
        for m in LOC.finditer(rhs):
            return base_local(F, int(m.group(1)), depth + 1)
    return local


def p7_index():
    idx = collections.defaultdict(list)
    for r in csv.DictReader(open(CEN % "premise-bridge-dereferenceable"), delimiter="\t"):
        if r["site_kind"] != "call-bridge":
            continue
        caller, sp = r["site"].split("@", 1)
        m = re.search(r":(\d+):(\d+): (\d+):(\d+)$", sp)
        global _SUB
        if _SUB is None:
            _SUB = substrate_lines()
        l0, c0, l1, c1 = map(int, m.groups())
        txt = _SUB[l0 - 1][c0 - 1:c1 - 1] if l0 == l1 else " ".join([_SUB[l0 - 1][c0 - 1:]] + _SUB[l0:l1 - 1] + [_SUB[l1 - 1][:c1 - 1]])
        r["argtext"] = re.sub(r"\s+", "", txt)
        idx[caller].append((int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), r))
    return idx


def span_tuple(span):
    m = re.search(r":(\d+):(\d+): (\d+):(\d+)$", span)
    return tuple(map(int, m.groups())) if m else None


def reshape(fn):
    """the substrate (expand -> extern -> preprocess) reshapes this function: which pattern(s)."""
    ti, ts, to = texts(fn)
    pats = []
    if ti.count("letrefmut") > ts.count("letrefmut"):
        pats.append("let-ref-mut-fresh inlined (%d -> %d)" % (ti.count("letrefmut"), ts.count("letrefmut")))
    if ts.count("__idx_") > ti.count("__idx_"):
        pats.append("index hoisted to __idx_N (%d)" % ts.count("let__idx_"))
    n_i, n_s = len(re.findall(r"letfresh\d+=str;", ti)), len(re.findall(r"letfresh\d+=\*str;", ts))
    if n_s > 0 and n_i > 0:
        pats.append("post-increment read hoisted: let freshN = str; *freshN -> let freshN = *str (%d)" % n_s)
    return "; ".join(pats)


def build():
    inp, ours, added, removed = main()
    p7 = p7_index()
    p7_used = set()
    bri, bri_n = bridge_receipt_index()
    out = []
    for r in added:
        F = getfn("ours", r["function"])
        c, callee, pos, ft_i, ft_o, cst = classify_added(r)
        loc = int(r["local"][1:])
        bl = base_local(F, loc)
        skey, sst = subject_of(r["function"], bl) if bl in F.debug and bl <= F.nargs else ("-", "-")
        detail, p7j = "", "-"
        ci, cs, co = text_counts(r["function"], span_text(r["span"]))
        if c in ("i", "v"):
            detail = "%s(arg%s): formal %s -> %s" % (callee, pos, ft_i, ft_o)
            # P7 join: the call-bridge receipt whose site span covers this deref (same caller, same line, columns overlap)
            arg = re.sub(r"\s+", "", span_text(r["span"]))
            arg = re.sub(r"^&(mut)?\*", "", arg)
            for k, (l0, c0, l1, c1, rr) in enumerate(p7.get(r["function"], [])):
                if (r["function"], k) in p7_used or rr["function"] != callee or int(rr["ordinal"]) != pos:
                    continue
                if rr["argtext"] == arg:
                    p7j = "%s:substrate@%s:%s" % (rr["binding"], rr["site"].split("@")[1].split("/")[-1], rr["quiet_prefix"])
                    p7_used.add((r["function"], k))
                    break
            bk = (r["function"], callee.split("::")[-1], pos, arg)
            r["bridge_receipt"] = bri[bk].pop(0) if bri.get(bk) else "-"
            if c == "i" and "pair" in sst:
                detail += "; root held raw by a pair hold"
        else:
            pat = reshape(r["function"])
            if pat:
                c, detail = "vi", "substrate-shape [%s]: in the rewriter's input already (text count input %d / substrate %d / ours %d)" % (pat, ci, cs, co)
            else:
                detail = "UNEXPLAINED (text count input %d / substrate %d / ours %d)" % (ci, cs, co)
        out.append(dict(change="added", function=r["function"], construct_or_cause=c, detail=detail, callee=callee or "-",
                        root=r["root"][:120], proj=r["proj"], root_subject=skey, root_status=sst, p7_join=p7j, bridge_receipt=r.get("bridge_receipt", "-"),
                        stmt=r["stmt"], span=r["span"].split("/")[-1], text_counts="%d/%d/%d" % (ci, cs, co)))
    for r in removed:
        F = getfn("input", r["function"])
        Fo = getfn("ours", r["function"])
        loc = int(r["local"][1:])
        bl = base_local(F, loc)
        name = F.debug.get(bl)
        ci, cs, co = text_counts(r["function"], span_text(r["span"]))
        # the same named local in ours: its type
        ol = next((l for l, n in Fo.debug.items() if n == name), None) if name else None
        oty = Fo.decl.get(ol, "?") if ol is not None else "?"
        if name and bl == loc and re.match(r"^(&|std::boxed::Box<|Box<|std::option::Option<&|Option<&|&mut )", oty):
            skey, sst = subject_of(r["function"], ol)
            c = "made-safe"
            detail = "%s: %s -> %s" % (name, F.decl.get(bl, "?"), oty)
        elif reshape(r["function"]):
            c, skey, sst = "substrate-shape", "-", "-"
            detail = "[%s] gone from the rewriter's input already (text count input %d / substrate %d / ours %d)" % (reshape(r["function"]), ci, cs, co)
        else:
            c, skey, sst = "other", "-", "-"
            detail = "UNEXPLAINED %s: %s -> %s (text count input %d / substrate %d / ours %d)" % (name, F.decl.get(bl, "?"), oty, ci, cs, co)
        out.append(dict(change="removed", function=r["function"], construct_or_cause=c, detail=detail, callee="-",
                        root=r["root"][:120], proj=r["proj"], root_subject=skey, root_status=sst, p7_join="-", bridge_receipt="-",
                        stmt=r["stmt"], span=r["span"].split("/")[-1], text_counts="%d/%d/%d" % (ci, cs, co)))
    p7_all = sum(len(v) for v in p7.values())
    left = sum(len(v) for v in bri.values())
    return inp, ours, out, p7_all, len(p7_used), bri_n, left


def bridge_receipt_index():
    """terminal/applied c-raw-reborrow bridge receipts, keyed (caller fn path, callee last segment, ordinal, argument text);
    offsets are bytes into the rewriter's input (the substrate)."""
    global _SUB
    if _SUB is None:
        _SUB = substrate_lines()
    sb = "\n".join(_SUB).encode("utf-8")
    starts = [0]
    for k, ch in enumerate(sb):
        if ch == 10:
            starts.append(k + 1)
    import bisect
    owner, mod, fn = [], None, None
    for l in _SUB:
        m = re.match(r"^\s*pub mod (\w+) \{", l)
        if m:
            mod = m.group(1)
        m = re.search(r"\bfn (\w+)\s*\(", l)
        if m:
            fn = m.group(1)
        owner.append("src::%s::%s" % (mod, fn))
    idx = collections.defaultdict(list)
    n = 0
    for x in csv.DictReader(open(CEN % "bridge-receipts"), delimiter="\t"):
        if x["stage"] != "terminal" or x["state"] != "applied" or "reborrow" not in x["bridge_kind"]:
            continue
        lo, hi = int(x["lo"]), int(x["hi"])
        line = bisect.bisect_right(starts, lo) - 1
        arg = re.sub(r"\s+", "", sb[lo:hi].decode("utf-8"))
        # callee: identifier before the '(' that encloses the argument
        d, k = 0, lo - 1
        while k >= 0:
            c = sb[k:k + 1]
            if c in (b")", b"]"):
                d += 1
            elif c in (b"(", b"["):
                if d == 0:
                    break
                d -= 1
            k -= 1
        mm = re.search(rb"(\w+)\s*$", sb[max(0, k - 80):k])
        callee = mm.group(1).decode() if mm else "?"
        pos = int(x["position"][3:]) if x["position"].startswith("arg") else -1
        idx[(owner[line], callee, pos, arg)].append("%s@substrate:%d:%d" % (x["bridge_kind"], line + 1, lo - starts[line] + 1))
        n += 1
    return idx, n


def write():
    inp, ours, out, p7a, p7u, bn, bl = build()
    cols = ["change", "function", "construct_or_cause", "callee", "detail", "root", "proj", "root_subject", "root_status",
            "bridge_receipt", "p7_join", "text_counts", "span", "stmt"]
    out.sort(key=lambda o: (o["function"], o["change"], o["construct_or_cause"], o["span"]))
    with open(os.path.join(OUT, "a1-sites.tsv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", lineterminator="\n", extrasaction="ignore")
        w.writeheader()
        w.writerows(out)
    off = collections.Counter()
    for side in ("input", "ours"):
        for r in csv.DictReader(open("%s/sites/%s-%s.tsv" % (R, side, PROG)), delimiter="\t"):
            if r["phase"] == "official":
                off[(side, r["function"])] += int(r["official"])
    fd = collections.Counter()
    for r in inp:
        fd[("input", r["function"])] += 1
    for r in ours:
        fd[("ours", r["function"])] += 1
    fns = sorted(set(f for _, f in fd) | set(o["function"] for o in out))
    pc = ["function", "full_deref_input", "full_deref_ours", "net", "added_i_call_bridge", "added_ii_decl_view",
          "added_iii_pair_swap_view", "added_iv_option_view", "added_v_raw_temp_bridge", "added_vi_substrate",
          "removed_made_safe", "removed_substrate", "removed_other", "check", "official_input", "official_ours", "bridges_by_callee"]
    rows = []
    tot = collections.Counter()
    for f in fns:
        mine = [o for o in out if o["function"] == f]
        a = collections.Counter(o["construct_or_cause"] for o in mine if o["change"] == "added")
        d = collections.Counter(o["construct_or_cause"] for o in mine if o["change"] == "removed")
        net = fd[("ours", f)] - fd[("input", f)]
        if not mine and net == 0:
            continue
        cal = collections.Counter(o["callee"].split("::")[-1] for o in mine if o["construct_or_cause"] in ("i", "v"))
        row = {"function": f, "full_deref_input": fd[("input", f)], "full_deref_ours": fd[("ours", f)], "net": net,
               "added_i_call_bridge": a["i"], "added_ii_decl_view": a["ii"], "added_iii_pair_swap_view": a["iii"],
               "added_iv_option_view": a["iv"], "added_v_raw_temp_bridge": a["v"], "added_vi_substrate": a["vi"],
               "removed_made_safe": d["made-safe"], "removed_substrate": d["substrate-shape"], "removed_other": d["other"],
               "official_input": off[("input", f)], "official_ours": off[("ours", f)],
               "bridges_by_callee": ",".join("%s:%d" % kv for kv in sorted(cal.items())) or "-"}
        row["check"] = "ok" if sum(a.values()) - sum(d.values()) == net else "MISMATCH"
        rows.append(row)
        for k in pc[1:-1]:
            if k != "check" and k != "function":
                tot[k] += row[k]
    rows.sort(key=lambda r: (-r["net"], r["function"]))
    tr = {k: tot[k] for k in pc[1:-1] if k != "check"}
    tr["full_deref_input"], tr["full_deref_ours"] = len(inp), len(ours)
    tr["official_input"] = sum(v for (sd, _), v in off.items() if sd == "input")
    tr["official_ours"] = sum(v for (sd, _), v in off.items() if sd == "ours")
    tr.update(function="TOTAL", check="ok" if tot["full_deref_ours"] - tot["full_deref_input"] == 79 else "MISMATCH",
              bridges_by_callee="-")
    with open(os.path.join(OUT, "a1-per-function.tsv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=pc, delimiter="\t", lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
        w.writerow(tr)
    print("TOTAL", tr)
    print("p7 call-bridge receipts %d, joined %d; bridge receipts (terminal applied c-raw-reborrow) %d, unjoined %d" % (p7a, p7u, bn, bl))
    return out, rows


if __name__ == "__main__" and "--write" in sys.argv:
    write()
