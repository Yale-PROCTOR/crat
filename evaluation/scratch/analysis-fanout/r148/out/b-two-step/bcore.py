#!/usr/bin/env python3
"""bcore.py -- analysis-fanout relay 148, task B: the two-step match (input -> substrate -> ours) with A1's rule.
Read-only outside this directory; Python only; no compiler.  Imported by b.py.

A site is one row of r148/sites/<side>-<p>.tsv:
  T2       = phase=promoted, full_deref=1   (normalized against the SimplifyCfg-promote-consts.after dump)
  official = phase=official, official=1     (normalized against the runtime-post-cleanup.after dump)
key = root :: projection, matched per function as a multiset (A1's rule, copied from out/a1-libzahl/a1.py and
parameterized by program and dump phase): root = debug name, argN for an unnamed formal, `ret` for _0, otherwise the
temporary's normalized definition(s) followed recursively (depth <= 8); a `const {allocN: ..}` is `static(<source
text>)`; a callee path keeps its last segment; move/copy and field/cast types dropped."""
import collections, csv, os, re, sys

sys.dont_write_bytecode = True
R = "scratch/analysis-fanout/r148"
sys.path.insert(0, R)
import mir_sites as M  # noqa: E402

LOC = re.compile(r"(?<![A-Za-z0-9_])_(\d+)\b")
PHASE_FILE = {"T2": "SimplifyCfg-promote-consts", "official": "runtime-post-cleanup"}
SIDES = ("input", "substrate", "ours")
PROGS = ("libzahl", "json.h", "urlparser")

_src = {}


def src_lines(f):
    if f not in _src:
        try:
            _src[f] = open(f, encoding="utf-8").read().split("\n")
        except OSError:
            _src[f] = []
    return _src[f]


def parse_span(span):
    m = re.match(r"(.+):(\d+):(\d+): (\d+):(\d+)$", span)
    if not m:
        return None
    return (m.group(1),) + tuple(map(int, m.groups()[1:]))


def span_text(span):
    p = parse_span(span)
    if not p:
        return "?"
    f, l0, c0, l1, c1 = p
    L = src_lines(f)
    if not L or l0 > len(L):
        return "?"
    if l0 == l1:
        return L[l0 - 1][c0 - 1:c1 - 1]
    return " ".join([L[l0 - 1][c0 - 1:]] + L[l0:l1 - 1] + [L[l1 - 1][:c1 - 1]]).strip()


def span_line(span):
    p = parse_span(span)
    if not p:
        return ""
    L = src_lines(p[0])
    return L[p[1] - 1].strip() if L and p[1] <= len(L) else ""


def strip_types(s):
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
        self.path = path
        self.decl, self.debug, self.blocks = M.parse_file(path)
        self.defs = collections.defaultdict(list)
        self.uses = collections.defaultdict(list)
        for idx, (bb, cl, st, span) in enumerate(self.blocks):
            if M.NONUSE.match(st) or st.startswith("FakeRead"):
                continue
            md = re.match(r"^_(\d+) = (.*)$", st)
            rhs = st
            if md:
                self.defs[int(md.group(1))].append((md.group(2), span, bb, idx))
                rhs = md.group(2)
            for m in LOC.finditer(rhs):
                self.uses[int(m.group(1))].append((st, bb, idx))
        lines = open(path, encoding="utf-8").read().splitlines()
        self.sig = next((l for l in lines if re.match(r"^(unsafe )?(extern \"C\" )?fn ", l) or l.startswith("fn ")), "")
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
        self._norm[key] = "_"
        alts = sorted(set(self.norm_rhs(rhs, span, depth + 1) for rhs, span, _, _ in self.defs.get(local, []))) or ["?"]
        r = "{" + "|".join(alts) + "}"
        self._norm[key] = r
        return r

    def norm_rhs(self, rhs, span, depth):
        rhs = rhs.rstrip().rstrip(";")
        rhs = re.sub(r"\s*-> \[.*$", "", rhs)
        rhs = re.sub(r"\s*-> (bb\d+|unwind.*)$", "", rhs)
        if re.match(r"^const \{alloc\d+: [^}]*\}$", rhs):
            return "static(%s)" % span_text(span)
        rhs = re.sub(r"const \{alloc\d+: [^}]*\}", "static(?)", rhs)
        rhs = re.sub(r"(?:[A-Za-z_][\w]*::|<[^()]*?>::)+([A-Za-z_]\w*)(::<[^()]*>)?\(", r"\1(", rhs)
        rhs = re.sub(r"\b(move|copy) ", "", rhs)
        rhs = strip_types(rhs)
        return LOC.sub(lambda m: self.norm(int(m.group(1)), depth), rhs)

    def norm_place(self, place):
        p = strip_types(place)
        first = [True]

        def rep(m):
            if first[0]:
                first[0] = False
                return "R"
            return self.norm(int(m.group(1)))
        return LOC.sub(rep, p)

    def base_local(self, local, depth=0):
        """the first debug-named local / formal a temporary's definition chain reaches."""
        if local in self.debug or 1 <= local <= self.nargs or depth > 8:
            return local
        for rhs, _, _, _ in self.defs.get(local, []):
            for m in LOC.finditer(rhs):
                return self.base_local(int(m.group(1)), depth + 1)
        return local

    def ty_of_name(self, name):
        return [self.decl.get(l, "?") for l, n in self.debug.items() if n == name]


def dump_path(side, prog, fn, unit):
    return "%s/mir/%s/%s/dump/lib.%s.%s.after.mir" % (R, side, prog, fn.replace("::", "-"), PHASE_FILE[unit])


_fns = {}


def getfn(side, prog, fn, unit):
    k = (side, prog, fn, unit)
    if k not in _fns:
        p = dump_path(side, prog, fn, unit)
        _fns[k] = Fn(p) if os.path.exists(p) else None
    return _fns[k]


def load_sites(side, prog, unit):
    out = []
    for r in csv.DictReader(open("%s/sites/%s-%s.tsv" % (R, side, prog)), delimiter="\t"):
        if unit == "T2" and not (r["phase"] == "promoted" and r["full_deref"] == "1"):
            continue
        if unit == "official" and not (r["phase"] == "official" and r["official"] == "1"):
            continue
        F = getfn(side, prog, r["function"], unit)
        loc = int(r["local"][1:])
        r["root"] = F.norm(loc)
        r["proj"] = F.norm_place(r["place"])
        r["key"] = r["root"] + " :: " + r["proj"]
        r["side"] = side
        out.append(r)
    return out


def match(a, b):
    """per function multiset match; returns (matched, added (b rows), removed (a rows))."""
    by = collections.defaultdict(lambda: ([], []))
    for r in a:
        by[r["function"]][0].append(r)
    for r in b:
        by[r["function"]][1].append(r)
    added, removed, matched = [], [], 0
    for fn, (x, y) in by.items():
        cx = collections.Counter(r["key"] for r in x)
        cy = collections.Counter(r["key"] for r in y)
        left = dict(cx)
        for r in y:
            if left.get(r["key"], 0) > 0:
                left[r["key"]] -= 1
                matched += 1
            else:
                added.append(r)
        left = dict(cy)
        for r in x:
            if left.get(r["key"], 0) > 0:
                left[r["key"]] -= 1
            else:
                removed.append(r)
    return matched, added, removed


if __name__ == "__main__":
    for prog in PROGS:
        for unit in ("T2", "official"):
            S = {s: load_sites(s, prog, unit) for s in SIDES}
            for a, b, step in (("input", "substrate", "P"), ("substrate", "ours", "W"), ("input", "ours", "P+W")):
                m, ad, rm = match(S[a], S[b])
                print("%-9s %-8s %-3s %5d -> %5d  matched %5d added %4d removed %4d net %+d %s" % (
                    prog, unit, step, len(S[a]), len(S[b]), m, len(ad), len(rm), len(ad) - len(rm),
                    "ok" if len(ad) - len(rm) == len(S[b]) - len(S[a]) else "RESIDUE"))
