#!/usr/bin/env python3
"""mir_sites.py -- analysis-fanout relay 148: the T2 counter's place occurrences as SITES, read from rustc's MIR dumps
(dump.sh: mir_promoted = SimplifyCfg-promote-consts.after; the official phase = runtime-post-cleanup.after).

The counter's rules (agents/tools/rq2/pos_counter/src/main.rs, `Official` / `Full`), re-implemented on the text:
  every place the MIR visitor visits outside a NonUse context (StorageLive / StorageDead /
  AscribeUserType / var debug info; PlaceMention IS a use: NonMutatingUse(PlaceMention)) is one occurrence;
  full_roots   (mir_promoted, cleanup blocks skipped): the place holds a Deref and its ROOT local is raw-pointer-typed;
  full_deref   (mir_promoted, cleanup blocks skipped): some Deref in the place has a raw-pointer-typed base;
  official     (runtime-post-cleanup, cleanup blocks INCLUDED): the root is a debug-named local whose `<fn>::<name>` is
               in the program's universe, and the place holds a Deref.
usage: mir_sites.py <side> <program> <out.tsv> [--check <uses.tsv>]
Writes one row per counted occurrence (full_deref or official or full_roots) with its span and statement."""
import collections, csv, os, re, sys

R = "scratch/analysis-fanout/r148"
UNIV = "scratch/analysis-fanout/r146/trees/t4/out-ours-60sp/universe/%s.txt"

NONUSE = re.compile(r"^(StorageLive|StorageDead|AscribeUserType|Coverage|ConstEvalCounter|nop\b|BackwardIncompatibleDropHint)")
LOCAL = re.compile(r"(?<![A-Za-z0-9_])_(\d+)\b")


def strip_comment(line):
    # code before the span comment; MIR code has no '//' except inside string constants, which carry no places
    i = line.find("//")
    return line if i < 0 else line[:i]


def scan_type(s, i):
    """from s[i] (just after ': '), return the index of the ')' closing the field / cast annotation."""
    depth = 0
    while i < len(s):
        c = s[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                return i
            depth -= 1
        elif c == "<":
            depth += 1
        elif c == ">" and s[i - 1] != "-":
            depth -= 1
        i += 1
    return -1


def parse_place(s, pos, m):
    """the place whose local token is s[m.start():m.end()]; returns (start, end, local, projections) or None."""
    j = m.start() - 1
    pre = []                       # prefixes, innermost first: '(*' or '('
    while j >= 0 and s[j] in "(*":
        if s[j] == "*" and j >= 1 and s[j - 1] == "(":
            pre.append("(*")
            j -= 2
        elif s[j] == "(":
            pre.append("(")
            j -= 1
        else:
            break
    k = m.end()
    proj = []
    used = 0
    while True:
        if k < len(s) and s[k] == "[":           # Index / ConstantIndex / Subslice: no prefix consumed
            d = 0
            e = k
            while e < len(s):
                if s[e] == "[":
                    d += 1
                elif s[e] == "]":
                    d -= 1
                    if d == 0:
                        break
                e += 1
            proj.append(("index", s[k:e + 1]))
            k = e + 1
            continue
        if used >= len(pre):
            break
        p = pre[used]
        if p == "(*" and k < len(s) and s[k] == ")":
            proj.append(("deref", None))
            used += 1
            k += 1
            continue
        if p == "(":
            mf = re.match(r"\.(\d+): ", s[k:])
            if mf:
                t0 = k + mf.end()
                t1 = scan_type(s, t0)
                if t1 < 0:
                    break
                proj.append(("field", s[t0:t1]))
                used += 1
                k = t1 + 1
                continue
            md = re.match(r" as (subtype )?", s[k:])
            if md:
                t0 = k + md.end()
                t1 = scan_type(s, t0)
                if t1 < 0:
                    break
                proj.append(("cast" if md.group(1) else "downcast", s[t0:t1]))
                used += 1
                k = t1 + 1
                continue
        break
    start = m.start() - sum(len(p) for p in pre[:used])
    return start, k, int(m.group(1)), proj


def strip_ref(t):
    t = t.strip()
    for p in ("*mut ", "*const ", "&mut ", "&"):
        if t.startswith(p):
            t = t[len(p):]
            t = re.sub(r"^'\w+ (mut )?", lambda mm: "" if not mm.group(1) else "", t) if p == "&" else t
            if p == "&" and t.startswith("mut "):
                t = t[4:]
            return t
    mb = re.match(r"^(?:std::boxed::|alloc::boxed::)?Box<(.*)>$", t)
    if mb:
        inner = mb.group(1)
        d = 0
        for i, c in enumerate(inner):
            if c == "<":
                d += 1
            elif c == ">":
                d -= 1
            elif c == "," and d == 0:
                return inner[:i]
        return inner
    return "?" + t


def elem(t):
    t = t.strip()
    if t.startswith("[") and t.endswith("]"):
        inner = t[1:-1]
        d = 0
        for i in range(len(inner) - 1, -1, -1):
            c = inner[i]
            if c in ")]>":
                d += 1
            elif c in "([<":
                d -= 1
            elif c == ";" and d == 0:
                return inner[:i].strip()
        return inner
    return "?" + t


def is_raw(t):
    return t.strip().startswith(("*mut ", "*const "))


def parse_file(path):
    txt = open(path, encoding="utf-8").read().splitlines()
    decl, debug = {}, {}
    sig = next((l for l in txt if l.startswith("fn ") or l.startswith("unsafe fn ") or " fn " in l[:40]), "")
    for mp in re.finditer(r"_(\d+): ", sig):
        t0 = mp.end()
        d, e = 0, t0
        while e < len(sig):
            c = sig[e]
            if c in "([<":
                d += 1
            elif c in ")]>" and not (c == ">" and sig[e - 1] == "-"):
                if d == 0:
                    break
                d -= 1
            elif c == "," and d == 0:
                break
            e += 1
        decl[int(mp.group(1))] = sig[t0:e].strip()
    blocks = []
    cur, cleanup = None, False
    for raw in txt:
        line = strip_comment(raw).rstrip()
        sline = line.strip()
        span = ""
        ms = re.search(r"// (?:scope \d+ at |in scope \d+ at |return place in scope \d+ at )?(\S+:\d+:\d+: \d+:\d+)", raw)
        if ms:
            span = ms.group(1)
        md = re.match(r"^\s*let (?:mut )?_(\d+): (.*);$", line)
        if md:
            decl[int(md.group(1))] = md.group(2)
            continue
        mg = re.match(r"^\s*debug (\S+) => _(\d+);$", line)
        if mg:
            debug[int(mg.group(2))] = mg.group(1)
            continue
        mb = re.match(r"^\s*bb(\d+)( \(cleanup\))?: \{", line)
        if mb:
            cur = int(mb.group(1))
            cleanup = bool(mb.group(2))
            continue
        if cur is None or not sline or sline == "}" or sline.startswith(("debug ", "scope ", "let ", "|")):
            continue
        blocks.append((cur, cleanup, sline, span))
    return decl, debug, blocks


def occurrences(decl, debug, blocks):
    out = []
    for bb, cleanup, st, span in blocks:
        if NONUSE.match(st):
            continue
        consumed = []
        for m in LOCAL.finditer(st):
            if any(a <= m.start() < b for a, b in consumed):
                continue
            # a local inside an Index projection is visited as a local, not a place
            if st[:m.start()].rstrip().endswith("[") or re.match(r"\s*\]", st[m.end():]):
                pre = st[:m.start()]
                if pre.count("[") > pre.count("]"):
                    continue
            r = parse_place(st, 0, m)
            if r is None:
                continue
            a, b, local, proj = r
            consumed.append((a, b))
            out.append((bb, cleanup, st, span, local, proj, st[a:b]))
    return out


def classify(decl, debug, local, proj):
    t = decl.get(local, "?")
    root_raw = is_raw(t)
    has_deref = any(p[0] == "deref" for p in proj)
    through_raw = False
    for kind, arg in proj:
        if kind == "deref":
            if is_raw(t):
                through_raw = True
            t = strip_ref(t)
        elif kind == "field":
            t = arg
        elif kind == "cast":
            t = arg
        elif kind == "index":
            if ".." not in arg and ":" not in arg:
                t = elem(t)
    return has_deref, root_raw, through_raw


def fn_key(fname):
    # lib.src-zabs-zzero.SimplifyCfg-promote-consts.after.mir -> src::zabs::zzero
    base = os.path.basename(fname)
    body = base[len("lib."):] if base.startswith("lib.") else base.split(".", 1)[1]
    for suf in (".SimplifyCfg-promote-consts.after.mir", ".runtime-post-cleanup.after.mir"):
        if body.endswith(suf):
            body = body[: -len(suf)]
    return body.replace("-", "::")


def main():
    side, prog, out = sys.argv[1], sys.argv[2], sys.argv[3]
    check = sys.argv[sys.argv.index("--check") + 1] if "--check" in sys.argv else None
    univ = set(l.strip() for l in open(UNIV % prog) if l.strip())
    d = "%s/mir/%s/%s/dump" % (R, side, prog)
    rows, per = [], collections.defaultdict(lambda: [0, 0, 0])
    for f in sorted(os.listdir(d)):
        if "promoted[" in f or not f.endswith(".after.mir"):
            continue
        phase = "promoted" if "SimplifyCfg-promote-consts" in f else ("official" if "runtime-post-cleanup" in f else None)
        if phase is None:
            continue
        fn = fn_key(f)
        decl, debug, blocks = parse_file(os.path.join(d, f))
        for bb, cleanup, st, span, local, proj, text in occurrences(decl, debug, blocks):
            has_deref, root_raw, through_raw = classify(decl, debug, local, proj)
            if not has_deref:
                continue
            name = debug.get(local, "")
            if phase == "promoted":
                if cleanup:
                    continue
                fr, fd, of = int(root_raw), int(through_raw), 0
            else:
                of = int(bool(name) and ("%s::%s" % (fn, name)) in univ)
                fr = fd = 0
            if not (fr or fd or of):
                continue
            per[fn][0] += of
            per[fn][1] += fr
            per[fn][2] += fd
            rows.append({"side": side, "program": prog, "function": fn, "phase": phase, "official": of, "full_roots": fr,
                         "full_deref": fd, "local": "_%d" % local, "name": name or "-", "local_ty": decl.get(local, "?"),
                         "place": text, "bb": bb, "cleanup": int(cleanup), "span": span, "stmt": st})
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t", lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    tot = [sum(v[i] for v in per.values()) for i in range(3)]
    print("%s %s sites: official %d full_roots %d full_deref %d" % (side, prog, *tot))
    if check:
        bad = 0
        seen = set()
        for r in csv.DictReader(open(check), delimiter="\t"):
            fn = r["function"]
            seen.add(fn)
            mine = per.get(fn, [0, 0, 0])
            want = [int(r["official"]), int(r["full_roots"]), int(r["full_deref"])]
            if mine != want:
                bad += 1
                if bad <= 15:
                    print("  MISMATCH %s mine %s counter %s" % (fn, mine, want))
        extra = [f for f in per if f not in seen and any(per[f])]
        print("  check vs %s: %d functions differ; %d functions with sites unknown to the counter %s" % (
            check, bad, len(extra), extra[:5]))


if __name__ == "__main__":
    main()
