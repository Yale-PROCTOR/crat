#!/usr/bin/env python3
"""a2-official/classify.py -- relay 148 task A2 (json.h, urlparser): why the official unit moves the other way from T2.

Reads only: r148/sites/{input,ours}-<p>.tsv (the counted occurrences), r148/mir/{input,ours}/<p>/dump/*.after.mir
(local types, debug names, the let-ref bindings and their uses), benchmarks/rs-crown-derived/<p>/lib.rs (the substrate
the rewriter reads: which C2Rust idioms the preprocessor rewrote), and the CROWN universe file mir_sites.py uses.
Writes: a2-sites.tsv, a2-per-function.tsv, a2-keys.tsv.  Python only; no compiler is run.

Matching (the task's): within a function, by (root debug name, projection) with multiplicity.  The projection skeleton
keeps field indices and drops the field / cast types (a field whose type turned into a reference must not split a match).

Two stages are separated per (function, key), because "input" = raw rs-crown and "ours" = the emitted tree, and the
rewriter reads the preprocessed substrate (benchmarks/rs-crown-derived), not rs-crown:
  substrate = predicted(derived) - input, from two preprocessor rewrites (crates/passes/src/preprocessor.rs):
    let-ref   `let ref mut freshN = P; ... *freshN ...`  ->  P at every use ("Remove `let ref`")
              input: 1 borrow of P (+1 PlaceMention(P) in mir_promoted only); derived: one occurrence of P per use of *freshN
    fresh-ptr `let freshN = p; p = p.offset(1); ... *freshN ...`  ->  `[*p = v;] let freshN = *p; p = p.offset(1);`
              input: the *freshN occurrences (counted when freshN is raw / in CROWN's universe);
              derived: one `*p` read + one `*p` write per store through freshN (counted when p is raw / in the universe)
  rewriter  = ours - predicted(derived), named by what the emitted tree did to the key's root.
The prediction is checked: on every key whose root is raw on both sides and that no bridge touches, rewriter == 0.
"""
import collections, csv, os, re, sys

R = "scratch/analysis-fanout/r148"
OUT = R + "/out/a2-official"
DERIVED = "crat/benchmarks/rs-crown-derived/%s/lib.rs"
sys.path.insert(0, R)
import mir_sites  # noqa: E402
from mir_sites import parse_file, scan_type, occurrences, classify  # noqa: E402

PROGS = ["json.h", "urlparser"]
PH = {"promoted": "SimplifyCfg-promote-consts", "official": "runtime-post-cleanup"}
COL = {"promoted": "full_deref", "official": "official"}


def skel(place, local, name):
    out, i, s = [], 0, place
    while i < len(s):
        m = re.match(r"\.(\d+): ", s[i:])
        if m:
            out.append("." + m.group(1))
            i = scan_type(s, i + m.end())
            continue
        m = re.match(r" as (subtype )?", s[i:])
        if m:
            out.append(" as T")
            i = scan_type(s, i + m.end())
            continue
        out.append(s[i])
        i += 1
    t = "".join(out)
    t = re.sub(r"(?<![A-Za-z0-9_])%s\b" % re.escape(local), "@" + name, t, count=1)
    return re.sub(r"\[_\d+\]", "[i]", t)


def kind(stmt, place):
    if stmt.startswith("PlaceMention("):
        return "mention"
    if stmt.startswith(place + " = "):
        return "write"
    if re.search(r"&(mut |raw (const|mut) )?" + re.escape(place), stmt):
        return "borrow"
    if ("copy " + place) in stmt or ("move " + place) in stmt:
        return "read"
    return "other"


def tycat(t):
    t = t.strip()
    if t.startswith(("*mut ", "*const ")):
        return "raw"
    if re.match(r"^&('\w+ )?(mut )?\[", t):
        return "slice-ref"
    if t.startswith("&"):
        return "ref"
    if re.match(r"^(std::|core::)?(option::)?Option<&", t):
        return "option-ref"
    return "value:" + t[:24]


_mir = {}


def mir(side, prog, fn, phase):
    k = (side, prog, fn, phase)
    if k not in _mir:
        path = "%s/mir/%s/%s/dump/lib.%s.%s.after.mir" % (R, side, prog, fn.replace("::", "-"), PH[phase])
        _mir[k] = parse_file(path) if os.path.exists(path) else ({}, {}, [])
    return _mir[k]


def cats(side, prog, fn, phase, name):
    decl, debug, _ = mir(side, prog, fn, phase)
    return sorted(set(tycat(decl.get(l, "?")) for l, n in debug.items() if n == name))


def load(side, prog, phase):
    rows = collections.defaultdict(list)
    for r in csv.DictReader(open("%s/sites/%s-%s.tsv" % (R, side, prog)), delimiter="\t"):
        if r["phase"] != phase or r[COL[phase]] != "1":
            continue
        nm = r["name"] if r["name"] != "-" else "tmp"
        r["key"] = skel(r["place"], r["local"], nm)
        r["root"] = nm
        r["kind"] = kind(r["stmt"], r["place"])
        rows[(r["function"], r["key"])].append(r)
    return rows


def span_line(span):
    m = re.search(r":(\d+):\d+: ", span)
    return m.group(1) if m else ""


def substrate(prog, fn, phase, rin_by_key, univ, partners):
    """predicted derived counts minus input counts, per key, for one function; plus the input sites each rewrite removes."""
    decl, debug, blocks = mir("input", prog, fn, phase)
    delta = collections.Counter()
    removed = []   # (key, row, rule)
    added = collections.Counter()  # (key, rule) -> n
    # --- let-ref: dest locals named fresh* of reference type
    dests = {l for l, n in debug.items() if re.fullmatch(r"fresh\d+", n) and decl.get(l, "").startswith("&")}
    occ = occurrences(decl, debug, blocks)
    uses = collections.Counter()
    for bb, cleanup, st, span, local, proj, text in occ:
        if local in dests and proj and proj[0][0] == "deref":
            if phase == "promoted" and cleanup:
                continue
            uses[local] += 1
    for (fnk, key), rows in rin_by_key.items():
        if fnk != fn:
            continue
        for r in rows:
            m = re.match(r"_(\d+) = &(mut )?", r["stmt"])
            if r["kind"] == "borrow" and m and int(m.group(1)) in dests:
                k = int(m.group(1))
                delta[key] += uses[k] - 1
                removed.append((key, r, "c'-letref-inline"))
                added[(key, "c'-letref-inline")] += uses[k]
                if phase == "promoted":
                    ment = [x for x in rows if x["kind"] == "mention" and x["bb"] == r["bb"]
                            and span_line(x["span"]) == span_line(r["span"]) and not x.get("_used")]
                    if ment:
                        ment[0]["_used"] = True
                        delta[key] -= 1
                        removed.append((key, ment[0], "c'-letref-inline"))
    # --- fresh pointers: freshN raw locals the preprocessor turned into values
    for l, n in debug.items():
        if n not in partners or not decl.get(l, "").startswith(("*mut ", "*const ")):
            continue
        p = partners[n]
        frows = [r for (fnk, key), rows in rin_by_key.items() if fnk == fn for r in rows if r["root"] == n]
        for r in frows:
            delta[r["key"]] -= 1
            removed.append((r["key"], r, "c'-fresh-pointer"))
        # derived: `*p = v` per store through freshN, and one `let freshN = *p`
        nstore = sum(1 for bb, cl, st, sp, loc, proj, text in occ
                     if loc == l and proj == [("deref", None)] and st.startswith(text + " = ")
                     and not (phase == "promoted" and cl))
        if phase == "official":
            counts = ("%s::%s" % (fn, p)) in univ
        else:
            pl = [loc for loc, nm in debug.items() if nm == p]
            counts = bool(pl) and decl.get(pl[0], "").startswith(("*mut ", "*const "))
        if counts:
            delta["(*@%s)" % p] += nstore + 1
            added[("(*@%s)" % p, "c'-fresh-pointer")] += nstore + 1
    return delta, removed, added


def rewriter_rule(prog, fn, phase, key, root, d, rout):
    cin, cout = cats("input", prog, fn, phase, root), cats("ours", prog, fn, phase, root)
    if d > 0 and rout and all(re.search(r"= &(mut )?\(\*", r["stmt"]) for r in rout[-d:]):
        return "d-bridge", "a reborrow `&*x` / `&*(*x).f` built where a raw value meets a delivered reference formal"
    if d < 0 and "raw" in cin and "raw" not in cout:
        if "option-ref" in cout and phase == "official":
            return ("c-option-accessor",
                    "%s delivered as Option<&..>: every access goes through `.as_mut().unwrap()` / `.unwrap()`, "
                    "a deref of a compiler temporary" % root)
        return "subject-made-safe", "%s: raw -> %s" % (root, "/".join(cout) or "absent")
    if d < 0 and root == "tmp":
        return "subject-made-safe", "a raw temporary no longer formed"
    return "unexplained", "cin=%s cout=%s" % (cin, cout)


def main():
    univ_all = {}
    sites, keyrows, perfn, summary = [], [], [], []
    for prog in PROGS:
        univ = set(l.strip() for l in open(mir_sites.UNIV % prog) if l.strip())
        partners = {}
        src = open(DERIVED % prog, encoding="utf-8").read()
        for m in re.finditer(r"let (?:mut )?(fresh\d+) = \*(\w+);", src):
            partners[m.group(1)] = m.group(2)
        fnstat = collections.defaultdict(dict)
        progtot = {}
        for phase in ("official", "promoted"):
            A, B = load("input", prog, phase), load("ours", prog, phase)
            fns = sorted(set(f for f, _ in A) | set(f for f, _ in B))
            tot = collections.Counter()
            for fn in fns:
                sd, removed, added = substrate(prog, fn, phase, A, univ, partners)
                keys = sorted(set(k for f, k in A if f == fn) | set(k for f, k in B if f == fn) | set(sd))
                fdel = collections.Counter()
                kept = 0
                for key in keys:
                    rin, rout = A.get((fn, key), []), B.get((fn, key), [])
                    root = (rin or rout)[0]["root"] if (rin or rout) else key.split("@")[1].split(")")[0]
                    pred = len(rin) + sd[key]
                    dsub, drw = sd[key], len(rout) - pred
                    if dsub:
                        for rule in ("c'-letref-inline", "c'-fresh-pointer"):
                            pass
                    # substrate deltas by rule
                    sub_by = collections.Counter()
                    for k2, r, rule in removed:
                        if k2 == key:
                            sub_by[rule] -= 1
                    for (k2, rule), n in added.items():
                        if k2 == key:
                            sub_by[rule] += n
                    assert sum(sub_by.values()) == dsub, (prog, fn, key, sub_by, dsub)
                    for rule, n in sub_by.items():
                        fdel[rule] += n
                    rw_rule, note = ("-", "")
                    if drw:
                        rw_rule, note = rewriter_rule(prog, fn, phase, key, root, drw, rout)
                        fdel[rw_rule] += drw
                    if phase == "official" and len(rin) and len(rout) and drw == 0:
                        ci, co = cats("input", prog, fn, phase, root), cats("ours", prog, fn, phase, root)
                        if "raw" in ci and "raw" not in co:
                            kept += len(rout)
                            fdel["(a-kept)"] += 0
                            sites.append((prog, fn, "official", "ours", "kept", "a-root-now-reference", "rewriter", key,
                                          "x%d" % len(rout), "/".join(co), "-", "root raw -> %s; still counted" % "/".join(co)))
                    if dsub or drw:
                        keyrows.append((prog, phase, fn, key, len(rin), pred, len(rout), dsub,
                                        ";".join("%s:%+d" % kv for kv in sorted(sub_by.items()) if kv[1]) or "-",
                                        drw, rw_rule, note))
                    # site rows (official only, and T2 for the rewriter part)
                    for k2, r, rule in removed:
                        if k2 == key:
                            sites.append((prog, fn, phase, "input", "left", rule, "substrate", key, r["kind"], r["local_ty"],
                                          r["span"].split("/")[-1], r["stmt"]))
                    if drw < 0:
                        gone = [r for r in rin if not any(r is x for _, x, _ in removed)]
                        for r in gone[:(-drw)]:
                            sites.append((prog, fn, phase, "input", "left", rw_rule, "rewriter", key, r["kind"], r["local_ty"],
                                          r["span"].split("/")[-1], r["stmt"]))
                    if drw > 0:
                        for r in rout[-drw:]:
                            sites.append((prog, fn, phase, "ours", "appeared", rw_rule, "rewriter", key, r["kind"],
                                          r["local_ty"], r["span"].split("/")[-1], r["stmt"]))
                    nadd = sum(n for (k2, rule), n in added.items() if k2 == key)
                    if nadd and rout:
                        # the substrate's added occurrences, as they stand in ours (root still counted there)
                        cand = [r for r in rout if r["kind"] in ("read", "write")]
                        for r in cand[-nadd:] if drw >= 0 else []:
                            rule = [rule for (k2, rule), n in added.items() if k2 == key][0]
                            sites.append((prog, fn, phase, "ours", "appeared", rule, "substrate", key, r["kind"],
                                          r["local_ty"], r["span"].split("/")[-1], r["stmt"]))
                nin = sum(len(v) for (f, k), v in A.items() if f == fn)
                nout = sum(len(v) for (f, k), v in B.items() if f == fn)
                assert sum(fdel.values()) == nout - nin, (prog, fn, phase, fdel, nin, nout)
                fnstat[fn][phase] = (nin, nout, fdel, kept)
                tot.update(fdel)
                tot["_in"] += nin
                tot["_out"] += nout
            progtot[phase] = tot
        for fn in sorted(fnstat):
            o = fnstat[fn].get("official", (0, 0, collections.Counter(), 0))
            t = fnstat[fn].get("promoted", (0, 0, collections.Counter(), 0))
            if o[0] == o[1] and t[0] == t[1] and not o[3] and not any(o[2].values()) and not any(t[2].values()):
                continue
            fmt = lambda c: ";".join("%s:%+d" % kv for kv in sorted(c.items()) if kv[1]) or "-"
            perfn.append((prog, fn, o[0], o[1], o[1] - o[0], fmt(o[2]), o[3], t[0], t[1], t[1] - t[0], fmt(t[2])))
        summary.append((prog, progtot))
    with open(OUT + "/a2-sites.tsv", "w") as fh:
        fh.write("program\tfunction\tunit\tside\tchange\trule\tstage\tkey\tkind\troot_ty\tspan\tstmt\tidentity\n")
        for s in sites:
            ident = "by-count" if (s[4] == "appeared" and s[6] == "substrate") else "exact"
            fh.write("\t".join(str(x) for x in s).replace("\tpromoted\t", "\tT2\t", 1) + "\t" + ident + "\n")
    with open(OUT + "/a2-per-function.tsv", "w") as fh:
        fh.write("program\tfunction\tofficial_in\tofficial_ours\tofficial_delta\tofficial_by_rule\tofficial_kept_by_a\t"
                 "T2_in\tT2_ours\tT2_delta\tT2_by_rule\n")
        for s in perfn:
            fh.write("\t".join(str(x) for x in s) + "\n")
    with open(OUT + "/a2-keys.tsv", "w") as fh:
        fh.write("program\tunit\tfunction\tkey\tinput\tderived_pred\tours\tsubstrate_delta\tsubstrate_by_rule\t"
                 "rewriter_delta\trewriter_rule\tnote\n")
        for s in keyrows:
            fh.write("\t".join(str(x) for x in s).replace("\tpromoted\t", "\tT2\t") + "\n")
    for prog, pt in summary:
        for phase in ("official", "promoted"):
            t = pt[phase]
            print("%-9s %-8s %5d -> %5d  %s" % (prog, "T2" if phase == "promoted" else phase, t["_in"], t["_out"],
                                                 {k: v for k, v in sorted(t.items()) if not k.startswith("_") and v}))


if __name__ == "__main__":
    main()
