#!/usr/bin/env python3
"""apply_151.py -- analysis-fanout 124 (relay 151 §1, R1111-1): re-seed rq1.inator.<p>.sig.{before, inator-static,
inator-dynamic, inator-unknown, ours-safe, ours-raw} (9 programs + total) under the one rule of rebucket2.py; the
rq1.inator.<p>.sig.inator-byvalue rows (123) are marked superseded (by-value now counts as static), values kept.
Input docs origin/main:paper/numbers-of-record.md + rebucket2.json; output r151/record-124.md, log-124.tsv. Fails closed."""
import hashlib, json, re, subprocess, sys

R = "scratch/analysis-fanout/r151"
DOCS = "crat/docs"
P9 = ["example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp", "total"]
KEYS = ["before", "inator-static", "inator-dynamic", "inator-unknown", "ours-safe", "ours-raw"]


def die(m):
    raise SystemExit("apply_151: FAIL: " + m)


new = json.load(open(R + "/rebucket2.json"))
raw = subprocess.run(["git", "-C", DOCS, "show", "origin/main:paper/numbers-of-record.md"], capture_output=True,
                     check=True).stdout
lines = raw.decode("utf-8").split("\n")
idx = {}
for i, l in enumerate(lines):
    m = re.match(r"^\| ([^ |]+) \|", l)
    if m and not l.startswith("| key |"):
        idx[m.group(1)] = i


def cells(l):
    pos = [i for i, ch in enumerate(l) if ch == "|"]
    if len(pos) != 7:
        die("cells: " + l[:60])
    return pos


def setrow(k, value, prefix):
    l = lines[idx[k]]
    pos = cells(l)
    old = l[pos[1] + 1:pos[2]].strip()
    oldprov = l[pos[5] + 2:pos[6]].rstrip()
    if "|" in prefix or "|" in value:
        die("pipe")
    lines[idx[k]] = "%s %s %s %s %s|" % (l[:pos[1] + 1], value, l[pos[2]:pos[5] + 1], prefix + oldprov, "")
    lines[idx[k]] = lines[idx[k]].rstrip("|").rstrip() + " |"
    return old


DEF = ("analysis-fanout 124 (relay 151, R1111-1 USER 10-14): RE-BUCKETED by one rule -- over &inator's type fragment "
       "of the position with the outermost ghost stripped (R1082-1), every nesting level walked (inside &, &mut, Box, "
       "[..], ghost): DYNAMIC if any level is reference-counted or interior-mutable (the constructors present in the nine "
       "outputs of record: Rc in 68 and Cell in 44 of the 317 positions; RefCell, Arc, Mutex, RwLock, UnsafeCell, Weak, OnceCell occur 0 "
       "times in all 37 rtypes.txt of the image and the source build); UNKNOWN if the fragment itself is &inator's "
       "`unknown` (a position it could not type; neither static nor dynamic, the seat's reading of the user's 'otherwise "
       "static', the user may overrule); STATIC otherwise (a reference, a mutable reference, a box, a by-value "
       "replacement of the pointer by its referent, and a reference or box to an untyped pointee: %d of the "
       "static here contain `unknown` below their outer level, 49 of the 279 exactly `&'n unknown`). Scope: parameters + returns (279 of the 317 interface positions, as 123); with the 38 struct "
       "fields (317): %s. Ours unchanged (our emitted type at the landed 32d966b9f; ref / mut / box -> safe, raw -> raw). "
       "Source: 119's joined positions (r145/pairs.tsv, whose fragments equal r143/reconcile.json's, the counter's input "
       "of record), rebucket2.py (agents/artifacts/2026-10-14-analysis-fanout-124a/); previously (123, "
       "119's mapping: static = ref + mut + box not Cell-flagged, dynamic = rc + Cell-flagged): %s; ")
log = []
for p in P9:
    s, a = new["sig"][p], new["all"][p]
    allf = "before %d, static %d, dynamic %d, unknown %d, ours safe %d, raw %d" % tuple(a.get(k, 0) for k in KEYS)
    for k in KEYS:
        key = "rq1.inator.%s.sig.%s" % (p, k)
        if key not in idx:
            die("missing " + key)
        v = str(s.get(k, 0))
        oldv = lines[idx[key]].split("|")[2].strip()
        if k in ("before", "ours-safe", "ours-raw") and v != oldv:
            die("unchanged column moved " + key)
        setrow(key, v, DEF % (s.get("inator-static.unknown-pointee", 0), allf, oldv))
        log.append((key, oldv, v))
    bk = "rq1.inator.%s.sig.inator-byvalue" % p
    oldv = lines[idx[bk]].split("|")[2].strip()
    setrow(bk, oldv, "analysis-fanout 124 (relay 151, R1111-1): SUPERSEDED -- under the one rule a by-value replacement "
                     "counts as static (rq1.inator.%s.sig.inator-static); kept as 123's count, not printed; " % p)
    log.append((bk, oldv, oldv + " (superseded)"))
text = "\n".join(lines)
for l in text.split("\n"):
    if re.match(r"^\| rq1\.inator\.", l) and l.count("|") != 7:
        die("row cells " + l[:60])
open(R + "/record-124.md", "w", encoding="utf-8", newline="").write(text)
open(R + "/log-124.tsv", "w").write("key\tbefore\tafter\n" + "".join("\t".join(x) + "\n" for x in log))
print("in md5", hashlib.md5(raw).hexdigest(), "out md5", hashlib.md5(text.encode()).hexdigest(), "rows", len(log),
      "moved", sum(1 for x in log if x[1] != x[2] and "superseded" not in x[2]))
