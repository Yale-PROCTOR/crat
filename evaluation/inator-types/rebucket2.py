#!/usr/bin/env python3
"""rebucket2.py -- analysis-fanout 124 (relay 151, R1111-1): &inator's signature types re-bucketed by ONE rule.
Per interface position, &inator's type fragment with the outermost `ghost` stripped (R1082-1); every nesting level
walked: if any level is a reference-counted or interior-mutable constructor (DYNAMIC below; the constructors present in
the nine outputs are Rc, Cell -- RefCell, Arc and the rest occur 0 times) -> dynamic; else if the fragment itself is
&inator's `unknown` (a position it could not type) -> unknown; else -> static (a reference, a mutable reference, a box,
a slice, a by-value replacement of the pointer by its referent, a reference to an untyped pointee `&'n unknown`).
Ours: our emitted type at the landed 32d966b9f: ref / mut / box -> safe, raw -> raw (unchanged from 119 / 123).
usage: rebucket2.py <pairs.tsv> [<out.json>]   (pairs.tsv = 119's joined positions: columns program kind owner index
       name ... inator (the fragment) ... ours)"""
import collections, csv, json, re, sys

DYNAMIC = re.compile(r"\b(Rc|Arc|RefCell|Cell|UnsafeCell|Mutex|RwLock|Weak|OnceCell)<")
NAME = {"running-example": "example"}


def strip_outer_ghost(t):
    t = t.strip()
    return t[len("ghost<"):-1].strip() if t.startswith("ghost<") and t.endswith(">") else t


def bucket(fragment):
    t = strip_outer_ghost(fragment)
    if DYNAMIC.search(t):
        return "dynamic"
    if t == "unknown":
        return "unknown"
    return "static-unknown-pointee" if "unknown" in t else "static"


def main():
    rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
    out = {}
    for scope in ("sig", "all"):
        t = collections.defaultdict(collections.Counter)
        for r in rows:
            if scope == "sig" and r["kind"] == "field":
                continue
            b = bucket(r["inator"])
            for p in (NAME.get(r["program"], r["program"]), "total"):
                c = t[p]
                c["before"] += 1
                c["inator-" + ("static" if b.startswith("static") else b)] += 1
                if b == "static-unknown-pointee":
                    c["inator-static.unknown-pointee"] += 1
                c["ours-safe"] += r["ours"] in ("ref", "mut", "box")
                c["ours-raw"] += r["ours"] == "raw"
        for p, c in t.items():
            if c["before"] != c["inator-static"] + c["inator-dynamic"] + c["inator-unknown"] or c["before"] != c["ours-safe"] + c["ours-raw"]:
                raise SystemExit("partition " + p)
        out[scope] = {p: dict(c) for p, c in t.items()}
    if len(sys.argv) > 2:
        json.dump(out, open(sys.argv[2], "w"), indent=1, sort_keys=True)
    for scope in out:
        print(scope)
        for p in ["example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp", "total"]:
            c = out[scope][p]
            print("  %-8s before %3d static %3d (unknown-pointee %2d) dynamic %3d unknown %3d | ours safe %3d raw %3d" % (
                p, c["before"], c.get("inator-static", 0), c.get("inator-static.unknown-pointee", 0), c.get("inator-dynamic", 0),
                c.get("inator-unknown", 0), c["ours-safe"], c["ours-raw"]))


if __name__ == "__main__":
    main()
