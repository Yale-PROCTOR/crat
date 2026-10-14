#!/usr/bin/env python3
"""sig.py -- relay 150 item 1 (S64, tab:effect-inator): per program, over 119's joined positions (r145/pairs.tsv:
&inator's type by R1082-1 = `theirs` + `theirs_cell`, ours = our emitted type at the landed 32d966b9f), the signature
positions (kind param or return; fields excluded) and, as the alternative, all positions (fields included).
inator-static = theirs ref/mut/box NOT Cell-flagged; inator-dynamic = theirs rc + every Cell-flagged non-rc position;
inator-byvalue / inator-unknown = by-value / unknown NOT Cell-flagged (a partition of before).
Alternative (Cell ignored): static = ref + mut + box, dynamic = rc.  ours-safe = ref + mut + box; ours-raw = raw."""
import collections, csv, json, sys
R = "scratch/analysis-fanout/r145/pairs.tsv"
NAME = {"running-example": "example"}
out = {}
for scope in ("sig", "all"):
    t = collections.defaultdict(collections.Counter)
    for r in csv.DictReader(open(R), delimiter="\t"):
        if scope == "sig" and r["kind"] == "field":
            continue
        for p in (NAME.get(r["program"], r["program"]), "total"):
            c = t[p]
            b, cell, o = r["theirs"], r["theirs_cell"] == "1", r["ours"]
            c["before"] += 1
            if b in ("ref", "mut", "box") and not cell:
                c["inator-static"] += 1
            elif b == "rc" or cell:
                c["inator-dynamic"] += 1
            elif b in ("by-value", "byvalue"):
                c["inator-byvalue"] += 1
            elif b == "unknown":
                c["inator-unknown"] += 1
            else:
                raise SystemExit("bucket " + b)
            c["alt.inator-static"] += b in ("ref", "mut", "box")
            c["alt.inator-dynamic"] += b == "rc"
            c["ours-safe"] += o in ("ref", "mut", "box")
            c["ours-raw"] += o == "raw"
            if o not in ("ref", "mut", "box", "raw"):
                raise SystemExit("ours " + o)
    for p, c in t.items():
        assert c["before"] == c["inator-static"] + c["inator-dynamic"] + c["inator-byvalue"] + c["inator-unknown"]
        assert c["before"] == c["ours-safe"] + c["ours-raw"]
    out[scope] = {p: dict(c) for p, c in t.items()}
json.dump(out, open("sig.json", "w"), indent=1, sort_keys=True)
for scope in out:
    print(scope)
    for p in ["example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp", "total"]:
        c = out[scope][p]
        print("  %-8s %s" % (p, " ".join("%s=%d" % (k, c.get(k, 0)) for k in ["before", "inator-static", "inator-dynamic", "inator-byvalue", "inator-unknown", "alt.inator-static", "alt.inator-dynamic", "ours-safe", "ours-raw"])))
