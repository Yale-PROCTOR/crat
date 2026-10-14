"""relay 145 section 2: the pairs (theirs by R1082-1's buckets, ours by the emitted type) classified; plus the seat's
name-join cross-check (parameters matched by function + parameter name, main <-> main_0).
usage: pairs.py <ours-positions.tsv>"""
import csv, json, collections, sys
csv.field_size_limit(10 ** 9)
reb = {(r["program"], r["kind"], r["owner"], r["index"]): r for r in json.load(open("rebucket.json"))["rows"]}
ours = list(csv.DictReader(open(sys.argv[1]), delimiter="\t", quoting=csv.QUOTE_NONE))
rec = json.load(open("reconcile.json"))
inj = json.load(open("inator-positions.json"))
def cls(t, o, cell):
    if t in ("ref", "mut") and o in ("ref", "mut"): return "both reference"
    if t == "box" and o == "box": return "both Box"
    if o == "raw" and (t in ("rc", "byvalue") or cell): return "theirs rc / by-value / interior-mutable vs ours raw"
    if o == "raw" and t in ("ref", "mut"): return "theirs & / &mut vs ours raw (the residue)"
    if o in ("ref", "mut", "box") and t in ("unknown", "byvalue"): return "ours safe vs theirs unknown / by-value"
    if o == "raw" and t == "unknown": return "both without a safe form (theirs unknown, ours raw)"
    if o == "raw" and t == "box": return "theirs Box vs ours raw"
    return "theirs %s vs ours %s" % (t, o)
mat = collections.Counter(); cl = collections.Counter(); per = collections.defaultdict(collections.Counter); out = []
for r in ours:
    k = None
    for kk, v in reb.items():
        if kk[0] == r["program"] and kk[1] == r["kind"] and int(kk[3]) == int(r["index"]) and v["c_owner"] == r["owner"]:
            k = kk; break
    if k is None: raise SystemExit("pairs: no &inator row for %r" % r)
    t = reb[k]["new_bucket"]; cell = reb[k]["cell_flag"]
    c = cls(t, r["ours"], cell)
    mat[(t + ("+cell" if cell else ""), r["ours"])] += 1; cl[c] += 1; per[r["program"]][c] += 1
    out.append(dict(r, theirs=t, theirs_cell=cell, pair_class=c))
un = sum(len(rec["summary"][p]["only_inator"]) + len(rec["summary"][p]["only_c2rust"]) for p in rec["summary"])
print("pairs:", len(out), "+ one-sided", un)
for c, n in cl.most_common(): print("  %-60s %d" % (c, n))
print("matrix (theirs x ours):"); [print("  ", k, n) for k, n in sorted(mat.items())]
with open("pairs.tsv", "w") as f:
    w = csv.DictWriter(f, fieldnames=list(out[0].keys()), delimiter="\t", lineterminator="\n"); w.writeheader(); [w.writerow(x) for x in out]
# the seat's name join: parameters by function + parameter name
names_ok = sum(1 for r in rec["rows"] if r["kind"] == "param")
same = 0; diff = []
for r in rec["rows"]:
    if r["kind"] != "param": continue
    inr = [x for x in inj["out"][r["program"]]["rows"] if x["kind"] == "param" and x["owner"] == r["owner"] and x["index"] == r["index"]]
    if inr and inr[0]["name"] == r["c_name"]: same += 1
    else: diff.append((r["program"], r["owner"], r["index"], r["c_name"], inr[0]["name"] if inr else None))
print("name join: %d of %d pointer parameters carry the same name on both sides; differ: %s" % (same, names_ok, diff[:10]))
