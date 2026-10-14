"""relay 145 (R1082-1): &inator's buckets with the outermost ghost stripped. The first constructor INSIDE the outermost
ghost (and inside the mu qualifiers Cell / RefCell / [] / [Cell], recorded as flags) decides:
&'n mut -> mut, &'n -> ref, Box -> box, Rc -> rc, unknown -> unknown, a scalar / struct / an inner ghost (no pointer
constructor: the referent stored by value) -> byvalue. The interior-mutable flag = Cell (or RefCell) anywhere in the fragment.
Reads r143/reconcile.json (the 317 positions, &inator's de-labelled fragment per position); writes rebucket.tsv / table."""
import json, re, collections, csv, sys
R = json.load(open("reconcile.json"))["rows"]
def die(m): raise SystemExit("rebucket: FAIL: " + m)
def classify(t):
    t = t.strip()
    ghost = False
    if t.startswith("ghost<") and t.endswith(">"):
        t = t[6:-1].strip(); ghost = True
    cell = bool(re.search(r"\b(Cell|RefCell)<", t))
    refcell = bool(re.search(r"\bRefCell<", t))
    # peel the mu qualifiers
    for _ in range(4):
        m = re.match(r"^(?:Cell|RefCell)<(.*)>$", t)
        if m:
            t = m.group(1).strip(); continue
        m = re.match(r"^\[(.*)\]$", t)
        if m:
            t = m.group(1).strip(); continue
        break
    if re.match(r"^&'\d+ mut ", t): return "mut", cell, refcell, ghost
    if re.match(r"^&'\d+ ", t): return "ref", cell, refcell, ghost
    if t.startswith("Box<"): return "box", cell, refcell, ghost
    if t.startswith("Rc<"): return "rc", cell, refcell, ghost
    if t == "unknown" or t.startswith("unknown"): return "unknown", cell, refcell, ghost
    if t.startswith("ghost<") or re.match(r"^(struct\(|i\d+|f\d+|bool|void)", t): return "byvalue", cell, refcell, ghost
    die("unclassified fragment: %r" % t)
P = ["running-example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]
B = ["ref", "mut", "box", "rc", "byvalue", "unknown"]
rows = []
for r in R:
    b, cell, refcell, ghost = classify(r["inator"])
    rows.append(dict(r, new_bucket=b, cell_flag=int(cell), refcell_flag=int(refcell), outer_ghost=int(ghost)))
with open("rebucket.tsv", "w") as f:
    w = csv.writer(f, delimiter="\t", lineterminator="\n")
    w.writerow(["program", "kind", "owner", "index", "name", "inator_type", "old_bucket", "new_bucket", "cell_flag", "outer_ghost"])
    for r in rows:
        w.writerow([r["program"], r["kind"], r["owner"], r["index"], r["name"], r["inator"], r["bucket"], r["new_bucket"], r["cell_flag"], r["outer_ghost"]])
tot = collections.Counter(); totc = collections.Counter(); out = []
print("| program | positions | " + " | ".join(B) + " | cell-flag (of which: " + "/".join(B) + ") | old ghost -> |")
for p in P:
    rs = [r for r in rows if r["program"] == p]
    c = collections.Counter(r["new_bucket"] for r in rs); cf = collections.Counter(r["new_bucket"] for r in rs if r["cell_flag"])
    g = collections.Counter(r["new_bucket"] for r in rs if r["bucket"] == "ghost")
    tot.update(c); totc.update(cf)
    print(f"| {p} | {len(rs)} | " + " | ".join(str(c.get(b, 0)) for b in B) + f" | {sum(cf.values())} ({'/'.join(str(cf.get(b,0)) for b in B)}) | {dict(g)} |")
print(f"| total | {sum(tot.values())} | " + " | ".join(str(tot.get(b, 0)) for b in B) + f" | {sum(totc.values())} ({'/'.join(str(totc.get(b,0)) for b in B)}) | |")
print("refcell flags", sum(r["refcell_flag"] for r in rows))
json.dump({"rows": rows}, open("rebucket.json", "w"), indent=1)
