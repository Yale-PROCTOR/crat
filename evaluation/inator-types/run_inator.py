"""relay 143: &inator's interface positions, trial 1 of the shipped image (tisp: the source-built binary, diag/), plus
the trial-identity and image-vs-source checks on the same unit."""
import glob, os, sys, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import positions as P
B = "inator-outputs"
PROGS = ["running-example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]
def res(root, p, trial):
    g = glob.glob(f"{B}/{root}/runs/{p}/trial-{trial}/benchmarks/{p}/results/*/rtypes.txt")
    return os.path.dirname(g[0]) if g else None
def key(r): return (r["kind"], r["owner"], r["index"], r["bucket"], r["rtype"])
out = {}
checks = {}
for p in PROGS:
    src = res("img", p, 1)
    binary = "image (shipped binary), trial 1"
    if src is None:
        src = res("diag/diag", p, 1); binary = "source-built binary at the pinned commit (diag/), trial 1"
    rows, defs, decl = P.inator_rows(src)
    out[p] = {"binary": binary, "dir": src, "rows": rows, "defined": sorted(defs), "declared": sorted(decl)}
    # trial identity on the unit
    base = sorted(key(r) for r in rows)
    diffs = []
    for t in range(2, 6):
        d = res("img", p, t)
        if d:
            other = sorted(key(r) for r in P.inator_rows(d)[0])
            # compare by position + bucket (lifetime labels differ between runs)
            a = sorted(k[:4] for k in base); b2 = sorted(k[:4] for k in other)
            diffs.append((t, a == b2))
    dg = res("diag/diag", p, 1)
    img_vs_src = None
    if dg and res("img", p, 1):
        img_vs_src = sorted(k[:4] for k in base) == sorted(k[:4] for k in (key(r) for r in P.inator_rows(dg)[0]))
    checks[p] = {"trials_same": diffs, "image_vs_source_same": img_vs_src}
    c = collections.Counter(r["bucket"] for r in rows)
    print(p, len(rows), dict(c), "| trials", diffs, "| img=src", img_vs_src, "|", binary)
json.dump({"out": out, "checks": checks}, open("inator-positions.json", "w"), indent=1)
