#!/usr/bin/env python3
"""tables.py -- relay 149 B: the CROWN and Laertes timing tables from r149/out/{crown,laertes2}/<p>/t<k>/ (contaminated
repeats, t<k>.contaminated.<n>, are excluded) and the first Laertes pass (out/laertes, inputs with only the three gates
dropped) as a variant. Per run: GNU time's wall (Elapsed), user, sys, max RSS; CROWN's three step times; the host's
1-min load sampled every 30 s (load.tsv) within [start, end] plus the driver's load at the run's start.
Each output tree is compared with the tree of record: CROWN -> benchmarks/rs-crown-transformed/<p>; Laertes ->
crown-artifact/comparison/laertes-{crown,laertes}/after/<p> (brotli has none).
Writes crown.tsv, laertes.tsv, laertes-pass1.tsv, summary.txt."""
import csv, filecmp, os, re, statistics, subprocess

R = os.path.dirname(os.path.abspath(__file__))
PROGS = "avl binn brotli bst buffer bzip2 genann heman ht json.h libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser".split()
LL = ["bzip2", "genann", "libcsv", "libzahl", "lil", "robotfindskitten", "tulipindicators", "urlparser"]
CA = "crown-artifact/comparison"


def gt(path):
    t = open(path).read()
    def f(lbl):
        m = re.search(re.escape(lbl) + r": (.*)", t)
        return m.group(1).strip() if m else None
    w = f("Elapsed (wall clock) time (h:mm:ss or m:ss)")
    parts = [float(x) for x in w.split(":")]
    wall = parts[-1] + 60 * parts[-2] + (3600 * parts[-3] if len(parts) == 3 else 0)
    return wall, float(f("User time (seconds)")), float(f("System time (seconds)")), int(f("Maximum resident set size (kbytes)"))


def kv(path):
    d = {}
    if os.path.exists(path):
        for l in open(path):
            if "=" in l:
                k, v = l.strip().split("=", 1)
                d[k] = v
    return d


def tree_cmp(a, b):
    """(files equal, files differing, only-in-a, only-in-b, differing lines) over *.rs files."""
    def rs(root):
        out = set()
        for d, _, fs in os.walk(root):
            for x in fs:
                if x.endswith(".rs"):
                    out.add(os.path.relpath(os.path.join(d, x), root))
        return out
    A, B = rs(a), rs(b)
    eq = sum(1 for x in A & B if filecmp.cmp(os.path.join(a, x), os.path.join(b, x), shallow=False))
    nd = 0
    for x in A & B:
        la = open(os.path.join(a, x), errors="replace").read().splitlines()
        lb = open(os.path.join(b, x), errors="replace").read().splitlines()
        if la != lb:  # GNU diff --minimal: changed lines on both sides
            out = subprocess.run(["diff", "--minimal", os.path.join(a, x), os.path.join(b, x)], capture_output=True).stdout
            nd += sum(1 for l in out.decode(errors="replace").splitlines() if l[:2] in ("< ", "> "))
    return eq, len(A & B) - eq, len(A - B), len(B - A), nd


def runlog(name):
    starts = {}
    for l in open(os.path.join(R, name)):
        m = re.match(r"^(\S+) RUN (\S+) (\S+) (t\d) load=(\S+)", l)
        if m:
            starts[(m.group(2), m.group(3), m.group(4))] = (m.group(1), m.group(5))
    return starts


load = [(l.split("\t")[0], float(l.split("\t")[1].split()[0])) for l in open(R + "/load.tsv") if "\t" in l]


def maxload(t0, t1):
    xs = [v for t, v in load if t0 <= t <= t1]
    return max(xs) if xs else None


def table(tool, log, out, rec):
    starts = runlog(log)
    rows = []
    for p in PROGS:
        walls, rec_eq = [], []
        st = kv("%s/out/%s/%s/t1/status" % (R, tool, p))
        for k in (1, 2, 3):
            d = "%s/out/%s/%s/t%d" % (R, tool, p, k)
            if not os.path.exists(d + "/status"):
                continue
            s = kv(d + "/status")
            if s.get("exit") != "0" or (tool != "crown" and s.get("done") in (None, "0")):
                continue
            wall, u, sy, rss = gt(d + "/time.txt")
            steps = open(d + "/steps").read().strip() if os.path.exists(d + "/steps") else ""
            t0, l0 = starts.get((tool, p, "t%d" % k), ("", ""))
            walls.append((wall, u, sy, rss, steps, l0))
            r = rec(p)
            rec_eq.append(tree_cmp(d + "/tree", r) if r else None)
        row = {"program": p, "t1_exit": st.get("exit", "-"), "t1_iterations": st.get("iterations", "-"),
               "t1_done": st.get("done", "-"), "trials": len(walls)}
        if walls:
            w = [x[0] for x in walls]
            row.update({"wall_min_s": "%.2f" % min(w), "wall_mean_s": "%.2f" % statistics.mean(w), "wall_max_s": "%.2f" % max(w),
                        "user_s_at_min": "%.2f" % walls[w.index(min(w))][1], "sys_s_at_min": "%.2f" % walls[w.index(min(w))][2],
                        "maxrss_mb": "%.0f" % (max(x[3] for x in walls) / 1024), "steps_at_min": walls[w.index(min(w))][4],
                        "load1_at_starts": ",".join(x[5] for x in walls),
                        "tree_vs_record": ";".join("eq%d/diff%d/onlyrun%d/onlyrec%d/lines%d" % c if c else "no-record" for c in rec_eq)})
        else:
            err = ""
            e = "%s/out/%s/%s/t1/stderr" % (R, tool, p)
            if os.path.exists(e):
                lines = [l.strip() for l in open(e, errors="replace") if re.search(r"panicked|^error|ERROR: The initial", l)]
                err = lines[0][:220] if lines else ""
                so = [l.strip() for l in open("%s/out/%s/%s/t1/stdout" % (R, tool, p), errors="replace") if l.startswith(("ERROR", "DONE"))]
                err = (so[0][:160] + " | " if so else "") + err
            row["failure"] = err.replace("\t", " ")
        rows.append(row)
    keys = []
    for r in rows:
        for k in r:
            if k not in keys:
                keys.append(k)
    with open(R + "/" + out, "w") as f:
        w = csv.DictWriter(f, fieldnames=keys, delimiter="\t", lineterminator="\n", restval="")
        w.writeheader()
        w.writerows(rows)
    return rows


crown = table("crown", "run-all.log", "crown.tsv", lambda p: "crat/benchmarks/rs-crown-transformed/%s" % p)
lae = table("laertes2", "run-laertes2.log", "laertes.tsv",
            lambda p: None if p == "brotli" else "%s/%s/after/%s" % (CA, "laertes-laertes" if p in LL else "laertes-crown", p))
lae1 = table("laertes", "run-all.log", "laertes-pass1.tsv",
             lambda p: None if p == "brotli" else "%s/%s/after/%s" % (CA, "laertes-laertes" if p in LL else "laertes-crown", p))
with open(R + "/summary.txt", "w") as f:
    for name, rows in (("crown", crown), ("laertes", lae), ("laertes-pass1", lae1)):
        timed = [float(r["wall_min_s"]) for r in rows if r.get("wall_min_s")]
        f.write("%s: timed %d / 20; total of mins %.2f s; median %.2f s; failures %s\n" % (
            name, len(timed), sum(timed), statistics.median(timed) if timed else 0,
            [r["program"] for r in rows if not r.get("wall_min_s")]))
print(open(R + "/summary.txt").read())
