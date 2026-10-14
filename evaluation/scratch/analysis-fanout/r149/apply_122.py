#!/usr/bin/env python3
"""apply_122.py -- analysis-fanout 122 (relay 149 B, R1091-2): CROWN's and Laertes's tools timed on the twenty.
New keys (pending), inserted after the last rq3.<non-inator> row (rq3.rest.sloc):
  rq3.crown.<p>.analysis-s (20), rq3.crown.total-s, rq3.crown.median-s, rq3.crown.reported-s (status: no per-program table)
  rq3.laertes.<p>.analysis-s (20; seconds, or the status text where the tool does not complete), rq3.laertes.timed,
  rq3.laertes.total-s, rq3.laertes.median-s (over the programs timed).
Input: docs origin/main:paper/numbers-of-record.md; r149/crown.tsv, laertes.tsv (tables.py). Output r149/record-122.md.
Fails closed."""
import csv, hashlib, re, statistics, subprocess
from decimal import Decimal

R = "scratch/analysis-fanout/r149"
DOCS = "crat/docs"
PROGS = "avl binn brotli bst buffer bzip2 genann heman ht json.h libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser".split()
LL = {"bzip2", "genann", "libcsv", "libzahl", "lil", "robotfindskitten", "tulipindicators", "urlparser"}
ROW = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) "
                 r"\| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")
HOST = ("host host-a (AMD Ryzen 9 9950X, 16 cores / 32 threads, 128 GiB installed, MemTotal 121 GiB), 2026-10-14 "
        "05:25-05:39Z (CROWN 05:25:00-05:27:1x, Laertes 05:36-05:39:11), after 60s' landed "
        "(32d966b9f) with no gate, census or corpus lock open")
PROTO = ("one program at a time, one throw-away container per run (--rm --network none --memory 48g), 3 trials, the value "
         "= the MIN wall (mean and max in r149/crown.tsv / laertes.tsv), GNU time -v around the whole tool invocation; the "
         "lane's window checked before every run AND at its end (no corpus lock, no open census / scan / gate, "
         "MemAvailable >= 65 GiB, 1-min load < 2.0, no rustc / cargo / z3 / crat / crown / resolve-lifetimes / miri / cc / ld "
         "process outside the run): a run the end check failed was set aside and repeated (2 repeats in the first Laertes "
         "pass, none in the passes of record); load sampled every 30 s (r149/load.tsv; 1-min load at the runs' starts "
         "0.70-1.90); a first attempt at 05:17Z was discarded because another lane's cargo build was running")
CROWN_DEF = ("CROWN's artifact image crown:latest (unmodified; the PLDI'23 artifact's tool at target/release/crown, toolchain "
             "nightly-2023-01-26) with the artifact's OWN configuration (run.sh's per-program options: lil "
             "--type-reconstruction --no-attempt with one regex of the alternatives .*fnc_.* / do_exit / lil_find_var / "
             "lil_to_double (joined by a bar), lodepng --no-attempt with bpmnode_create / uivector_resize, quadtree --force-box, genann --raw-mutability, the rest none) on the image's "
             "benchmark/<p> = benchmarks/rs-crown/<p> byte for byte; the wall covers the three crown calls the artifact makes "
             "per program in the image -- preprocess and explicit-addr (preprocess.sh) and rewrite (the image's run.sh: "
             "the ownership analysis and the rewrite in one call, writing analysis_results) -- the per-step split in "
             "crown.tsv; excluded: preprocess.sh's cargo build --release (a no-op on the built image) and the summarise "
             "call the host copy of the artifact's run.sh adds after rewrite (statistics; the image's run.sh has none); every trial's output tree equals the distributed benchmarks/rs-crown-transformed/<p> file "
             "for file (all 20 programs, 0 differing lines)")
LAE_DEF = ("the Laertes artifact image aliasing-limits-oopsla23:final (Zenodo 10.5281/zenodo.7714175, sha256:20b9f999, the "
           "2023 tool, toolchain nightly-2020-10-15), invoked as cargo run --release --bin resolve-lifetimes (the wall "
           "includes cargo's freshness check of the prebuilt binary and the tool's own initial compile, its rewrite "
           "iterations and the rustc check of each). Inputs and commands of record by where the artifact's Laertes tree "
           "came from: CROWN's eleven (laertes-crown; avl binn bst buffer heman ht json.h libtree lodepng quadtree rgba): "
           "-f --emulate-lifetime-only, the command CROWN's distributed logs (after/<p>/resolve-lifetimes-output.txt) show, "
           "on comparison/laertes-crown/before/<p> with the crate-root header of the artifact's Laertes output (the three "
           "gates the 2020 toolchain rejects removed, its const_fn_fn_ptr_basics / const_mut_refs added; binn also "
           "rustc_private for its extern crate libc; r149/in2/ADAPTATION.tsv); Laertes's own eight (laertes-laertes): the "
           "image's own initial-benchmarks/<p> unchanged with its own invocation and the artifact's baseline flags -f "
           "--merge-field-lifetimes --emulate-lifetime-only (the trees CROWN distributes for these eight are the 2021 "
           "tool's output, which this mode emulates; the 2023 tool's output differs from them in form, e.g. const fn new "
           "against impl Default); brotli: benchmark/brotli with 050's V2 header (no Laertes tree exists; CROWN's README: "
           "the tool crashes on it). The CROWN-eleven trees match the distributed ones up to avl 3, bst 1, ht 3, json.h 5, "
           "libtree 1, lodepng 25, buffer 119 differing lines")


def die(m):
    raise SystemExit("apply_122: FAIL: " + m)


def reg(p):
    return {"json.h": "jsonh"}.get(p, p)


def rows_of(f):
    return {r["program"]: r for r in csv.DictReader(open(R + "/" + f), delimiter="\t")}


cr, la = rows_of("crown.tsv"), rows_of("laertes.tsv")
if set(cr) != set(PROGS) or set(la) != set(PROGS):
    die("program sets")
FAIL = {
    "binn": "no time: the tool panics (E0603 'module unix is private', a diagnostic it cannot handle) on the distributed "
            "before-tree (header adapted, r149/in2/ADAPTATION.tsv), whose 1,720 libc:: uses the artifact's Laertes tree does not have "
            "(that tree came from another translation)",
    "brotli": "no time: the initial program does not compile in the tool's environment (E0463: c2rust_bitfields not found); "
              "CROWN's README: the tool crashes on brotli, no Laertes tree exists",
    "heman": "no time: the tool panics (E0308 type mismatch it cannot handle, kazmath/aabb2.rs) on the distributed "
             "before-tree (header adapted, r149/in2/ADAPTATION.tsv; the panic is in a file the adaptation does not touch); the "
             "authors' log in CROWN's artifact (after/heman/resolve-lifetimes-output.txt), same command, has the status line "
             "'DONE: The compiler successfully compiles the code' after 7 iterations",
    "quadtree": "no time: the tool panics (E0308 type mismatch it cannot handle, node.rs) on the distributed before-tree; "
                "(header adapted, r149/in2/ADAPTATION.tsv; the panic is in a file the adaptation does not touch); the authors' log in "
                "CROWN's artifact, same command, has the status line 'DONE: The compiler successfully compiles the code' after "
                "1 iteration",
    "rgba": "no time: the tool panics (E0308 type mismatch it cannot handle, test.rs) on the distributed before-tree; "
            "(header adapted, r149/in2/ADAPTATION.tsv; the panic is in a file the adaptation does not touch); the authors' log in "
                "CROWN's artifact, same command, has the status line 'DONE: The compiler successfully compiles the code' after "
                "1 iteration",
}
new = []
cw = {}
for p in PROGS:
    r = cr[p]
    if not r.get("wall_min_s") or r["trials"] != "3":
        die("crown " + p)
    cw[p] = float(r["wall_min_s"])
    new.append(("rq3.crown.%s.analysis-s" % reg(p), r["wall_min_s"], "seconds",
                "analysis-fanout 122 (relay 149 B, R1091-2): CROWN timed by us: %s; %s; %s; trials 3: min %s / mean %s / max "
                "%s s, user %s s and sys %s s at the min, max RSS %s MB; steps at the min: %s" % (
                    CROWN_DEF.split(" on the image's")[0] + ", on benchmarks/rs-crown/%s" % p, HOST, PROTO, r["wall_min_s"],
                    r["wall_mean_s"], r["wall_max_s"], r["user_s_at_min"], r["sys_s_at_min"], r["maxrss_mb"],
                    r["steps_at_min"].replace("steps_ns ", "ns "))))
cmed = statistics.median(Decimal(cr[p]["wall_min_s"]) for p in PROGS)  # exact: GNU time prints 2 decimals
new.append(("rq3.crown.total-s", str(sum(Decimal(cr[p]["wall_min_s"]) for p in PROGS)), "seconds",
            "analysis-fanout 122 (relay 149 B, R1091-2): the sum over the twenty rq3.crown.<p>.analysis-s (each the min of 3 "
            "trials); %s; %s; %s" % (CROWN_DEF, HOST, PROTO)))
new.append(("rq3.crown.median-s", str(cmed), "seconds",
            "analysis-fanout 122 (relay 149 B, R1091-2): the median over the twenty rq3.crown.<p>.analysis-s; " + HOST))
new.append(("rq3.crown.reported-s", "no per-program times published", "status",
            "analysis-fanout 122 (relay 149 B.4): CROWN's paper (A03, p. 18, RQ3): 'The execution time of the analysis and "
            "the rewrite for the whole benchmark suite is within 60 seconds.' (p. 2 and p. 19: 'half a million LOC in less "
            "than 10 seconds', its scalability claim); the artifact's README (Runtime Performance): 'time ./run.sh ... On "
            "our machine, the above command terminates roughly within 1 min.'; no per-program table in either"))
lw = {}
for p in PROGS:
    r = la[p]
    if r.get("wall_min_s"):
        if r["trials"] != "3" or p in FAIL:
            die("laertes " + p)
        lw[p] = float(r["wall_min_s"])
        src = ("Laertes's own initial-benchmarks/%s, -f --merge-field-lifetimes --emulate-lifetime-only" % p if p in LL else
               "CROWN's laertes-crown before/%s (header of record), -f --emulate-lifetime-only" % p)
        new.append(("rq3.laertes.%s.analysis-s" % reg(p), r["wall_min_s"], "seconds",
                    "analysis-fanout 122 (relay 149 B, R1091-2): Laertes timed by us on %s: exit 0, DONE after %s iteration(s); "
                    "trials 3: min %s / mean %s / max %s s, user %s s and sys %s s at the min, max RSS %s MB; %s; %s" % (
                        src, r["t1_iterations"], r["wall_min_s"], r["wall_mean_s"], r["wall_max_s"], r["user_s_at_min"],
                        r["sys_s_at_min"], r["maxrss_mb"], HOST, PROTO)))
    else:
        if p not in FAIL:
            die("laertes failure without a status: " + p)
        if "|" in FAIL[p]:
            die("pipe")
        new.append(("rq3.laertes.%s.analysis-s" % reg(p), FAIL[p].split(":")[0] + ": " + {
            "binn": "panics on the distributed before-tree", "brotli": "does not compile in the tool's environment",
            "heman": "panics on the distributed before-tree", "quadtree": "panics on the distributed before-tree",
            "rgba": "panics on the distributed before-tree"}[p] + " (header adapted)", "status",
            "analysis-fanout 122 (relay 149 B.2): %s (trial 1 exit %s; the failure text in r149/out/laertes2/%s/t1/; only "
            "programs where the tool completes are timed); %s" % (FAIL[p], r["t1_exit"], p, HOST)))
if len(lw) != 15:
    die("laertes timed %d" % len(lw))
new.append(("rq3.laertes.timed", str(len(lw)), "count",
            "analysis-fanout 122 (relay 149 B.2): programs on which Laertes completes and is timed, of the twenty (no time: "
            "binn, brotli, heman, quadtree, rgba); " + LAE_DEF))
new.append(("rq3.laertes.total-s", str(sum(Decimal(la[p]["wall_min_s"]) for p in lw)), "seconds",
            "analysis-fanout 122 (relay 149 B, R1091-2): the sum over the 15 timed rq3.laertes.<p>.analysis-s (each the min "
            "of 3 trials); %s; %s; %s" % (LAE_DEF, HOST, PROTO)))
new.append(("rq3.laertes.median-s", str(statistics.median(Decimal(la[p]["wall_min_s"]) for p in lw)), "seconds",
            "analysis-fanout 122 (relay 149 B, R1091-2): the median over the 15 timed rq3.laertes.<p>.analysis-s; " + HOST))

raw = subprocess.run(["git", "-C", DOCS, "show", "origin/main:paper/numbers-of-record.md"], capture_output=True,
                     check=True).stdout
lines = raw.decode("utf-8").split("\n")
keys = {}
for i, l in enumerate(lines):
    m = ROW.match(l)
    if m and not l.startswith("| key |"):
        keys[m.group("key")] = i
for k, *_ in new:
    if k in keys:
        die("key exists: " + k)
anchor = keys.get("rq3.rest.sloc")
if anchor is None:
    die("anchor")
ins = []
for k, v, unit, prov in new:
    if "|" in prov or "|" in v:
        die("pipe in " + k)
    ins.append("| %s | %s | pending | n/a | %s | %s |" % (k, v, unit, prov))
out = lines[:anchor + 1] + ins + lines[anchor + 1:]
text = "\n".join(out)
open(R + "/record-122.md", "w", encoding="utf-8", newline="").write(text)
open(R + "/new-keys-122.tsv", "w").write("key\tvalue\tunit\n" + "".join("%s\t%s\t%s\n" % x[:3] for x in new))
print("in md5", hashlib.md5(raw).hexdigest(), "out md5", hashlib.md5(text.encode()).hexdigest(), "inserted", len(ins))
print("crown total %.2f median %.2f; laertes timed %d total %.2f median %.2f" % (
    sum(cw.values()), cmed, len(lw), sum(lw.values()), statistics.median(lw.values())))
