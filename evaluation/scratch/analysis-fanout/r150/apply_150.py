#!/usr/bin/env python3
"""apply_150.py -- analysis-fanout 123 (relay 150): the paper's pending keys. Fails closed.
Input docs origin/main:paper/numbers-of-record.md; output r150/record-123.md; r150/new-keys-123.tsv.
1 S64  new rq1.inator.<p>.sig.{before,inator-static,inator-dynamic,inator-byvalue,inator-unknown,ours-safe,ours-raw}
       (9 programs + total) from sig.json (sig.py over 119's r145/pairs.tsv), after the last rq3.inator.* row.
2 S65  122's rq3.crown.<p>.analysis-s / rq3.laertes.<p>.analysis-s / rq3.{crown,laertes}.total-s RENAMED to the
       table's rq3.<p>.crown-s / rq3.<p>.laertes-s / rq3.total.{crown,laertes}-s (rows kept in place, values from 122;
       Laertes's no-time cells a short status); a note on the 20 rq3.<p>.analysis-s and rq3.total.analysis-s.
3 rq4  a scope note on every rq4.* row (six-program of record under R817 / twenty-program frame-14u run / setting).
4 C:59 new layer1.already-reference (36) and layer1.held-first-order (918) after layer1.declarations; the identity.
5      a note on analysis.rounds.* / analysis.guarded.* (re-read against the solve's progress.jsonl); new
       analysis.rounds.cap-reached (0) after analysis.rounds.per-program.
6      a note on rq1.tests.{programs,passed,total} (54' harness, not 60s'; the six suites' key)."""
import hashlib, json, re, subprocess

R = "scratch/analysis-fanout/r150"
DOCS = "crat/docs"
ROW = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) "
                 r"\| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")
LOOSE = re.compile(r"^\| (?P<key>[^ |]+) \|")   # any table row, an empty value cell '| |' included
P9 = ["example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]
P20 = "avl binn brotli bst buffer bzip2 genann heman ht jsonh libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser".split()
L60 = ("60s' (the FINAL frame; landed 2026-10-14T03:39:27Z, assembler 151; borrow-ownership 32d966b9f; census main/"
       "batch60sp, main 225)")
T = "analysis-fanout 123 (relay 150 item %s, 10-14): "


def die(m):
    raise SystemExit("apply_150: FAIL: " + m)


def render(c):
    s = "| %s | %s | %s | %s | %s | %s |" % (c["key"], c["value"], c["status"], c["layer"], c["unit"], c["prov"])
    if ROW.match(s) is None or s.count("|") != 7:
        die("render " + c["key"])
    return s


raw = subprocess.run(["git", "-C", DOCS, "show", "origin/main:paper/numbers-of-record.md"], capture_output=True,
                     check=True).stdout
lines = raw.decode("utf-8").split("\n")
rows = {}
for i, l in enumerate(lines):
    m = LOOSE.match(l)
    if m and not l.startswith("| key |") and not l.startswith("|---"):
        if m.group("key") in rows:
            die("dup " + m.group("key"))
        rows[m.group("key")] = i
cell = lambda k: ROW.match(lines[rows[k]]).groupdict()
out = list(lines)
inserts = {}   # anchor key -> list of new rows (inserted after the anchor)
log = []


def note(k, text):
    """insert text at the start of the provenance cell (after the 6th '|' and its space); every other byte kept."""
    l = out[rows[k]]
    if "|" in text:
        die("pipe in note " + k)
    pos = [i for i, ch in enumerate(l) if ch == "|"]
    if len(pos) < 7:
        die("cells " + k)
    j = pos[5] + 2
    out[rows[k]] = l[:j] + text + l[j:]
    v = l[pos[1] + 1:pos[2]].strip()
    log.append((k, "note", v, v))


def new(anchor, k, v, unit, layer, prov):
    if k in rows:
        die("exists " + k)
    if "|" in prov or "|" in v:
        die("pipe " + k)
    inserts.setdefault(anchor, []).append(render({"key": k, "value": v, "status": "pending", "layer": layer,
                                                  "unit": unit, "prov": prov}))
    log.append((k, "new", "-", v))


# ---------------------------------------------------------------- 1 S64
sig = json.load(open(R + "/sig.json"))
anchor1 = [k for k in rows if k.startswith("rq3.inator.")]
anchor1 = max(anchor1, key=lambda k: rows[k])
DEF1 = (T % 1 + "S64, Table tab:effect-inator: 119's interface positions of &inator's nine (r145/pairs.tsv: the 317 "
        "positions present on both sides, function pointers out; &inator's type by R1082-1, the outermost ghost stripped, "
        "with its Cell flag; ours = our EMITTED type at the landed 32d966b9f, the nine run at that same head (119, "
        "re-stamped landed by 120), a compile-check revert counting raw), restricted to the SIGNATURE positions the "
        "caption names (parameters and returns; the 38 struct fields out: %d of the 317). Mapping: before = the "
        "positions; inator-static = &inator ref + mut + box NOT Cell-flagged; inator-dynamic = &inator rc + every "
        "Cell-flagged position that is not rc (interior mutability: aliasing checked at run time); inator-byvalue / "
        "inator-unknown = &inator by-value (the pointer replaced by its referent) / unknown (its own polymorphic-pointer "
        "type), not Cell-flagged; these four partition before. ours-safe = ours ref + mut + box (& / &mut / slices / "
        "cursors / Box); ours-raw = ours raw; these two partition before. ALTERNATIVES (the user decides the caption; no "
        "value changes after): Cell as a flag ignored -> static = ref + mut + box, dynamic = rc (%s); with the struct "
        "fields counted (all 317 positions) -> %s (r150/sig.json)")
names = ["before", "inator-static", "inator-dynamic", "inator-byvalue", "inator-unknown", "ours-safe", "ours-raw"]
for p in P9 + ["total"]:
    s, a = sig["sig"][p], sig["all"][p]
    alt = "static %d, dynamic %d" % (s["alt.inator-static"], s["alt.inator-dynamic"])
    allf = "before %d, static %d, dynamic %d, by-value %d, unknown %d, ours safe %d, raw %d" % tuple(
        a.get(n, 0) for n in names)
    for n in names:
        v = s.get(n, 0)
        extra = "" if p != "total" else "; the sum over the nine program rows"
        new(anchor1, "rq1.inator.%s.sig.%s" % (p, n), str(v), "count", "delivered" if n.startswith("ours") else "n/a",
            DEF1 % (sig["sig"]["total"]["before"], alt, allf) + extra)

# ---------------------------------------------------------------- 2 S65
STATUS = {"binn": "crash", "heman": "crash", "quadtree": "crash", "rgba": "crash", "brotli": "does not compile"}
REN = T % 2 + ("S65: renamed to Table tab:scale-crown's key from 122's %s (value and measurement unchanged; 149 B.4's "
               "name withdrawn); ")
for p in P20:
    for tool in ("crown", "laertes"):
        old = "rq3.%s.%s.analysis-s" % (tool, p)
        if old not in rows:
            die("missing " + old)
        c = ROW.match(out[rows[old]]).groupdict()
        v = c["value"]
        if tool == "laertes" and p in STATUS:
            if not v.startswith("no time"):
                die("laertes status " + p)
            c["prov"] = ("the cell's value is the short status '%s' (the table prints the dagger; 122's status was '%s'); "
                         % (STATUS[p], v)) + c["prov"]
            v = STATUS[p]
        c["key"], c["value"] = "rq3.%s.%s-s" % (p, tool), v
        c["prov"] = REN % old + c["prov"]
        if c["key"] in rows:
            die("exists " + c["key"])
        out[rows[old]] = render(c)
        log.append((c["key"], "renamed from " + old, cell(old)["value"], v))
for tool in ("crown", "laertes"):
    old = "rq3.%s.total-s" % tool
    c = ROW.match(out[rows[old]]).groupdict()
    c["key"] = "rq3.total.%s-s" % tool
    c["prov"] = REN % old + c["prov"]
    out[rows[old]] = render(c)
    log.append((c["key"], "renamed from " + old, c["value"], c["value"]))
N2 = T % 2 + ("three programs at once on host-b; re-measured serially (era-5c 220) -- re-seeded when era-5c 174 "
              "lands; ")
for p in P20 + ["total"]:
    note("rq3.%s.analysis-s" % p, N2)

# ---------------------------------------------------------------- 3 rq4
W151 = ("wave-6o report 151 (relay 189, at the landed 32d966b9f): the six RQ4 trees at batch60sp are byte-identical "
        "to batch58pps39 (58''') (agents/artifacts/2026-10-14-wave-6o-151/tree-sha256-60sp-vs-58ppp.txt), so every "
        "verdict carries; value unchanged")
SIX = T % 3 + "SIX-program key (of record under R817: libtree, rgba, quadtree, urlparser, genann, buffer on their shipped suites); " + W151 + "; the paper's section RQ3 may print it; "
SET = T % 3 + "SETTING of the six-program runs (of record under R817); " + W151 + "; the paper may print it; "
TWENTY = T % 3 + ("TWENTY-program key of the frame-14u RQ4 design (the earlier whole-corpus runs; NOT of record "
                  "under R817, whatever census a value was last re-derived at); the paper cites the six only: "
                  "section RQ3 and Appendix C should not print it; ")
CONFIG = T % 3 + ("SETTING as the frame-14u run's facts state it (wave-6o 097, the twenty-program design: pass C, "
                  "harness-edits.txt); whether the six-program runs (wave-6o 118 / 149 / 151) used the same flags is "
                  "not shown in this row's provenance -- wave-6o confirms before the paper prints it (Appendix C "
                  "tab:rq4-config); ")
CENSUS = T % 3 + ("CENSUS LABEL: names the frame-14u census (4a47f16f7, the L01^14u cache), the one the RQ4 runs "
                  "last ran on; for the paper's six at 60s' the trees are byte-identical to 58" + "'" * 3 + " ("
                  + W151 + "), so the census of record for the six is main/batch60sp -- the seat restates the "
                  "value before Appendix C prints it; ")
cls = {}
for k in rows:
    if not k.startswith("rq4."):
        continue
    if k.startswith("rq4.suite."):
        cls[k] = SIX
    elif k in ("rq4.checker", "rq4.discipline"):
        cls[k] = SET
    elif k == "rq4.config":
        cls[k] = CONFIG
    elif k == "rq4.census":
        cls[k] = CENSUS
    else:
        cls[k] = TWENTY
for k, t in cls.items():
    note(k, t)

# ---------------------------------------------------------------- 4 C:59
IDN = ("identity at 60s' (main/batch60sp's 7,011 subject-outcome rows, r146 layers-d6.tsv): layer1.declarations 7,011 = "
       "rq1.frame-safe-decisions 3,612 (decided safe, R956-1 with D6) + layer1.held-first-order 918 (first-order-held "
       "subjects out of the denominator: pending 251, ref-beside 262, retained-access 404, backstop 1) + "
       "layer1.already-reference 36 + layer1.decided-raw 1,449 + layer1.excluded-items 996; without the holds row "
       "Appendix C's sub-rows add up to 6,093")
new("layer1.declarations", "layer1.already-reference", "36", "count", "decided",
    T % 4 + "Appendix C:59: the already-reference bindings -- c2rust's `let ref mut freshN` bindings, references in the "
    "input, not decided (R454: agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv, "
    "counts_toward_N == true), re-derived at 60s': all 36 join main/batch60sp's census subjects on (program, owner_fn, "
    "binding) (family ref, decision degraded, delivery degraded; r150/already_ref.py); the 36 the realization "
    "denominator leaves out (decided safe 4,566 less R454's 36 = 4,530); " + IDN + "; " + L60)
new("layer1.declarations", "layer1.held-first-order", "918", "count", "decided",
    T % 4 + "Appendix C:59's missing sub-row: the decided-safe subjects held out of the realization denominator under "
    "R956-1 with D6 (pending 251, ref-beside 262, retained-access 404, backstop 1; = ablation.order.batch60sp.holds; "
    "4,530 - 3,612); " + IDN + "; " + L60)
note("layer1.decided-raw", T % 4 + "checked: this is 60s' (58''' was 1,678), not stale; " + IDN + "; ")

# ---------------------------------------------------------------- 5 rounds
N5 = T % 5 + ("re-read against the solve of record's progress.jsonl (worktrees/era5c-r215-kindorder/progress.jsonl"
              ": 20 program events, all status complete with return code 0; each event's cache key = the entry these "
              "values were read from, 20 / 20; r150/rounds-check.out); value unchanged; ")
for k in rows:
    if k.startswith("analysis.rounds.") or k.startswith("analysis.guarded."):
        note(k, N5)
new("analysis.rounds.per-program", "analysis.rounds.cap-reached", "0", "count", "n/a",
    T % 5 + "programs whose verification loop reached a cap in the solve of record (era5c-r215-kindorder, the 60-KINDORDER "
    "cache; progress.jsonl 20 / 20 complete): 0 -- the most rounds any verification took is 15 (bzip2, "
    "analysis.rounds.max) against that program's mode-A cap K+8 = 6,507, planner cap 10K+1 = 64,991 and loop cap "
    "10K+2 = 64,992; the smallest cap anywhere is bst's mode-A 52 (bst took 1); guarded fallbacks 0 "
    "(analysis.guarded.fallbacks); every receipt repair = guarded; r146/census/cache/reader/60sp/records.tsv columns "
    "max_run_rounds_vs_caps, loop_cap_10K+2; " + L60)

# ---------------------------------------------------------------- 6 tests
N6 = T % 6 + ("NOT 60s': this key is the 54' whole harness's (16 programs with any test); the six shipped suites at "
              "60s' are rq1.tests.suites.programs 6 / rq1.tests.suites.passed 6 (main 225, the per-program "
              "rq1.tests.<p>.pass rows); the sentence at evaluation.tex:387 ('the test suites that N of the programs ship "
              "(libtree, rgba, quadtree, urlparser, genann, buffer)') should print rq1.tests.suites.programs; ")
for k in ("rq1.tests.programs", "rq1.tests.passed", "rq1.tests.total"):
    note(k, N6)

# ---------------------------------------------------------------- 7: the paper's own undefined keys (66b586d)
import csv as _csv, collections as _col
from decimal import Decimal as _D
_tr = _col.defaultdict(lambda: _col.defaultdict(_D))
_trials = _col.defaultdict(list)
for _r in _csv.DictReader(open(R + "/rq3-trials-021.tsv"), delimiter="\t"):
    if _r["exit"] != "0":
        die("021 trial exit")
    _tr[_r["program"]][_r["trial"]] += _D(_r["wall_s"])
for _p, _ts in _tr.items():
    _k = "example" if _p == "running-example" else _p
    _v = min(_ts.values())
    _all = ", ".join("t%s %s" % (t, _ts[t]) for t in sorted(_ts))
    new("rq3.inator.%s.emit-s" % _k, "rq3.inator.%s.total-s" % _k, "%.2f" % _v, "seconds", "n/a",
        "analysis-fanout 123 (relay 150; the key Table tab:scale-inator prints at the paper's 66b586d, undefined until "
        "now): our time on the program, rq3-inator report 021's own definition -- per trial the sum of its three "
        "stages (substrate: crat --pass expand,extern,preprocess; solve: S1 e5c_inner_solve_named_source, compile + "
        "slots / origins + solve + entry preparation; emit: the census child, rewrite + verify rounds + custody), "
        "GNU time walls; the value = the MIN of the per-trial totals (not the sum of the stage minima): five trials "
        "%s; = 021's table's bold total; from agents/artifacts/2026-10-14-rq3-inator-021/rq3-trials.tsv (host-b, the "
        "landed 32d966b9f, idle, 05:24-05:44Z 10-14)" % _all)

# ---------------------------------------------------------------- assemble
final = []
for i, l in enumerate(out):
    final.append(l)
    m = ROW.match(l)
    if m:
        k0 = [k for k, j in rows.items() if j == i]
        if k0 and k0[0] in inserts:
            final.extend(inserts[k0[0]])
text = "\n".join(final)
keys = [ROW.match(l).group("key") for l in final if ROW.match(l) and not l.startswith("| key |")]
if len(keys) != len(set(keys)):
    die("duplicate keys after")
open(R + "/record-123.md", "w", encoding="utf-8", newline="").write(text)
open(R + "/log-123.tsv", "w").write("key\taction\tbefore\tafter\n" + "".join("\t".join(x) + "\n" for x in log))
print("in md5", hashlib.md5(raw).hexdigest(), "out md5", hashlib.md5(text.encode()).hexdigest(),
      "new", sum(1 for x in log if x[1] == "new"), "renamed", sum(1 for x in log if x[1].startswith("renamed")),
      "notes", sum(1 for x in log if x[1] == "note"), "rq4 six/set/config/census/twenty",
      sum(1 for v in cls.values() if v is SIX), sum(1 for v in cls.values() if v is SET),
      sum(1 for v in cls.values() if v is CONFIG), sum(1 for v in cls.values() if v is CENSUS),
      sum(1 for v in cls.values() if v is TWENTY), "rq4 rows", len(cls))
