#!/usr/bin/env python3
# r095 rq4 verifier: builds stage.verified.json from raw run files (not from the computing agent's outputs).
# usage: nice -n 10 python3 verify_build.py <numbers-of-record.md from docs origin/main>
import json, re, sys, os
NOR = sys.argv[1]
F = "scratch/main/frame14"
W = "scratch/wave-6o/six-f14"
S = "scratch/wave-6o/six54"
E = "scratch/wave-6o/e4"
A129 = "docs/agents/artifacts/2026-10-06-wave-6o-129"
SIX = ["libtree", "rgba", "quadtree", "urlparser", "genann", "buffer"]

nor = {}
for l in open(NOR, encoding="utf-8"):
    if l.startswith("| ") and l.count("|") >= 7:
        c = [x.strip() for x in l.strip().strip("|").split("|")]
        nor[c[0]] = c

def tsv_rows(path):
    rows = []
    for l in open(path):
        if l.startswith("#") or l.startswith("input\t"): continue
        rows.append(l.rstrip("\n").split("\t"))
    return rows

# ---- per run: (input status, output status) on pass D, read from the raw files ----
def miri_first(path):  # miri-runs-*.tsv: one row per input -> first_report
    return {r[0]: r[1] for r in tsv_rows(path)}

runs = {}
for p in ["rgba", "quadtree", "urlparser", "genann", "buffer"]:
    out = miri_first(f"{W}/D/{p}/miri-runs-emitted-TB.tsv")
    ind = {"urlparser": "D5", "genann": "D8"}.get(p, "D")
    inp = miri_first(f"{S}/{ind}/{p}/miri-runs-substrate-TB.tsv")
    inA = miri_first(f"{S}/{'A8' if p == 'genann' else 'A'}/{p}/miri-runs-substrate-TB.tsv")
    runs[p] = [(k, inA[k], inp[k], out[k]) for k in out]
lA = {r[0]: r[3] for r in tsv_rows(f"{S}/libtree-A-substrate.tsv")}
lD = {r[0]: r[3] for r in tsv_rows(f"{S}/libtree-D-substrate.tsv")}
oD = {r[0]: r[3] for r in tsv_rows(f"{W}/libtree-D-emitted.tsv")}
runs["libtree"] = [(k, "ub" if lA[k] != "-" else "pass", "pass" if lD[k] == "-" else "ub", "pass" if oD[k] == "-" else "ub") for k in oD]

# repair classes applied per program (repairs-f14.tsv; the input side ran 54' repairs.tsv, same input rows)
cls = {}
for l in open("docs/agents/tools/runtime/miri/repairs-f14.tsv"):
    if l.startswith("#") or not l.strip(): continue
    f = l.split("\t"); cls.setdefault(f[0], set()).add(f[1])

def classify(p, inA, inD, outD):
    # the manuscript's definitions (paper origin/main sections/evaluation.tex, RQ4) = the key texts of 056:
    if inD == "pass" and outD == "pass":
        if inA == "pass": return "both-clean"
        # input stopped on its own; clean only with the declared edit on both programs
        if cls.get(p, set()) <= {"reference", "uninitialised"}: return "input-repaired"
        return "both-clean?"  # C-defect repair then clean: not met in the six
    if outD == "fabricated-extent": return "length-waiver"
    if inD != "pass" and outD != "pass": return "blocked"   # the input's own C defect stops both; not repairable to clean
    if inD == "pass" and outD != "pass": return "ours"
    return "?"

cols = ["runs", "both-clean", "input-repaired", "length-waiver", "ours", "blocked"]
T = {}
for p in SIX:
    c = {k: 0 for k in cols}
    for (_, a, d, o) in runs[p]:
        c["runs"] += 1; c[classify(p, a, d, o)] += 1
    T[p] = c
T["total"] = {k: sum(T[p][k] for p in SIX) for k in cols}
for p in SIX + ["total"]: print(p, [T[p][k] for k in cols], file=sys.stderr)

# CROWN column (frame-independent; 129a/129b/120b/112a): runs, runs with a Miri report
def first_any(path):
    return [r[1] for r in tsv_rows(path)]
crown = {}
crown["libtree"] = [("pass" if r[3] == "-" else "ub") for r in tsv_rows(f"{A129}/crown-libtree-D.tsv")]
cu = open(f"{A129}/crown-urlparser-D.tsv").read().split("# workD-c2rust")[0]
crown["urlparser"] = [l.split("\t")[1] for l in cu.splitlines() if l.startswith("test\t")]
crown["genann"] = ["pass" if " pass=1 " in open(f"{A129}/receipts-D-genann-crown.txt").read() else "ub"]
crown["rgba"] = first_any(f"{E}/work-six-crown/rgba/miri-runs-emitted-TB.tsv")
crown["quadtree"] = first_any(f"{E}/work-crown/quadtree/miri-runs-emitted-TB.tsv")
crown["buffer"] = first_any(f"{E}/work-crown/buffer/miri-runs-emitted-TB.tsv")
for p in SIX: print("crown", p, len(crown[p]), sum(1 for x in crown[p] if x != "pass"), file=sys.stderr)

def thiskey(k):
    prov = nor[k][5]
    m = re.search(r"(R817-1, USER 2026-10-05\): .*)$", prov)
    return m.group(1) if m else ""

head = ("at the frame of record L01^14 (landed <DATE>): wave-6o report 130 (R851-2 ACCEPTED), the six programs' shipped suites under Miri "
        "(Tree Borrows), pass D: the declared repairs on both programs, the oracle extents on the output; frame census " + F +
        " (code 4a47f16f7, analysis frame era5c-l01p14-v1; aggregate.kv raw_boundary_code_frame=4a47f16f7fa46c0bf9f0d0adcdb382a0dc2a734c "
        "raw_boundary_analysis_frame=era5c-l01p14-v1; every receipt line frame=era5c-l01p14-v1). ")
rule = ("Columns as the manuscript defines them (paper sections/evaluation.tex, RQ4) and as 056 keyed them; one run = one test of the suite "
        "(libtree's nine make-check tests, one test binary each for the other five); each run in exactly one column: clean = neither program "
        "reports a finding; input repaired = the input stops at a finding that is not a defect of the C program (the declared reference / "
        "uninitialised rows) and the same edit on both programs makes the run clean; length waiver = the output stops at a slice of the waived "
        "length (section 77; on pass D the oracle-extent overlap of 130); ours = the output stops at a finding the input does not have; blocked = "
        "Miri cannot run the test to its end for another reason (here the input's own C defect, the same site on both sides). ")
evid = {
 "libtree": "libtree: input pass A stops at its own small_vec_u64_append:758 in all 9 (c2rust references; " + S + "/libtree-A-substrate.tsv); with the four reference rows input pass D 9 / 9 make 0 no report (" + S + "/libtree-D-substrate.tsv) and output pass D 9 / 9 make 0 no report (" + W + "/libtree-D-emitted.tsv; the four rows in libtree-D-emitted/proj/harness-edits.txt): 9 input repaired. ",
 "rgba": "rgba: input passes A and D clean (" + S + "/A and D/rgba/miri-runs-substrate-TB.tsv), output pass D pass (" + W + "/D/rgba/miri-runs-emitted-TB.tsv), no repair row: 1 clean. ",
 "quadtree": "quadtree: input passes A and D clean, output pass D pass, no repair row: 1 clean. ",
 "buffer": "buffer: input passes A and D clean, output pass D pass, no repair row: 1 clean. ",
 "urlparser": "urlparser: input pass D stops at its own fifth class (strdup reads past an 11-byte allocation after strff, a C defect, wave-6o 127; " + S + "/D5/urlparser/miri-runs-substrate-TB.tsv) and output pass D at the same class (" + W + "/D/urlparser/miri-runs-emitted-TB.tsv, strdup:719): 1 blocked. ",
 "genann": "genann: input pass D runs test.c to its end, 9 / 9 (127a; " + S + "/D8/genann, 7,126 s; the one input-defect row is the test's own double fclose, a C defect); output pass D stops at section 77 oracle-extent-overlap genann_run:899 (" + W + "/D/genann/miri-runs-emitted-TB.tsv): 1 length waiver. ",
}
cmds = ("Commands: OUTPUT (130's rq4-f14-run.sh) nice -n 10 python3 docs/agents/tools/runtime/miri_census.py " + F + " " + W +
        "/D --programs rgba,quadtree,urlparser,buffer --discipline TB --variant emitted --timeout 3600 --native scratch/main/runtime-frame13 --oracle --repair docs/agents/tools/runtime/miri/repairs-f14.tsv, "
        "the same with --programs genann --inputs test --timeout 28800, and CRAT_MIRI_REPAIRS=docs/agents/tools/runtime/miri/repairs-f14.tsv nice -n 10 python3 " + S + "/libtree_suite.py " + F + " " + W + " D emitted. "
        "INPUT carried over from 54' (the six substrates unchanged since 2026-08-06; the R814 switch touched brotli and lodepng only, 129c), run under 54' table repairs.tsv (its input rows = repairs-f14.tsv's): "
        + S + "/run.sh step D substrate --repair repairs.tsv (rgba, quadtree, buffer), run-q9.sh (urlparser D5), run-q10.sh (genann D8, 8 h cap), run-q4.sh libtree_suite.py b54p D substrate. "
        "Recount: verify_build.py in r095/stage/rq4. ")
out = []
for p in SIX + ["total"]:
    for c in cols:
        k = f"rq4.suite.{p}.{c}"
        e = evid.get(p, "the six together = the sum of the six per-program rows (" + ", ".join(f"{q} {T[q][c]}" for q in SIX) + "). ")
        prov = head + rule + e + cmds + "Key definition (056): " + thiskey(k)
        out.append({"key": k, "value": str(T[p][c]), "layer": nor[k][3], "unit": nor[k][4], "provenance": prov, "was": nor[k][1],
                    "definition_source": "paper origin/main sections/evaluation.tex RQ4 (column definitions) + analysis-fanout 056 + numbers-of-record row"})
crown_src = {"libtree": A129 + "/crown-libtree-D.tsv (129b, pass D, 9 / 9 make 0)",
             "rgba": E + "/work-six-crown/rgba/miri-runs-emitted-TB.tsv (120b; no repair row, A = D)",
             "quadtree": E + "/work-crown/quadtree/miri-runs-emitted-TB.tsv (112a; CROWN's own Box::from_raw(NULL), NonNull at 0; no repair row)",
             "urlparser": A129 + "/crown-urlparser-D.tsv (129, pass D: the input's fifth class, strdup, the same as the c2rust input)",
             "genann": A129 + "/receipts-D-genann-crown.txt (129a, pass D, pass=1, 6,904 s, 9 / 9)",
             "buffer": E + "/work-crown/buffer/miri-runs-emitted-TB.tsv (112a / 120b; no repair row, A = D)"}
for p in SIX:
    for c, v in (("runs", len(crown[p])), ("ub", sum(1 for x in crown[p] if x != "pass"))):
        k = f"rq4.suite.crown.{p}.{c}"
        prov = ("at the frame of record L01^14 (landed <DATE>): wave-6o report 130 section 2 (R851-2 ACCEPTED: against CROWN, the same on four; quadtree CROWN's own; genann CROWN clean), "
                "CROWN's output does not depend on our frame (frame census " + F + ", code 4a47f16f7, era5c-l01p14-v1, named for the table it sits in); "
                "Miri Tree Borrows on the shipped suite, pass D (the declared repair rows, the same as ours); source " + crown_src[p] +
                ". ub counts runs with any Miri report, whoever owns it. Key definition (056): " + thiskey(k))
        out.append({"key": k, "value": str(v), "layer": nor[k][3], "unit": nor[k][4], "provenance": prov, "was": nor[k][1],
                    "definition_source": "wave-6o 130 section 2, 129a, 129b, 120b, 112a + analysis-fanout 056"})
common = head + "The run's facts: "
out.append({"key": "rq4.census", "value": "era5c-l01p14-v1 at 4a47f16f7 (frame 14)", "layer": nor["rq4.census"][3], "unit": nor["rq4.census"][4],
  "provenance": common + "every line of " + W + "/receipts-A.txt, receipts-C.txt, receipts-D.txt carries frame=era5c-l01p14-v1; the six emitted trees under " + F + "/emitted-trees (written 05:13Z, before 130's runs at 06:13Z; unchanged to the census end 07:23Z). Command: grep -oh 'frame=[^ ]*' " + W + "/receipts-?.txt then sort -u.",
  "was": nor["rq4.census"][1], "definition_source": "numbers-of-record rq4.census + receipts + aggregate.kv"})
out.append({"key": "rq4.discipline", "value": "Tree Borrows", "layer": nor["rq4.discipline"][3], "unit": nor["rq4.discipline"][4],
  "provenance": common + "every line of " + W + "/receipts-A.txt, receipts-C.txt, receipts-D.txt carries discipline=TB; miri_census.py line 317 adds -Zmiri-tree-borrows for TB (unchanged since 2026-10-05 13:47Z); libtree_suite.py sets -Zmiri-tree-borrows. Command: grep -oh 'discipline=[^ ]*' " + W + "/receipts-?.txt then sort -u.",
  "was": nor["rq4.discipline"][1], "definition_source": "numbers-of-record rq4.discipline + receipts"})
out.append({"key": "rq4.checker", "value": nor["rq4.checker"][1], "layer": nor["rq4.checker"][3], "unit": nor["rq4.checker"][4],
  "provenance": common + "cargo +nightly miri --version prints miri 0.1.0 (923c95cdf5 2026-09-16) and rustup run nightly rustc --version prints rustc 1.100.0-nightly (923c95cdf 2026-09-16); the nightly toolchain's miri binary is dated 2026-09-28 12:04Z and librustc_driver 2026-09-17, both before 130's runs (2026-10-06 06:13Z), so the runs used this checker (miri_census.py and libtree_suite.py call cargo +nightly miri).",
  "was": nor["rq4.checker"][1], "definition_source": "numbers-of-record rq4.checker"})
for o in out:
    assert "|" not in o["value"] and "|" not in o["provenance"] and "\n" not in o["provenance"], o["key"]
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "stage.verified.json"), "w"), indent=1, ensure_ascii=False)
print(len(out))
