#!/usr/bin/env python3
"""apply_58ppp.py -- analysis-fanout 117 (relay 141, R975-1: S39 adopted): write the 58''' re-seed into a COPY of the
record in ONE pass.

Input : r141/record-current.md (= docs origin/main:paper/numbers-of-record.md, checked byte for byte)
        r141/{census,trees,rq5,conf,waivers,proof}/staged.tsv (key, value_now, value_58ppp, verdict, cause)
        r141/apply/new-keys.tsv (the validator keys, inserted after ec4.cover.viol)
Output: r141/apply/record-58ppp.md, record.diff, moved.tsv, apply-log.tsv

Row rules:
  equal / differs  value_58ppp written; provenance = the 58''' header + cause + "; previously at 58'': <old provenance>"
                   (proof rows: no frame header; their cause carries the frozen print's own header)
  carried          value unchanged; provenance prefixed "58''': carried (input identical: <cause>; ...)"
  not-at-58ppp     row untouched
Verifier corrections (cause text only; no value moves) are applied from TEXT_FIXES, each pinned to an exact count.
Every check fails closed through raise SystemExit (no assert)."""
import csv, difflib, hashlib, os, re, subprocess, sys

R = "scratch/analysis-fanout/r141"
APPLY = R + "/apply"
IN_RECORD = R + "/record-current.md"
OUT_RECORD, OUT_DIFF, OUT_MOVED, OUT_LOG = (APPLY + "/" + n for n in ("record-58ppp.md", "record.diff", "moved.tsv", "apply-log.tsv"))
NEW_KEYS = APPLY + "/new-keys.tsv"
CRAT, DOCS = "crat", "crat/docs"
GROUPS = ["census", "trees", "rq5", "conf", "waivers", "proof"]
VERDICTS = {"equal", "differs", "carried", "not-at-58ppp"}
EXPECTED_HEAD = "a87e3c6f3"      # 3eaf5228d + era-5c's frame files (assembler 146a), no code change
LANDED_CODE = "3eaf5228d"


def die(m):
    raise SystemExit("apply_58ppp: FAIL: " + m)


def need(c, m):
    if not c:
        die(m)


def git(*a):
    r = subprocess.run(["git"] + list(a), capture_output=True)
    need(r.returncode == 0, "git %s: %s" % (" ".join(a), r.stderr.decode(errors="replace")))
    return r.stdout


def md5(b):
    return hashlib.md5(b).hexdigest()


def pct(n, d, p):
    return ("%." + str(p) + "f") % (100.0 * n / d)


DELIVERED, LEDGER, UNIVERSE = 2678, 2682, 4301
HOLDS = {"pending": 248, "ref-beside": 263, "retained-access": 403, "backstop": 1}
WITHHELD = sum(HOLDS.values())
need(WITHHELD == 915, "holds")
DENOM = UNIVERSE - WITHHELD
need(DENOM == 3386, "denominator")
RATE, OLD = pct(DELIVERED, DENOM, 2), pct(DELIVERED, UNIVERSE, 2)
need((RATE, OLD) == ("79.09", "62.26"), "rates %s %s" % (RATE, OLD))
HEADLINE_KEYS = {
    "rq1.frame-delivered": str(DELIVERED),
    "rq1.frame14u.delivered": str(DELIVERED),
    "rq1.frame-safe-decisions": str(DENOM),
    "rq1.frame-safe-decisions.amended": str(DENOM),
    "rq1.frame14u.safe-decisions": str(DENOM),
    "rq1.frame-realization-rate": pct(DELIVERED, DENOM, 1) + "%",
    "rq1.frame-realization-rate.amended": pct(DELIVERED, DENOM, 1) + "%",
    "rq1.frame14u.realization-rate": RATE + "%",
    "rq1.frame-realization-rate.old-definition": pct(DELIVERED, UNIVERSE, 1) + "%",
}


def header(head):
    return (
        "58''' (landed 2026-10-11 13:14:18Z (the push; assembler 146 and the landing record), R975-1 (USER: S39 adopted; seat addendum 975), relay 141; borrow-ownership "
        "cf9719575 -> 3eaf5228d (assembler 146, relay 189: 58'' + era-5c's five S39 picks; analyses tree 2c6824c70) and "
        "era-5c's frame files a87e3c6f3 on top (assembler 146a, pushed 14:41:27Z: crates/pointer_replacer/frames/l01p14u-s39-env.sh and "
        "-frame.md, no code change; origin/borrow-ownership after git fetch at the apply = %s)): census main/batch58pps39 "
        "(main 219: code 3eaf5228d run cache-only on era-5c's S39 cache worktrees/era5c-r211-s39pp (20 entries, ten "
        "solved on host-a and ten (A2) on host-b; manifest batch58pps39-manifest.tsv = l01p14u-s39-manifest.tsv row for row; "
        "the listing unchanged across the run; frame check: analysis 746aad53, configuration beff8254, launch 09eec6ff); "
        "CRAT_COPY_RELAX=depth0-borrow-to-raw, CRAT_MERGE_LIVENESS=on, CRAT_P11_SCOPE unset = integers-only (R959-1); "
        "status=complete-with-typed-failure data=false delivery=degraded, 20/20 emitted, 0 worker aborts; the one typed "
        "failure is tulipindicators' delivery custody: 4 ledger-only rows (fuzzer::main_0::{argv#2, info_0#20}, "
        "smoke::test_ind_name::{info#4, s#49}) that the ledger counts delivered and the emitted tree keeps raw (they sit in "
        "ti_find_indicator's two callers, whose callee the compile check reverts); every delivered count is BY THE EMITTED "
        "TREE: %s (the ledger %s); %s / %s = %s %% under R956-1 with D6 (%d first-order-held subjects out of the "
        "denominator, each counted once: pending %d, ref-beside %d, retained-access %d, backstop %d; the into-held-formal "
        "cascade 142 stays in; D6 adds 0), the old definition (R709-1 as worded) %s / %s = %s %% (main 219 prints 62.27 %%, "
        "a rounding slip of 62.2646 %%); by identity by the tree +51 / -22 against 58'', +67 / -22 against 58)"
        % (head, "{:,}".format(DELIVERED), "{:,}".format(LEDGER), "{:,}".format(DELIVERED), "{:,}".format(DENOM), RATE,
           WITHHELD, HOLDS["pending"], HOLDS["ref-beside"], HOLDS["retained-access"], HOLDS["backstop"],
           "{:,}".format(DELIVERED), "{:,}".format(UNIVERSE), OLD))


FANOUT = "analysis-fanout 117 (relay 141)"

# verifier corrections of cause text: (group, old, new, expected number of rows touched or None = at least one)
TEXT_FIXES = [
    ("trees", "brotli's owning-typed declarations 85 -> 95 (ClusterBlocksDistance's Box owners)",
     "brotli's owning-typed declarations 85 -> 95 (+14 / -4: ClusterBlocksDistance 12 Box locals and "
     "InitBlockSplitterCommand::{new_array, new_array_0} gained; InitBlockSplitterDistance and InitContextBlockSplitter "
     "lose their two each)", 1),
    ("trees", "recomputed at 58''' = no Laertes output in the artifact (CROWN's Table 2: †) over the programs with a "
     "Laertes tree; the record value is R891-1's",
     "recomputed at 58''' = no Laertes tree for brotli (CROWN's Table 2: †); the record's 0.0% is R891-1's", 2),
    ("trees", ", ZopfliCreateCommands::num_literals,", ", BrotliZopfliCreateCommands::num_literals,", None),
    ("trees", ", ZopfliCreateCommands -2,", ", BrotliZopfliCreateCommands -2,", None),
    ("rq5", "base = 58'''s row file of record", "base = the 58'' row file of record", 10),
    ("rq5", "1,568 rows keep 58'''s row-level cause", "1,568 rows keep their 58'' row-level cause", 10),
    ("rq5", " where another subject entered the decided-safe set at 58''': the pair swaps of main 219 §3)",
     " where another subject entered the decided-safe set at 58''': same-function swaps, a population other than "
     "main 219 section 3's six delivered pair swaps)", 10),
    ("waivers", "per-program/detail at 58''': brotli 38, buffer 7, heman 5, quadtree 3;",
     "per-program/detail at 58''': buffer 7, heman 5, quadtree 2 (the verifier's split; brotli 38 and quadtree 1 are option-box);", 1),
    ("waivers", "per-program/detail at 58''': buffer 30, brotli 16, quadtree 4, heman 2;",
     "per-program/detail at 58''': buffer 30, quadtree 4, heman 2 (the verifier's split; brotli 16 is option-box);", 1),
    ("waivers", "(the 58''' bridge receipts carry only callee-bound / callee-bound:may:size labels, 40 rows)",
     "(the 58''' receipts carry only callee-bound / callee-bound:may:size labels: 8 bridge-receipt rows, all "
     "tulipindicators; 24 rows across the bridge, mechanical-obligation and slice-construction receipts; no R677-6 or "
     "must label)", 1),
    ("waivers", "per-program/detail at 58''': rows 474, 9 programs: brotli 277, libzahl 126, lodepng 38, json.h 18, bzip2 5, "
     "heman 4, binn 2, libtree 2, quadtree 2;",
     "per-program/detail at 58''': the 325 clear rows: brotli 207, libzahl 86, json.h 18, lodepng 8, heman 2, libtree 2, "
     "quadtree 2 (of 474 pair-table rows in 9 programs);", 1),
    ("waivers", "previously at 54': 358 (the record s 374 is frame 13 s)",
     "the record's 374 is frame 13's; previously at 54': 358", 1),
    ("waivers", "control 54' (main/b54p) = 20001; 58'' (main/batch58pp) = 15856; previously at 54': 20001",
     "control 54' (main/b54p) = 20001; 58'' (main/batch58pp) = 15856; the 54' value reproduces only under 054's line "
     "reader, which counts 3 brotli continuation lines and loses 2 sites' terminal rows (rejoined 19,998); the 58'' and "
     "58''' values have no split cell and are exact; previously at 54': 20001", 1),
    ("waivers", "control 54' (main/b54p) = 17512; 58'' (main/batch58pp) = 14301; previously at 54': 17512",
     "control 54' (main/b54p) = 17512; 58'' (main/batch58pp) = 14301; the 54' value reproduces only under 054's line "
     "reader (rejoined 17,509); 58'' and 58''' exact; previously at 54': 17512", 1),
    ("waivers", "control 54' (main/b54p) = 19019; 58'' (main/batch58pp) = 14835; previously at 54': 19019",
     "control 54' (main/b54p) = 19019; 58'' (main/batch58pp) = 14835; the 54' value reproduces only under 054's line "
     "reader (rejoined 19,021); 58'' and 58''' exact; previously at 54': 19019", 1),
    ("waivers", "{'terminal-not-applied:dropped-site:a5-site-proof-reclassified:seam-positive-retention;dropped-site': 3}",
     "3 rows, exclusion terminal-not-applied:dropped-site:a5-site-proof-reclassified:seam-positive-retention;dropped-site:seam-positive-retention:seam-positive-retention (the full string of main/batch58pps39 subject-outcomes)", 1),
]
# value corrections: (group, key, staged value, written value, cause old, cause new)
VALUE_FIXES = [
    ("waivers", "codegen.rewrite.slice-construction.sites", "202", "203",
     "control 54' (main/b54p) = 235; 58'' (main/batch58pp) = 205; previously at 54': 235",
     "CORRECTED by the verifier (r141/waivers/verify-independent): 054's line reader drops the terminal row of one "
     "brotli obligation (class 2805, slice-local-construction) whose length-expression cell spans two physical lines; "
     "rejoined, 203 at 58''' (206 at 58''); control 54' (main/b54p) = 235 under 054's reader (236 rejoined); "
     "previously at 54': 235"),
]
# verdict label fixes (group, key, staged verdict, written verdict)
VERDICT_FIXES = [("census", "premise.bridge-dereferenceable.call-view", "equal", "carried")]


def owner_of(key):
    if key.startswith("rq5."):
        return "rq5"
    if key in ("rq2.wins.decl", "rq2.ties.decl"):
        return "trees"
    return None


ROW_RE = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) "
                    r"\| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")


def render(c):
    return "| %s | %s | %s | %s | %s | %s |" % (c["key"], c["value"], c["status"], c["layer"], c["unit"], c["prov"])


def main():
    git("-C", CRAT, "fetch", "-q", "origin", "borrow-ownership")
    head = git("-C", CRAT, "log", "-1", "--format=%h", "origin/borrow-ownership").decode().strip()
    need(head == EXPECTED_HEAD, "origin/borrow-ownership is %s" % head)
    need(git("-C", CRAT, "rev-parse", EXPECTED_HEAD + "^").decode().strip().startswith(LANDED_CODE), "a87e3c6f3^ != 3eaf5228d")
    need(git("-C", CRAT, "rev-parse", EXPECTED_HEAD + ":crates/pointer_replacer/src").strip()
         == git("-C", CRAT, "rev-parse", LANDED_CODE + ":crates/pointer_replacer/src").strip(), "src moved after 3eaf5228d")

    raw = open(IN_RECORD, "rb").read()
    need(raw == git("-C", DOCS, "show", "origin/main:paper/numbers-of-record.md"), "record-current.md is not docs origin/main's")
    lines = raw.decode("utf-8").split("\n")
    index = {}
    for i, l in enumerate(lines):
        m = ROW_RE.match(l)
        if m and m.group("key") and not l.startswith("| key |") and not l.startswith("|---"):
            need(m.group("key") not in index, "duplicate record key " + m.group("key"))
            index[m.group("key")] = i

    csv.field_size_limit(10 ** 9)
    staged = {}
    fix_hits = [0] * len(TEXT_FIXES)
    value_hits = []
    for g in GROUPS:
        with open("%s/%s/staged.tsv" % (R, g), encoding="utf-8", newline="") as f:
            rd = csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
            need(rd.fieldnames == ["key", "value_now", "value_58ppp", "verdict", "cause"], g + ": header")
            for r in rd:
                need(r["verdict"] in VERDICTS, "%s %s verdict %r" % (g, r["key"], r["verdict"]))
                for j, (fg, old, new, _) in enumerate(TEXT_FIXES):
                    if fg == g and old in r["cause"]:
                        r["cause"] = r["cause"].replace(old, new)
                        fix_hits[j] += 1
                for fg, fk, was, now, cold, cnew in VALUE_FIXES:
                    if fg == g and fk == r["key"]:
                        need(r["value_58ppp"] == was and cold in r["cause"], "value fix %s: staged %s" % (fk, r["value_58ppp"]))
                        r["value_58ppp"] = now
                        r["cause"] = r["cause"].replace(cold, cnew)
                        value_hits.append(fk)
                for fg, fk, was, now in VERDICT_FIXES:
                    if fg == g and fk == r["key"]:
                        need(r["verdict"] == was, "verdict fix %s: staged %s" % (fk, r["verdict"]))
                        r["verdict"] = now
                staged.setdefault(r["key"], []).append((g, r))
    need(sorted(value_hits) == sorted(f[1] for f in VALUE_FIXES), "value fixes applied %s" % value_hits)
    for j, (g, old, new, n) in enumerate(TEXT_FIXES):
        need(fix_hits[j] > 0 and (n is None or fix_hits[j] == n), "text fix %d hit %d rows" % (j, fix_hits[j]))

    rows = {}
    for k, lst in staged.items():
        if len(lst) == 1:
            rows[k] = (lst[0][0], lst[0][1], [])
            continue
        own = owner_of(k)
        need(own is not None, "duplicate staged key without an owner: " + k)
        vals = {(r["value_now"], r["value_58ppp"]) for _, r in lst}
        need(len(vals) == 1, "duplicate disagrees: %s %s" % (k, vals))
        mine = [(g, r) for g, r in lst if g == own]
        need(len(mine) == 1, "owner does not stage " + k)
        rows[k] = (own, mine[0][1], sorted(g for g, _ in lst if g != own))

    for k, want in HEADLINE_KEYS.items():
        need(k in rows and rows[k][1]["value_58ppp"] == want, "headline %s staged %r want %r"
             % (k, rows.get(k, (0, {}))[1].get("value_58ppp"), want))

    hdr = header(head)
    need("|" not in hdr, "pipe in header")
    out = list(lines)
    moved, log, counts = [], [], {}
    for k in sorted(rows):
        g, r, also = rows[k]
        need(k in index, "staged key not in the record: " + k)
        li = index[k]
        cells = ROW_RE.match(lines[li]).groupdict()
        need(render(cells) == lines[li], "row does not round-trip: " + k)
        need(cells["value"] == r["value_now"], "%s: record %r != staged value_now %r" % (k, cells["value"], r["value_now"]))
        verdict, new, cause = r["verdict"], r["value_58ppp"], r["cause"].strip()
        need("|" not in cause and "\t" not in cause and "\n" not in cause, k + ": bad cause")
        need("|" not in new and "\t" not in new, k + ": bad value")
        if verdict in ("equal", "carried"):
            need(new == cells["value"], "%s: %s but values differ" % (k, verdict))
        if verdict == "differs":
            need(new != cells["value"] and new not in ("", "-"), "%s: differs but %r" % (k, new))
        cross = (" (cross-check: r141/%s stages the same value)" % "/".join(also)) if also else ""
        old = cells["prov"]
        if verdict == "not-at-58ppp":
            action = "untouched"
        elif verdict == "carried":
            cells["prov"] = ("58''': carried (input identical: %s; 58''' landed 2026-10-11 13:14:18Z, R975-1, relay 141; "
                             "borrow-ownership %s; census main/batch58pps39 (main 219); %s, r141/%s%s); %s"
                             % (cause, head, FANOUT, g, cross, old))
            action = "carried"
        else:
            if g == "proof":
                cells["prov"] = "%s; previously: %s" % (cause, old)
            else:
                before = ("frame 13" if k == "rq4.pair.sites" else "54'") if g == "waivers" else "58''"
                cells["prov"] = "%s; %s: r141/%s%s: %s; previously at %s: %s" % (hdr, FANOUT, g, cross, cause, before, old)
            cells["value"] = new
            action = "reseeded"
            if new != r["value_now"]:
                moved.append((k, r["value_now"], new, g))
        need(cells["prov"].count("|") == old.count("|"), k + ": pipe added")
        out[li] = render(cells)
        m2 = ROW_RE.match(out[li])
        need(m2 is not None and m2.group("key") == k and m2.group("value") == cells["value"], k + ": rewritten row")
        counts[(g, verdict, action)] = counts.get((g, verdict, action), 0) + 1
        log.append((k, g, verdict, r["value_now"], cells["value"], action))

    changed = [i for i in range(len(lines)) if lines[i] != out[i]]
    need(set(changed) <= {index[k] for k in rows}, "a non-staged line changed")
    need(len(out) == len(lines), "line count moved before inserts")

    # the validator keys (new rows, pending), inserted after ec4.cover.viol
    with open(NEW_KEYS, encoding="utf-8", newline="") as f:
        rd = csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
        need(rd.fieldnames == ["key", "value", "layer", "unit", "cause"], "new-keys header")
        newrows = list(rd)
    need("ec4.cover.viol" in index, "anchor")
    ins = []
    for r in newrows:
        need(r["key"] not in index, "new key already in record: " + r["key"])
        need("|" not in r["cause"] and "\t" not in r["cause"] and r["value"] != "", "new key " + r["key"])
        if r["key"].endswith(".at-58pp"):
            prov = "%s: r141/apply/new-keys.tsv: %s" % (FANOUT, r["cause"])
        else:
            prov = "%s; %s: r141/apply/new-keys.tsv: %s" % (hdr, FANOUT, r["cause"])
        ins.append(render({"key": r["key"], "value": r["value"], "status": "pending", "layer": r["layer"],
                           "unit": r["unit"], "prov": prov}))
        moved.append((r["key"], "(new)", r["value"], "conf"))
    a = index["ec4.cover.viol"] + 1
    out = out[:a] + ins + out[a:]
    text = "\n".join(out)
    with open(OUT_RECORD, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    with open(OUT_DIFF, "w", encoding="utf-8") as f:
        f.write("\n".join(difflib.unified_diff(lines, out, "record (docs origin/main)", "record-58ppp.md", lineterm="", n=0)) + "\n")
    with open(OUT_MOVED, "w", encoding="utf-8") as f:
        f.write("key\tbefore\t58'''\tgroup\n" + "".join("\t".join(x) + "\n" for x in sorted(moved)))
    with open(OUT_LOG, "w", encoding="utf-8") as f:
        f.write("key\tgroup\tverdict\tbefore\tafter\taction\n" + "".join("\t".join(x) + "\n" for x in log))
    print("head", head)
    print("record in md5", md5(raw), "out md5", md5(text.encode()), "rows rewritten", len(changed), "inserted", len(ins),
          "values moved", len(moved) - len(ins))
    for (g, v, a_), n in sorted(counts.items()):
        print("  %-8s %-13s %-10s %d" % (g, v, a_, n))


if __name__ == "__main__":
    main()
