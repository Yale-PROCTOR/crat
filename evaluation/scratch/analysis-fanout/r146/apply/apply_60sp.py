#!/usr/bin/env python3
"""apply_60sp.py -- analysis-fanout 120 (relay 146): the FINAL re-seed at 60s' (census main/batch60sp, main 225) into a
COPY of the record in ONE pass, plus the 52 new ablation.order.* keys (inserted after the last rq1.frame14u.* row).

usage: apply_60sp.py [<landed-at UTC> <assembler report>]   (no arguments = a DRY RUN: the head check is skipped)
Input : r146/record-current.md (= docs origin/main:paper/numbers-of-record.md, checked byte for byte)
        r146/{census,trees,rq5,conf,waivers}/staged.tsv (key, value_now, value_60sp, verdict, cause)
        r146/ablation/new-keys.tsv
Output: r146/apply/record-60sp.md, record.diff, moved.tsv, apply-log.tsv
Rows: equal / differs -> value_60sp, provenance = the 60s' header + cause + "; previously at 58''': <old provenance>";
carried -> value unchanged, "60s': carried (...)" prefix; not-at-60sp -> untouched.
Every check fails closed through raise SystemExit (no assert)."""
import csv, difflib, hashlib, re, subprocess, sys

DRY = len(sys.argv) < 3
LANDED_AT = "DRY-RUN" if DRY else sys.argv[1]
ASSEMBLER = "DRY-RUN" if DRY else sys.argv[2]
R = "scratch/analysis-fanout/r146"
APPLY = R + "/apply"
IN_RECORD = R + "/record-current.md"
OUT_RECORD, OUT_DIFF, OUT_MOVED, OUT_LOG = (APPLY + "/" + n for n in ("record-60sp.md", "record.diff", "moved.tsv", "apply-log.tsv"))
NEW_KEYS = R + "/ablation/new-keys.tsv"
CRAT, DOCS = "crat", "crat/docs"
GROUPS = ["census", "trees", "rq5", "conf", "waivers"]
VERDICTS = {"equal", "differs", "carried", "not-at-60sp"}
HEAD_OF_CENSUS = "32d966b9fc2ef56fcd40e95ee762f73b0e0be70a"
PREV = "58" + "'" * 3


def die(m):
    raise SystemExit("apply_60sp: FAIL: " + m)


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


DELIVERED, UNIVERSE = 2715, 4530
HOLDS = {"pending": 251, "ref-beside": 262, "retained-access": 404, "backstop": 1}
WITHHELD = sum(HOLDS.values())
need(WITHHELD == 918, "holds")
DENOM = UNIVERSE - WITHHELD
need(DENOM == 3612, "denominator")
RATE, OLD = pct(DELIVERED, DENOM, 2), pct(DELIVERED, UNIVERSE, 2)
need((RATE, OLD) == ("75.17", "59.93"), "rates %s %s" % (RATE, OLD))
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
        "60s' (the FINAL frame; landed %s, assembler %s, relay 146; borrow-ownership b3825fe91 -> 32d966b9f (60s 4eb66851b "
        "= batch 60 7682bb8a0 + era-5c's Ref > Owning > Raw switch; + wave-6a's replacement offer e3afd991e: every A9 reference "
        "lend withheld, box-param-lend-withheld; + era-5c's final-frame files 08281bcab); analyses a5495bf59; "
        "origin/borrow-ownership after git fetch at the apply = %s): census main/batch60sp (main 225: code 32d966b9f run "
        "cache-only on era-5c's 60-KINDORDER cache worktrees/era5c-r215-kindorder (20 entries; keycheck 20/20 analysis "
        "1d8dcd40, configuration d9a474da, launch 2e94d9a5; frame check REPRODUCED d9a474da); env of record "
        "frames/l01p14u-s39-mutlend-o-env.sh (= the solve's ablation-env.sh variable for variable; CRAT_ERA5C_KIND_ORDER="
        "ref-own-raw, CRAT_COPY_RELAX=depth0-borrow-to-raw, CRAT_MERGE_LIVENESS=on, CRAT_P11_SCOPE unset = integers-only); "
        "status=complete data=true, 20/20, diagnostics 0; counted by the emitted tree %s = the ledger (custody ledger-only 0, "
        "tree-only 0); %s / %s = %s %% under R956-1 with D6 (%d first-order-held subjects out of the denominator: pending %d, "
        "ref-beside %d, retained-access %d, backstop %d; D6 adds 0), the old definition (R709-1 as worded) %s / %s = %s %%; "
        "by identity +15 / -8 against batch 60 (7682bb8a0: 2,708 / 3,385 = 80.00 %%), +99 / -69 against 60s (4eb66851b: "
        "2,685 / 3,579 = 75.02 %%), +43 / -6 against %s)"
        % (LANDED_AT, ASSEMBLER, head, "{:,}".format(DELIVERED), "{:,}".format(DELIVERED), "{:,}".format(DENOM), RATE,
           WITHHELD, HOLDS["pending"], HOLDS["ref-beside"], HOLDS["retained-access"], HOLDS["backstop"],
           "{:,}".format(DELIVERED), "{:,}".format(UNIVERSE), OLD, PREV))


FANOUT = "analysis-fanout 120 (relay 146)"
TEXT_FIXES = [
    ("trees", "recomputed at 60s' = no Laertes output in the artifact (CROWN's Table 2: †) (the same at the " + PREV
     + " control) over the programs with a Laertes tree; the record value is R891-1's",
     "recomputed at 60s' = no Laertes tree for brotli (CROWN's Table 2: †), the same at the " + PREV
     + " control; the record's 0.0% is R891-1's", 2),
]
NEWKEY_TEXT_FIXES = [("kind_moves.py same-function pair re-breaks 16)",
                      "kind_moves.py same-function pair re-breaks: 16 pairs, 32 slots)", 2)]


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
    head = git("-C", CRAT, "rev-parse", "origin/borrow-ownership").decode().strip()
    if DRY:
        head = "DRY-RUN(" + head[:9] + ")"
    else:
        need(head == HEAD_OF_CENSUS, "origin/borrow-ownership is %s, not the head main censused" % head)
    head9 = head[:9] if not DRY else head

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
    for g in GROUPS:
        with open("%s/%s/staged.tsv" % (R, g), encoding="utf-8", newline="") as f:
            rd = csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
            need(rd.fieldnames == ["key", "value_now", "value_60sp", "verdict", "cause"], g + ": header")
            for r in rd:
                need(r["verdict"] in VERDICTS, "%s %s verdict %r" % (g, r["key"], r["verdict"]))
                for j, (fg, old, new, _) in enumerate(TEXT_FIXES):
                    if fg == g and old in r["cause"]:
                        r["cause"] = r["cause"].replace(old, new)
                        fix_hits[j] += 1
                staged.setdefault(r["key"], []).append((g, r))
    for j, (g, old, new, n) in enumerate(TEXT_FIXES):
        need(fix_hits[j] == n, "text fix %d hit %d rows" % (j, fix_hits[j]))

    rows = {}
    for k, lst in staged.items():
        if len(lst) == 1:
            rows[k] = (lst[0][0], lst[0][1], [])
            continue
        own = owner_of(k)
        need(own is not None, "duplicate staged key without an owner: " + k)
        vals = {(r["value_now"], r["value_60sp"]) for _, r in lst}
        need(len(vals) == 1, "duplicate disagrees: %s %s" % (k, vals))
        mine = [(g, r) for g, r in lst if g == own]
        need(len(mine) == 1, "owner does not stage " + k)
        rows[k] = (own, mine[0][1], sorted(g for g, _ in lst if g != own))
    need(not any(k.startswith("proof.") for k in rows), "a proof key is staged")

    for k, want in HEADLINE_KEYS.items():
        need(k in rows and rows[k][1]["value_60sp"] == want, "headline %s staged %r want %r"
             % (k, rows.get(k, (0, {}))[1].get("value_60sp"), want))

    hdr = header(head9)
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
        verdict, new, cause = r["verdict"], r["value_60sp"], r["cause"].strip()
        need("|" not in cause and "\t" not in cause and "\n" not in cause, k + ": bad cause")
        need("|" not in new and "\t" not in new, k + ": bad value")
        if verdict in ("equal", "carried"):
            need(new == cells["value"], "%s: %s but values differ" % (k, verdict))
        if verdict == "differs":
            need(new != cells["value"] and new not in ("", "-"), "%s: differs but %r" % (k, new))
        cross = (" (cross-check: r146/%s stages the same value)" % "/".join(also)) if also else ""
        old = cells["prov"]
        if verdict == "not-at-60sp":
            action = "untouched"
        elif verdict == "carried":
            cells["prov"] = ("60s': carried (input identical: %s; 60s' landed %s, assembler %s, relay 146; borrow-ownership %s; census "
                             "main/batch60sp (main 225); %s, r146/%s%s); %s" % (cause, LANDED_AT, ASSEMBLER, head9, FANOUT, g, cross, old))
            action = "carried"
        else:
            cells["prov"] = "%s; %s: r146/%s%s: %s; previously at %s: %s" % (hdr, FANOUT, g, cross, cause, PREV, old)
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

    with open(NEW_KEYS, encoding="utf-8", newline="") as f:
        rd = csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
        need(rd.fieldnames == ["key", "value", "layer", "unit", "cause"], "new-keys header")
        newrows = list(rd)
    anchors = [k for k in index if k.startswith("rq1.frame14u.")]
    need(anchors, "anchor")
    ins, nk_hits = [], {}
    for r in newrows:
        need(r["key"] not in index, "new key already in record: " + r["key"])
        need(r["key"].startswith("ablation.order."), "new key outside ablation.order.*: " + r["key"])
        for old_t, new_t, n in NEWKEY_TEXT_FIXES:
            if old_t in r["cause"]:
                r["cause"] = r["cause"].replace(old_t, new_t)
                nk_hits[old_t] = nk_hits.get(old_t, 0) + 1
        need("|" not in r["cause"] and "\t" not in r["cause"] and r["value"] != "", "new key " + r["key"])
        prov = ("%s; %s: r146/ablation/new-keys.tsv (the objective-order ablation; heads of record by hash: batch 60 7682bb8a0 "
                "= main 223, batch 60s 4eb66851b = main 224, 60s' 32d966b9f = main 225): %s" % (hdr, FANOUT, r["cause"]))
        ins.append(render({"key": r["key"], "value": r["value"], "status": "pending", "layer": r["layer"],
                           "unit": r["unit"], "prov": prov}))
        moved.append((r["key"], "(new)", r["value"], "ablation"))
    for old_t, new_t, n in NEWKEY_TEXT_FIXES:
        need(nk_hits.get(old_t, 0) == n, "new-key text fix hit %d" % nk_hits.get(old_t, 0))
    need(len(ins) == 52, "new keys %d" % len(ins))
    a = max(index[k] for k in anchors) + 1
    out = out[:a] + ins + out[a:]
    text = "\n".join(out)
    with open(OUT_RECORD, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    with open(OUT_DIFF, "w", encoding="utf-8") as f:
        f.write("\n".join(difflib.unified_diff(lines, out, "record (docs origin/main)", "record-60sp.md", lineterm="", n=0)) + "\n")
    with open(OUT_MOVED, "w", encoding="utf-8") as f:
        f.write("key\tbefore\t60s'\tgroup\n" + "".join("\t".join(x) + "\n" for x in sorted(moved)))
    with open(OUT_LOG, "w", encoding="utf-8") as f:
        f.write("key\tgroup\tverdict\tbefore\tafter\taction\n" + "".join("\t".join(x) + "\n" for x in log))
    print("head", head, "dry" if DRY else "")
    print("record in md5", md5(raw), "out md5", md5(text.encode()), "rows rewritten", len(changed), "inserted", len(ins),
          "values moved", len(moved) - len(ins))
    for (g, v, a_), n in sorted(counts.items()):
        print("  %-8s %-13s %-10s %d" % (g, v, a_, n))


if __name__ == "__main__":
    main()
