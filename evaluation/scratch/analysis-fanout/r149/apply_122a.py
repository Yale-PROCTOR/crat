#!/usr/bin/env python3
"""apply_122a.py -- analysis-fanout 122a (relay 149 A and C): R1091-1 (RQ5 out of the paper) and the seat's answers to
120 section 4, written into the record as provenance notes; the four ec4.validator.*.at-58pp rows dropped (C.11).
No value changes. Input = docs origin/main:paper/numbers-of-record.md; output r149/record-122a.md. Fails closed."""
import hashlib, re, subprocess

R = "scratch/analysis-fanout/r149"
DOCS = "crat/docs"
ROW = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) "
                 r"\| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")


def die(m):
    raise SystemExit("apply_122a: FAIL: " + m)


raw = subprocess.run(["git", "-C", DOCS, "show", "origin/main:paper/numbers-of-record.md"], capture_output=True,
                     check=True).stdout
lines = raw.decode("utf-8").split("\n")
S = "the seat, relay 149 C.%s (10-14): "
RQ5 = "not cited: RQ5 removed from the paper, R1091-1 (USER, 10-14); "
RQ3T = ("three at once on host-b (the 60-KINDORDER solve ran up to 3 programs at once), re-measured serially "
        "(era-5c 220; relay 149 B, R1091-2), until then not the times of record; ")
NOTES = [  # (key predicate, note, expected hits)
    (lambda k: k.startswith("rq5."), RQ5, 80),
    (lambda k: k == "analysis.copy-lend.owners-created",
     S % 1 + "as measured: an order move is not a lend-created owner (the producer's literal 229 are the Ref > Owning > "
     "Raw order's moves; b55 -> batch 60, copy-lend on and no order, moves 0); ", 1),
    (lambda k: k in ("waiver.leak-parity", "waiver.leak-parity-scope"),
     S % 2 + "as measured, 15 under relay 139's rule; main 225's 23 is the receipt sum (quadtree's 6 + 9 and heman's "
     "2 + 2 receipts name the same closes) -- say so where the key is read; ", 2),
    (lambda k: k == "ablation.order.overlap-hold.brotli-lost.at-60s",
     S % 5 + "the key governs: of brotli's 102 losses at 60s, 90 are function reverts (closure:partition) and 2 carry an "
     "overlap or pair label (HistogramAddHistogramCommand::v pair-raw-view, EncodeData::new_commands "
     "pair-proven-overlap); the paper's sentence is re-worded to the key (the seat tells the paper session); ", 1),
    (lambda k: k == "ablation.order.overlap-hold.brotli-lost",
     S % 5 + "the key governs: at 60s' against 60 brotli loses 6 (kind-raw 3, box-param-lend-withheld 2, "
     "held:into-held-formal 1), none with an overlap or pair label; the paper's sentence is re-worded to the key; ", 1),
    (lambda k: re.fullmatch(r"ablation\.order\.batch60(s|sp)?\.safe-decisions", k) is not None,
     S % 6 + "as written: the old-definition denominator, R956-1's in the cause; ", 3),
    (lambda k: re.fullmatch(r"rq3\.([a-z0-9.]+)\.analysis-s", k) is not None and not k.startswith("rq3.inator.")
     and k.split(".")[1] in {"largest", "rest", "total", "avl", "binn", "brotli", "bst", "buffer", "bzip2", "genann",
                             "heman", "ht", "jsonh", "libcsv", "libtree", "libzahl", "lil", "lodepng", "quadtree", "rgba",
                             "robotfindskitten", "tulipindicators", "urlparser"},
     S % 7 + RQ3T, 23),
    (lambda k: k == "analysis.owners-by-preference" or k.startswith("analysis.owners-by-preference."),
     S % 8 + "as measured (603 -> 22: the order makes those owners Owning again); the sentence that cites 603 is flagged "
     "to the paper session by the seat; ", 4),
    (lambda k: k.startswith("box.param.owning"),
     S % 8 + "as measured; the depth-1 rows keep counting under the producer's every-depth rule (4 of the 20 delivered "
     "are depth-1 slots whose subject is a reference); ", 4),
    (lambda k: k == "waiver.waived-bridges.tier-2",
     S % 9 + "unit: bridges applied under the tier-2 retention waiver = 0 (1 planned and dropped, bzip2); main 225's "
     "'tier-2 bridge rows 1,050' is the census receipt's count of exclusion-artifact rows, not a waiver count; ", 1),
    (lambda k: k == "waiver.fallback-extent",
     S % 9 + "unit: tree uses (816); main 225's section-77 figure of 216 counts receipt rows (108 sites, 104 applied); ", 1),
    (lambda k: k in ("waiver.entry-static", "codegen.pair-cert.static-vs-entry-waived"),
     S % 9 + "54 on both units, split differently: the audit unit libzahl 42 / brotli 8 / heman 4, main's pairs-table "
     "unit libzahl 54; ", 2),
    (lambda k: k in ("rq1.brotli.uses.delivered", "rq1.brotli.uses.rate", "rq1.total.uses.delivered", "rq1.total.uses.rate"),
     S % 10 + "brotli's twin wrapper __crat_raw_EncodeWindowBits is not emitted at 60s' (-10 raw uses in T2's full_deref "
     "unit, official 0; its 2 positions last_bytes / last_bytes_bits go with it; EncodeWindowBits' own two positions and "
     "every identity unchanged): not traced; ", 4),
    (lambda k: k in ("conf.cert.matched", "conf.cert.total"),
     S % 11 + "heman kmRay2IntersectBox::{next_point, other_point, this_point}: raw -> ref departures with no "
     "certificate match, unchanged since " + "58" + "'" * 3 + ": stated, not traced; ", 2),
    (lambda k: k == "ec2.waived",
     S % 11 + "9 = X's implicit release sites (quadtree 6, lodepng 2, tulipindicators 1); the census's 23 implicit-close "
     "receipts (C2 waiver_drop: quadtree 15, heman 4, lodepng 2, buffer 1, tulipindicators 1) exceed it by 14: quadtree's "
     "9 receipts that name the same closes as its 6 (C.2), heman's 4 scope-exit receipts beside its eight Box formals, "
     "which X counts as transferred owners with no implicit release site, and buffer's 1 (not traced); ", 1),
]
LABEL_NOTE = (S % 11 + "the frame label era5c-l01p14-v1 is the receipts' own (the frame of record: analyses a5495bf59, "
              "configuration d9a474da); ")
DROP = {"ec4.validator.certified.at-58pp", "ec4.validator.viol.at-58pp", "ec4.validator.check-sat.at-58pp",
        "ec4.validator.digest-match.at-58pp"}

out, hits, dropped, labelled = [], [0] * len(NOTES), [], 0
for l in lines:
    m = ROW.match(l)
    if not m or l.startswith("| key |"):
        out.append(l)
        continue
    c = m.groupdict()
    k = c["key"]
    if k in DROP:
        dropped.append(k)
        continue
    pre = ""
    for i, (pred, note, _) in enumerate(NOTES):
        if pred(k):
            pre += note
            hits[i] += 1
    if "era5c-l01p14-v1" in c["prov"] and re.match(r"^(ec[1-4]|conf)\.", k):
        pre += LABEL_NOTE
        labelled += 1
    if pre:
        if "|" in pre:
            die("pipe in note")
        c["prov"] = pre + c["prov"]
        nl = "| %s | %s | %s | %s | %s | %s |" % (c["key"], c["value"], c["status"], c["layer"], c["unit"], c["prov"])
        m2 = ROW.match(nl)
        if not m2 or m2.group("value") != m.group("value") or nl.count("|") != l.count("|"):
            die("row " + k)
        out.append(nl)
    else:
        out.append(l)
for i, (_, note, want) in enumerate(NOTES):
    if hits[i] != want:
        die("note %d (%s) hit %d, want %d" % (i, note[:40], hits[i], want))
if sorted(dropped) != sorted(DROP):
    die("dropped %s" % dropped)
text = "\n".join(out)
open(R + "/record-122a.md", "w", encoding="utf-8", newline="").write(text)
print("in md5", hashlib.md5(raw).hexdigest(), "out md5", hashlib.md5(text.encode()).hexdigest(), "notes", hits,
      "label notes", labelled, "dropped", len(dropped), "rows", sum(1 for x in out if ROW.match(x)) - 1)
