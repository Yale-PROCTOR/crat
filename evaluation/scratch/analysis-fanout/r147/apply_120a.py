#!/usr/bin/env python3
"""apply_120a.py -- analysis-fanout 120a (relay 147 item 4): the four ec4.validator.* keys at the landed 60s' from
wave-6o report 151's receipts. Input = docs origin/main:paper/numbers-of-record.md; output r147/record-120a.md.
Fails closed. usage: apply_120a.py"""
import csv, hashlib, re, subprocess, sys

R = "scratch/analysis-fanout/r147"
DOCS = "crat/docs"
PREV = "58" + "'" * 3


def die(m):
    raise SystemExit("apply_120a: FAIL: " + m)


def git(*a):
    r = subprocess.run(["git", "-C", DOCS] + list(a), capture_output=True)
    if r.returncode:
        die(r.stderr.decode())
    return r.stdout


raw = git("show", "origin/main:paper/numbers-of-record.md")
rec_receipts = git("show", "origin/main:agents/artifacts/2026-10-14-wave-6o-151/validator-receipts-batch60sp.tsv")
if rec_receipts != open(R + "/receipts-151.tsv", "rb").read():
    die("receipts-151.tsv is not docs origin/main's")
rows = list(csv.DictReader(open(R + "/receipts-151.tsv", encoding="utf-8"), delimiter="\t"))
kv = {}
for l in open("scratch/main/batch60sp/per-program.kv"):
    m = re.search(r"(?:^| )program=(\S+)", l)
    d = re.search(r"raw_boundary_cache_model_sha256=([0-9a-f]+)", l)
    if m:
        kv[m.group(1)] = d.group(1) if d else None
if len(rows) != 20 or set(r["program"] for r in rows) != set(kv) or len(kv) != 20:
    die("program sets")
cert = sum(1 for r in rows if r["viol"] == "0" and r["repair"] == "0" and r["decline"] == "0")
viol = sum(int(r["viol"]) for r in rows)
cs = sum(int(r["check_sat"]) for r in rows)
me = sum(int(r["model_entries"]) for r in rows)
dm = sum(1 for r in rows if kv[r["program"]] == r["model_sha256"])
uns = [(r["program"], r["viol_unslotted_container"]) for r in rows if r["viol_unslotted_container"] != "0"]
ok = sum(r["status"] == "ok" for r in rows)
acc = sum(r["replay"] == "accept" for r in rows)
to_own = sum(int(r["to_owning"]) for r in rows)
if (cert, viol, cs, me, dm, ok, acc, uns, to_own) != (20, 0, 0, 0, 20, 19, 19, [("heman", "3")], 144):
    die("receipts read %r" % ((cert, viol, cs, me, dm, ok, acc, uns, to_own),))

HDR = ("60s' (the FINAL frame; landed 2026-10-14T03:39:27Z, assembler 151, R1088-1; borrow-ownership b3825fe91 -> 32d966b9f; "
       "census main/batch60sp (main 225), frame of record era5c-r215-kindorder (analysis 1d8dcd40, configuration d9a474da, "
       "launch 2e94d9a5), env frames/l01p14u-s39-mutlend-o-env.sh): analysis-fanout 120a (relay 147 item 4): wave-6o report 151 "
       "(relay 189; docs agents/reports/wave-6o/151-*.md, receipts agents/artifacts/2026-10-14-wave-6o-151/"
       "validator-receipts-batch60sp.tsv): the BorrowCoverage validator rebuilt at the landed 32d966b9f (analyses a5495bf5; "
       "151's process note: the overnight driver's first run took the base b3825fe91 and wrote no receipts, the receipts of "
       "record are the re-run at the landed head), K from batch60sp's delivered kinds (delivered_source export on all twenty), "
       "one program per process, cache-only, after the landing; read by this lane over the twenty rows and cross-checked "
       "against main/batch60sp/per-program.kv: ")
NEW = {
    "ec4.validator.certified": ("20", "programs whose receipt certifies (viol 0, repair 0, decline 0): 20 of 20 = 19 status ok + "
                                "heman ok-unslotted-container (3 unslotted-container self-edges in kmRay2IntersectBox, the "
                                "benign R864-2 class; viol_unslotted_container 3, viol 0); replay accept on 19, heman reject "
                                "(the receipt row); Owning -> Ref certificate departures 0 (to_owning 144 delivered across the "
                                "twenty under Ref > Owning > Raw, model_entries 0 on every program)"),
    "ec4.validator.viol": ("0", "viol summed over the twenty = 0 (no program has viol > 0); viol_unslotted_container 3 (heman), "
                           "not a coverage violation"),
    "ec4.validator.check-sat": ("0", "check_sat summed over the twenty = 0 and model_entries 0 (the check runs without a solve)"),
    "ec4.validator.digest-match": ("20", "the receipt's model_sha256 equals the census's raw_boundary_cache_model_sha256 for 20 "
                                   "of 20 (at %s 19: tulipindicators recorded no digest under its delivery-custody failure; "
                                   "at 60s' custody is clean, data=true, so all twenty compare)" % PREV),
}
ROW = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) "
                 r"\| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")
lines = raw.decode("utf-8").split("\n")
out, hit, log = list(lines), {}, []
for i, l in enumerate(lines):
    m = ROW.match(l)
    if m and m.group("key") in NEW:
        k = m.group("key")
        if k in hit:
            die("duplicate " + k)
        c = m.groupdict()
        v, cause = NEW[k]
        if "|" in HDR + cause:
            die("pipe")
        old_v = c["value"]
        c["prov"] = HDR + cause + "; previously at %s: " % PREV + c["prov"]
        c["value"] = v
        out[i] = "| %s | %s | %s | %s | %s | %s |" % (c["key"], c["value"], c["status"], c["layer"], c["unit"], c["prov"])
        if out[i].count("|") != l.count("|"):
            die("pipes " + k)
        hit[k] = i
        log.append((k, old_v, v))
if set(hit) != set(NEW):
    die("missing %s" % (set(NEW) - set(hit)))
if sum(a != b for a, b in zip(lines, out)) != 4:
    die("changed lines")
text = "\n".join(out)
open(R + "/record-120a.md", "w", encoding="utf-8", newline="").write(text)
print("in md5", hashlib.md5(raw).hexdigest(), "out md5", hashlib.md5(text.encode()).hexdigest())
for x in log:
    print("  %s %s -> %s" % x)
