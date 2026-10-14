#!/usr/bin/env python3
"""relay 145 section 3 (from 144 section 2): the realization gap -- model-safe (model_kind ref / owning) census subjects
that are NOT realized (subject-outcomes delivery != realized-as-predicted), by cause, every subject named, split into
(a) holds by design, (b) pattern gaps (owning lane named per class), (c) unexplained; each (b) class counted on the nine
AND on the twenty at the same head.
usage: sizing.py <nine-run-dir with prep/<p>/census-t1> <twenty census dir (main/batch60sp)> <out-prefix>
The label of a subject: the census subject's reason when it is not '-'; else its exclusion's first reason; a
'reverted' delivery is labelled by the compile check (with the function's diagnostic code where one is named)."""
import collections, csv, glob, os, re, sys

csv.field_size_limit(10 ** 9)
NINE = ["running-example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]

A = [  # holds by design (not buildable): prefixes of the label
    "held:void-pointee", "held:io-domain", "escapes-via-field-store", "pair-raw-view", "held:pair-not-shown-disjoint",
    "pair-not-shown-disjoint", "pair-proven-overlap", "copy-source-coupled", "held:thin-extent", "held:address-observation-only",
    "box-param-caller-retains", "aliased-storage-withdrawn", "held:retained-alias", "held:retained-access",
    "held:into-held-formal", "held:into-held-binding", "held:masked-index-runtime-length", "held:local-callee-access-extent",
    "freed-slot", "box-param-indirect-callers", "return-certificate-indirect-callers", "held:dropped-site",
    "box-param-lend-withheld",
]
B = {  # pattern gaps -> owning lane (relay 144 section 2's routing)
    "return-not-adapted": "wave-6l / main (returns)",
    "compile-check revert": "the lane whose rendering the diagnostic names (main / wave-5d by default)",
    "unsupported-decl-shape": "era-5c / main (declaration shapes)",
    "place-read-pointee": "era-5c / main (declaration shapes)",
    "box-initializer-unsupported": "wave-6a (box initializers)",
    "box-construction-unmappable": "wave-6a (box initializers)",
    "box-withdrawn-at-emission": "wave-6a (box initializers)",
    "ptr-comparison": "main / wave-5d (A5 views)",
    "slice-cursor-use": "slicecursor (cursor forms)",
    "slice-neg-or-unknown-offset": "slicecursor (cursor forms)",
    "cursor-base-unavailable": "slicecursor (cursor forms)",
    "call-site-not-adapted": "main / wave-5d (call-site bridges, A5 views)",
    "missing-required-site": "main / wave-5d (call-site bridges, A5 views)",
    "cross-class-interval-collision": "main / wave-5d (A5 classes: an interval collision between two classes' edits)",
    "seam-site-overlap": "main / wave-5d (call-site bridges, A5 views)",
    "opt-use-unsupported": "wave-6o (Option / nullability)",
    "null-init": "wave-6o (Option / nullability)",
    "opt-local-construction": "wave-6o (Option / nullability)",
    "slice-use-unsupported": "wave-6a / wave-5d (slice receivers and arguments)",
    "slice-local-construction": "wave-6a / wave-5d (slice receivers and arguments)",
}


def tsv(path):
    if not os.path.exists(path):
        return []
    return list(csv.DictReader(open(path, encoding="utf-8"), delimiter="\t", quoting=csv.QUOTE_NONE))


def label_of(s, o, diag):
    if o.get("delivery") == "reverted":
        fn = s.get("owner_fn", "")
        codes = sorted(diag.get(fn, set()))
        return "compile-check revert" + (" [" + ",".join(codes) + "]" if codes else " [no diagnostic in the function: closure / class]")
    r = s.get("reason", "-")
    if r and r != "-":
        return r
    ex = s.get("exclusion", "-") or "-"
    if ex != "-":
        m = re.match(r"^terminal-not-applied:(?:dropped-site:|blocked-subject:)?([^:;]+)", ex)
        return (m.group(1) if m else ex.split(";")[0])
    return "(no reason recorded)"


def classify(label):
    if label.startswith("compile-check revert"):
        return "b", B["compile-check revert"], "compile-check revert"
    for k, lane in B.items():
        if label.startswith(k):
            return "b", lane, k
    for k in A:
        if label.startswith(k):
            return "a", "-", k
    return "c", "-", label


def gap(census_dir, prog):
    subj = {s["subject_key"]: s for s in tsv(f"{census_dir}/{prog}.raw-boundary-subjects.tsv")}
    outs = tsv(f"{census_dir}/{prog}.raw-boundary-subject-outcomes.tsv")
    diag = collections.defaultdict(set)
    for d in tsv(f"{census_dir}/{prog}.raw-boundary-compiler-diagnostics.tsv"):
        code = d.get("code") or next((v for v in d.values() if v and re.fullmatch(r"E0\d{3}", v)), "")
        diag[d.get("function", "")].add(code or "?")
    rows = []
    for o in outs:
        s = subj.get(o["subject_key"])
        if s is None:
            continue
        if s.get("model_kind") not in ("ref", "owning"):
            continue
        if o.get("delivery") == "realized-as-predicted":
            continue
        lab = label_of(s, o, diag)
        cls, lane, key = classify(lab)
        rows.append({"program": prog, "subject": o["subject_key"], "model": s["model_kind"], "family": s.get("family", ""),
                     "delivery": o.get("delivery", ""), "label": lab, "class": cls, "group": key, "lane": lane})
    return rows


def main():
    nine_run, twenty, out = sys.argv[1], sys.argv[2], sys.argv[3]
    nine = []
    for p in NINE:
        d = f"{nine_run}/prep/{p}/census-t1"
        if os.path.isdir(d):
            nine += gap(d, p)
        else:
            print("WARNING: no census for", p)
    progs20 = sorted(os.path.basename(f).split(".raw-boundary-subjects.tsv")[0] for f in glob.glob(f"{twenty}/*.raw-boundary-subjects.tsv"))
    tw = []
    for p in progs20:
        tw += gap(twenty, p)
    for name, rows in (("nine", nine), ("twenty", tw)):
        with open(f"{out}-{name}.tsv", "w") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else ["program"], delimiter="\t", lineterminator="\n")
            w.writeheader()
            for r in rows:
                w.writerow(r)
    c9 = collections.Counter((r["class"], r["group"]) for r in nine)
    c20 = collections.Counter((r["class"], r["group"]) for r in tw)
    lanes = {(r["class"], r["group"]): r["lane"] for r in nine + tw}
    print("nine: %d model-safe not realized (%s); twenty: %d (%d programs; %s)" % (
        len(nine), dict(collections.Counter(r["delivery"] for r in nine)), len(tw), len(progs20),
        dict(collections.Counter(r["delivery"] for r in tw))))
    for cls in "abc":
        keys = sorted({k for k in list(c9) + list(c20) if k[0] == cls}, key=lambda k: (-c9.get(k, 0), -c20.get(k, 0), k[1]))
        print("== (%s) nine %d, twenty %d" % (cls, sum(c9[k] for k in keys), sum(c20[k] for k in keys)))
        for k in keys:
            print("  %-45s nine %3d  twenty %4d  %s" % (k[1][:45], c9.get(k, 0), c20.get(k, 0), lanes[k] if cls == "b" else ""))


if __name__ == "__main__":
    main()
