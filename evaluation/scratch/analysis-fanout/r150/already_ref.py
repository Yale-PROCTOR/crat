#!/usr/bin/env python3
"""already_ref.py -- relay 150 item 4 (Appendix C:59): the already-reference bindings at 60s' and the declarations
identity. The bindings: R454's list (agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv,
counts_toward_N == true: c2rust's `let ref mut freshN` bindings, references in the input) joined on (program,
owner, binding) to main/batch60sp's census subjects (owner_fn, subject_key's local name)."""
import collections, csv, glob, os, re
csv.field_size_limit(10 ** 9)
B = "scratch/main/batch60sp"
L = "docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv"
want = [r for r in csv.DictReader(open(L), delimiter="\t") if r["counts_toward_N"] == "true"]
subj, outc = {}, {}
for f in glob.glob(B + "/*.raw-boundary-subjects.tsv"):
    p = os.path.basename(f).split(".raw-boundary-subjects.tsv")[0]
    for r in csv.DictReader(open(f), delimiter="\t", quoting=csv.QUOTE_NONE):
        subj[r["subject_key"]] = (p, r)
    for r in csv.DictReader(open(B + "/%s.raw-boundary-subject-outcomes.tsv" % p), delimiter="\t", quoting=csv.QUOTE_NONE):
        outc[r["subject_key"]] = r
print("subjects", len(subj))
idx = collections.defaultdict(list)
for k, (p, r) in subj.items():
    m = re.search(r"::([A-Za-z_][A-Za-z0-9_]*)#\d+$", k) or re.search(r"::_?([A-Za-z_][A-Za-z0-9_]*)$", k)
    name = k.rsplit("::", 1)[-1].split("#")[0]
    idx[(p, r["owner_fn"], name)].append(k)
hit, miss = [], []
for w in want:
    ks = idx.get((w["program"], w["owner"], w["binding"]), [])
    (hit if ks else miss).append((w, ks))
print("R454 bindings", len(want), "joined", len(hit), "missing", [(w["program"], w["owner"], w["binding"]) for w, _ in miss][:5])
fam = collections.Counter((subj[k][1]["family"], subj[k][1]["decision"], outc.get(k, {}).get("delivery", "?")) for w, ks in hit for k in ks)
print("joined subjects by family/decision/delivery", dict(fam))
# the identity over all subjects
c = collections.Counter()
for k, (p, r) in subj.items():
    o = outc.get(k, {})
    c[(r["family"], r["decision"], o.get("delivery", "-"))] += 1
print("subjects by family/decision/delivery (top):", c.most_common(12))
