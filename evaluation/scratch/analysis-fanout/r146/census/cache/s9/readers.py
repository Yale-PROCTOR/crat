#!/usr/bin/env python3
"""r105/s9: the era-5b licensing reader arm at the frame of record (L01^14 restored solve).
Per program: reader functions / parameters, reader candidates, transfers (Present = represented,
else Missing), the reference-effect candidates (C05), and for each candidate the L01^14 model
kinds of (view local _N@d0, field slot) from r100's reverse-index (the entry's model map).
The guard r = ref(view) AND own(field) (solver.rs lend_guard). The view is joined to the
frame-14 census through r100's keymap (slot_key -> subject delivery).
Entries are read in bounded 64 MiB chunks; each value is decoded from a <=64 MiB window."""
import collections, csv, json, sys
import os, glob
sys.path.insert(0, "scratch/analysis-fanout/r146/census/work")
import frame146  # r141: FRAME=58pp | s39
S = frame146.SOLVE
OUTD = os.path.join(os.path.dirname(os.path.abspath(__file__)), frame146.FRAME); os.makedirs(OUTD, exist_ok=True)
K = "scratch/analysis-fanout/r146/census/work/g088b/keymap141/" + frame146.FRAME  # r141
CH = 64 << 20
dec = json.JSONDecoder()
KEYS = [b'"reader_functions":', b'"reader_candidates":', b'"reader_transfers":', b'"reference_effects":']

def grab_all(path):
    found = {}
    with open(path, "rb") as f:
        pos = 0; tail = b""
        while len(found) < len(KEYS):
            c = f.read(CH)
            if not c: break
            buf = tail + c; base = pos - len(tail)
            for k in KEYS:
                if k not in found:
                    i = buf.find(k)
                    if i >= 0: found[k] = base + i + len(k)
            pos += len(c); tail = buf[-64:]
        out = {}
        for k, off in found.items():
            f.seek(off); w = f.read(CH).decode("utf-8", "replace")
            out[k.decode().strip('":')] = dec.raw_decode(w)[0]
    return out

model = {}; behind = {}
with open(f"{K}/reverse-index.tsv") as fh:
    for r in csv.DictReader(fh, delimiter="\t"):
        model[(r["program"], r["slot_key"])] = r["model_kind_l01p14"]
        behind[(r["program"], r["slot_key"])] = (r["subject_key"], r["behind_delivered"], r["delivered_roles"], r["slot_kind_class"], r["mir_name"])
census = {}
with open(f"{K}/keymap.tsv") as fh:
    for r in csv.DictReader(fh, delimiter="\t"):
        if r["row_source"] == "subject":
            census[(r["program"], r["slot_key"])] = (r["subject_key"], r["family"], r["delivery"], r["emitted_form"])

# r141: the twenty from the worker receipts (the S39 row's own launch manifest names only its ten)
progs = sys.argv[1:] or [x["program"] for x in json.load(open("worktrees/era5c-l01p14u-solve/launch-manifest.json"))["programs"]]
tot = collections.Counter(); rows = []
for p in progs:
    e = json.load(open(f"{S}/workers/{p}.json"))["completed"]["cache_entry"]
    if not os.path.exists(e): e = os.path.join(frame146.CACHE, os.path.basename(e))  # r141: host-b path
    g = grab_all(e)
    rf, rc, rt, re_ = g.get("reader_functions", []), g.get("reader_candidates", []), g.get("reader_transfers", []), g.get("reference_effects", {})
    rep = {}
    for t in rt:
        c = t["candidate"]; cov = t["coverage"]
        rep[(c["function"], c["block"], c["statement"])] = cov.get("state", "?") if isinstance(cov, dict) else json.dumps(cov)[:40]
    pc = collections.Counter()
    for c in rc:
        view = f"{c['function']}::_{c['destination']['local']}@d0"
        vk = model.get((p, view), "absent"); fk = model.get((p, c["field_key"]), "absent")
        audit = rep.get((c["function"], c["block"], c["statement"]), "no-transfer-row")
        guard = (vk == "ref" and fk == "owning")
        cen = census.get((p, view))
        b = behind.get((p, view), ("-",) * 5)
        rows.append(dict(program=p, function=c["function"], block=c["block"], statement=c["statement"], view=view,
                         field=c["field_key"], view_kind=vk, field_kind=fk, audit=audit, guard_r=int(guard),
                         view_class=b[3], mir_name=b[4], census_subject=cen[0] if cen else "-",
                         census_family=cen[1] if cen else "-", census_delivery=cen[2] if cen else "-",
                         census_form=cen[3] if cen else "-", behind_delivered=b[1], delivered_roles=b[2]))
        pc[(vk, fk)] += 1
        tot["candidates"] += 1; tot["audit_" + audit] += 1; tot["guard_true"] += guard
    rec = re_.get("candidates", []) if isinstance(re_, dict) else []
    tot["reader_functions"] += len(rf); tot["reader_params"] += sum(len(r["parameters"]) for r in rf)
    tot["transfers"] += len(rt); tot["reference_effect_candidates"] += len(rec)
    print(p, "functions", len(rf), "params", sum(len(r["parameters"]) for r in rf), "candidates", len(rc),
          "transfers", len(rt), "ref_effect_candidates", len(rec), dict(pc), flush=True)
print("TOTAL", dict(tot))
cols = list(rows[0].keys()) if rows else []
with open(OUTD + "/candidates.tsv", "w") as fh:
    w = csv.DictWriter(fh, cols, delimiter="\t"); w.writeheader(); w.writerows(rows)
