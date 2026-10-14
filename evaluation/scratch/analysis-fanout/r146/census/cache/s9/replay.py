#!/usr/bin/env python3
"""r105/s9: every occurrence of the export key "reader_replay" in each L01^14 cache entry
(bounded 64 MiB chunks), decoded from a <=16 MiB window. The export's reader_replay holds the
ACCEPTED round's receipts (export.rs begin_round clears it each round; reader_replay.rs
begin_round pushes one expectation per represented candidate whose view is Ref and field is
neither Ref nor Raw, i.e. exactly the candidates whose guard r = ref(view) & own(field) holds)."""
import json, sys
import os, glob
sys.path.insert(0, "scratch/analysis-fanout/r146/census/work")
import frame146  # r141: FRAME=58pp | s39
S = frame146.SOLVE
OUTD = os.path.join(os.path.dirname(os.path.abspath(__file__)), frame146.FRAME); os.makedirs(OUTD, exist_ok=True)
CH = 64 << 20; KEY = b'"reader_replay":'
dec = json.JSONDecoder()
# r141: the twenty from the worker receipts (the S39 row's own launch manifest names only its ten)
progs = sys.argv[1:] or [x["program"] for x in json.load(open("worktrees/era5c-l01p14u-solve/launch-manifest.json"))["programs"]]
for p in progs:
    e = json.load(open(f"{S}/workers/{p}.json"))["completed"]["cache_entry"]
    if not os.path.exists(e): e = os.path.join(frame146.CACHE, os.path.basename(e))  # r141: host-b path
    offs = []
    with open(e, "rb") as f:
        pos = 0; tail = b""
        while True:
            c = f.read(CH)
            if not c: break
            buf = tail + c; base = pos - len(tail); i = 0
            while True:
                i = buf.find(KEY, i)
                if i < 0: break
                o = base + i + len(KEY)
                if o not in offs: offs.append(o)
                i += 1
            pos += len(c); tail = buf[-32:]
        vals = []
        for o in offs:
            f.seek(o); w = f.read(16 << 20).decode("utf-8", "replace")
            vals.append(dec.raw_decode(w)[0])
    print(p, "occurrences", len(offs), json.dumps(vals)[:1500], flush=True)
