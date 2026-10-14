#!/usr/bin/env python3
"""Large entries: decode ONLY each snapshot's `metadata` and `value_origins` byte ranges (located by
markers.py's unique snapshot-level markers), run the return_port_owning port, join to the model head."""
import json, sys, os, collections
sys.path.insert(0, 'scratch/analysis-fanout/r100/keymap')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model_head import read_head
from return_port_port import run
path, markers, secend = sys.argv[1], sys.argv[2], int(sys.argv[3])
hits = [(int(l.split()[0]), l.split()[1]) for l in open(markers)]
md = [a for a, m in hits if m.startswith(',"metadata"')]
nrc = [a for a, m in hits if m.startswith(',"no_ref')]
vo = [a for a, m in hits if m.startswith(',"value_origins')]
prog, universe, model, _ = read_head(path)
dec = json.JSONDecoder()
res = []
with open(path, 'rb') as f:
    for i in range(len(md)):
        s = md[i] + len(',"metadata":'); f.seek(s); meta = json.loads(f.read(nrc[i] - s))
        s2 = vo[i] + len(',"value_origins":'); stop = md[i + 1] if i + 1 < len(md) else secend
        f.seek(s2); v, _ = dec.raw_decode(f.read(stop - s2).decode())
        a, em, h = run({'metadata': meta, 'value_origins': v})
        res.append((i, em, collections.Counter(h.values())))
        del meta, v
agree = len({tuple(r[1]) for r in res}) == 1
em = res[-1][1]
print(prog, 'snapshots', len(res), 'agree', agree, 'admitted', len(em), dict(collections.Counter(model.get(k, '?') for k in em)), 'holds', dict(res[-1][2]), flush=True)
with open('admitted-rows.tsv', 'a') as out:
    for i, ems, _ in res:
        for k in ems: out.write(f"{prog}\t{i}\t{k}\t{model.get(k,'?')}\n")
