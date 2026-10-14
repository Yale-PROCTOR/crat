#!/usr/bin/env python3
"""For each L01^14 cache entry: slice origin.licensing by the byte offsets in licensing-offsets.txt
(json.loads of that slice only), run the return_port_owning port per snapshot, and join the admitted
keys to the entry's model (read by r100's bounded model_head.read_head)."""
import json, sys, os, collections
sys.path.insert(0, 'scratch/analysis-fanout/r100/keymap')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model_head import read_head
from return_port_port import run
C = 'worktrees/era5c-l01p14-restored-solve/cache/era5b-model-cache-v1/'
offs = {l.split()[0]: (int(l.split()[2]), int(l.split()[3])) for l in open('licensing-offsets.txt')}
skip = set(sys.argv[1:])
out = open('admitted-rows.tsv', 'a')
for name, (s, e) in offs.items():
    if name in skip: continue
    if e - s > 400 << 20: print('SKIP-LARGE', name, e - s, flush=True); continue
    prog, universe, model, _ = read_head(C + name)
    with open(C + name, 'rb') as f:
        f.seek(s); snaps = json.loads(f.read(e - s))
    sets = []
    for snap in snaps:
        a, em, h = run(snap)
        sets.append((snap['offset'], tuple(em), collections.Counter(h.values())))
    same = len({x[1] for x in sets}) == 1
    em = sets[-1][1]
    kinds = collections.Counter(model.get(k, '?') for k in em)
    print(prog, 'snapshots', len(snaps), 'agree', same, 'admitted', len(em), dict(kinds), 'holds', dict(sets[-1][2]), flush=True)
    for off, ems, _ in sets:
        for k in ems:
            out.write(f"{prog}\t{off}\t{k}\t{model.get(k,'?')}\n")
    out.flush()
