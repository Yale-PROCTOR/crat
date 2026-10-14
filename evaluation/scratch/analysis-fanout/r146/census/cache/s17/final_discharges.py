#!/usr/bin/env python3
"""Stream each L01^14 cache entry (mmap; never loaded whole) and dump the
retirement-final record's `discharged` list (the accepted model's discharge
receipts, retirement.rs:93-140) as JSONL, one file per program.
Usage: final_discharges.py <solve-dir> <out-dir>"""
import mmap, sys, json, glob, os, re
solve, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
dec = json.JSONDecoder()
def raw_list(m, s):
    w = 1 << 20
    while True:
        txt = m[s:s + w].decode('utf-8', errors='ignore')
        try:
            v, _ = dec.raw_decode(txt)
            return v
        except json.JSONDecodeError:
            if s + w >= len(m):
                raise
            w *= 4
progs = sys.argv[3:] or None
for wf in sorted(glob.glob(os.path.join(solve, 'workers', '*.json'))):
    w = json.load(open(wf)); prog = w['program']
    if progs and prog not in progs: continue
    entry = set(re.findall(r'[0-9a-f]{64}\.json', json.dumps(w)))
    assert len(entry) == 1, (prog, entry)
    path = os.path.join(solve, 'cache', 'era5b-model-cache-v1', entry.pop())
    f = open(path, 'rb'); m = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    finals = []; i = m.find(b'"retirement-final":{"availability"')
    while i >= 0:
        finals.append(i); i = m.find(b'"retirement-final":{"availability"', i + 1)
    rows_out = []
    for fi in finals:
        nxt = m.find(b'"retirement-rounds":{"availability"', fi)
        d = m.find(b'"discharged":[', fi)
        if d < 0 or (nxt >= 0 and d > nxt):
            continue
        lst = raw_list(m, d + len(b'"discharged":'))
        rows_out.append(lst)
    with open(os.path.join(out, prog + '.final-discharged.jsonl'), 'w') as o:
        for k, lst in enumerate(rows_out):
            for r in lst:
                r['_final_index'] = k
                o.write(json.dumps(r, sort_keys=True) + '\n')
    print(prog, os.path.basename(path), 'finals=', len(finals), 'lists=', len(rows_out), 'rows=', [len(x) for x in rows_out], flush=True)
