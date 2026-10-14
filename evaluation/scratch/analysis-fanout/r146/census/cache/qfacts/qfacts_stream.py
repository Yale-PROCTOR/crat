#!/usr/bin/env python3
"""qfacts_stream.py SOLVE_DIR OUT.tsv [PROG...]
Streamed (64 MiB chunks, never whole) read of every QualifierFacts export record in each program's completed
cache entry (workers/<p>.json completed.cache_entry). Each record's unescaped `fields` object is matched:
  {"fields":{"depth":D,"fatness":{"state":S,"value":V},"level":L, ... ,"sign":{"state":S2,"value":V2},"slot":SLOT},"key":"QualifierFacts/
Writes program, slot, depth, fatness_state, fatness_value, level, sign_state, sign_value.
Completeness: the record count per program is compared afterwards with the model map size (layers.py's slots=).
READ ONLY."""
import json, os, re, sys
S = sys.argv[1].rstrip('/')
out = open(sys.argv[2], 'w')
PROGS = sys.argv[3:] or ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv',
                         'libtree', 'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators',
                         'urlparser']
REC = re.compile(rb'\{"fields":\{"depth":(\d+),"fatness":\{"state":"(\w+)","value":"([^"]*)"\},"level":"(\w+)",'
                 rb'.{0,600}?"sign":\{"state":"(\w+)","value":"([^"]*)"\},"slot":"([^"]+)"\},"key":"QualifierFacts/')
CH = 1 << 26
out.write('program\tslot\tdepth\tfatness_state\tfatness_value\tlevel\tsign_state\tsign_value\n')
for p in PROGS:
    w = json.load(open(f'{S}/workers/{p}.json'))
    e = w['completed']['cache_entry']
    if not os.path.exists(e):
        e = os.path.join(S, 'cache/era5b-model-cache-v1', os.path.basename(e))
    seen, nbytes = {}, 0
    with open(e, 'rb') as fh:
        tail = b''
        while True:
            chunk = fh.read(CH)
            if not chunk:
                break
            nbytes += len(chunk)
            buf = tail + chunk
            last = 0
            for m in REC.finditer(buf):
                slot = m.group(7).decode()
                seen[slot] = (m.group(1).decode(), m.group(2).decode(), m.group(3).decode(), m.group(4).decode(),
                              m.group(5).decode(), m.group(6).decode())
                last = m.end()
            tail = buf[max(last, len(buf) - 8192):]
    for slot, v in sorted(seen.items()):
        out.write('\t'.join((p, slot) + v) + '\n')
    out.flush()
    print(p, os.path.basename(e), nbytes, 'records', len(seen), file=sys.stderr, flush=True)
