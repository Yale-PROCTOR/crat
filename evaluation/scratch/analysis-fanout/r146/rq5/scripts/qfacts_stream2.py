#!/usr/bin/env python3
"""qfacts_stream2.py (r141, relay 141, group rq5): r133 g088a qfacts_stream.py with two additions and the record regex,
chunking and output UNCHANGED:
  qfacts_stream2.py --solve SOLVE_DIR OUT.tsv      entries from workers/<p>.json completed.cache_entry (the original)
  qfacts_stream2.py --manifest MANIFEST.tsv CACHE_DIR OUT.tsv   entries = CACHE_DIR/<fingerprint>.json per manifest row
Streamed in 64 MiB chunks, never whole; before every chunk MemAvailable must be >= 30 GiB (else SystemExit).
Also writes OUT.tsv.fat (program, slot, state:value for present @d0 rows = r133's fatfacts derivation) and
OUT.tsv.counts (records per program). READ ONLY on the cache."""
import csv, json, os, re, sys
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv',
         'libtree', 'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators',
         'urlparser']
REC = re.compile(rb'\{"fields":\{"depth":(\d+),"fatness":\{"state":"(\w+)","value":"([^"]*)"\},"level":"(\w+)",'
                 rb'.{0,600}?"sign":\{"state":"(\w+)","value":"([^"]*)"\},"slot":"([^"]+)"\},"key":"QualifierFacts/')
CH = 1 << 26
def memavail_gib():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable:'):
            return int(l.split()[1]) / (1 << 20)
    raise SystemExit('no MemAvailable')
if sys.argv[1] == '--solve':
    S, OUT = sys.argv[2].rstrip('/'), sys.argv[3]
    def entry(p):
        w = json.load(open(f'{S}/workers/{p}.json'))
        e = w['completed']['cache_entry']
        if not os.path.exists(e):
            e = os.path.join(S, 'cache/era5b-model-cache-v1', os.path.basename(e))
        return e
elif sys.argv[1] == '--manifest':
    M, CD, OUT = sys.argv[2], sys.argv[3].rstrip('/'), sys.argv[4]
    man = {r['program']: r['fingerprint'] for r in csv.DictReader(open(M), delimiter='\t')}
    if sorted(man) != sorted(PROGS):
        raise SystemExit('manifest programs differ: %s' % sorted(man))
    def entry(p):
        e = f'{CD}/{man[p]}.json'
        if not os.path.exists(e):
            raise SystemExit('missing entry ' + e)
        return e
else:
    raise SystemExit('usage')
out = open(OUT, 'w')
fat = open(OUT + '.fat', 'w')
cnt = open(OUT + '.counts', 'w')
out.write('program\tslot\tdepth\tfatness_state\tfatness_value\tlevel\tsign_state\tsign_value\n')
for p in PROGS:
    e = entry(p)
    seen, nbytes = {}, 0
    with open(e, 'rb') as fh:
        tail = b''
        while True:
            if memavail_gib() < 30:
                raise SystemExit(f'MemAvailable below 30 GiB while streaming {p}; stopped')
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
    if nbytes != os.path.getsize(e):
        raise SystemExit(f'short read {p}')
    for slot, v in sorted(seen.items()):
        out.write('\t'.join((p, slot) + v) + '\n')
        if v[1] == 'present' and slot.endswith('@d0'):
            fat.write(f'{p}\t{slot}\t{v[1]}:{v[2]}\n')
    out.flush(); fat.flush()
    cnt.write(f'{p}\t{os.path.basename(e)}\t{nbytes}\t{len(seen)}\n'); cnt.flush()
    print(p, os.path.basename(e), nbytes, 'records', len(seen), file=sys.stderr, flush=True)
