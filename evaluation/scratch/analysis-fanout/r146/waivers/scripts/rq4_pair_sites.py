#!/usr/bin/env python3
"""rq4_pair_sites.py <census-dir> <scratch>: wave-6o 097's pair_sites.py `instrument` step (docs agents/tools/runtime/pair_sites.py,
pure Python: copies each emitted tree under <scratch> and maps the pair sites) per program; prints sites / instrumented /
unchecked / unmapped per program. Nothing is built or run."""
import collections, glob, os, sys
sys.path.insert(0, 'scratch/analysis-fanout/r146/waivers/work/agents/tools/runtime')
import pair_sites
C, S = sys.argv[1], sys.argv[2]
tot = collections.Counter()
for f in sorted(glob.glob(C + '/*.raw-boundary-pairs.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    import csv
    n = sum(1 for r in csv.DictReader(open(f), delimiter='\t') if r['role'] in ('raw-view', 'primary'))
    if not n: continue
    sites = pair_sites.instrument(C, p, os.path.join(S, p))
    st = collections.Counter(s[2] for s in sites)
    print(p, len(sites), dict(st)); tot['sites'] += len(sites); tot.update(st)
print('TOTAL', dict(tot))
