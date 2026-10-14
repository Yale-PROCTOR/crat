#!/usr/bin/env python3
"""ident141.py <base-census> <census>: delivered subjects by identity (program, subject_key), realized-as-predicted
(the census given BY THE EMITTED TREE: pass r141/census/cen-s39-tree for 58'''), gained / lost per program, with the
census's reason and emitted form of each moved subject. Read-only; fails closed via SystemExit."""
import csv, glob, os, sys, collections
csv.field_size_limit(10 ** 9)
def load(C):
    d, info = set(), {}
    for f in glob.glob(C.rstrip('/') + '/*.raw-boundary-subject-outcomes.tsv'):
        p = os.path.basename(f).split('.raw-boundary')[0]
        sub = {r['subject_key']: r for r in csv.DictReader(open(f.replace('subject-outcomes', 'subjects')), delimiter='\t')}
        for r in csv.DictReader(open(f), delimiter='\t'):
            k = (p, r['subject_key'])
            info[k] = (r['delivery'], r['emitted_form'], sub[r['subject_key']]['reason'], sub[r['subject_key']]['family'])
            if r['delivery'] == 'realized-as-predicted':
                d.add(k)
    return d, info
(a, ia), (b, ib) = load(sys.argv[1]), load(sys.argv[2])
if set(ia) != set(ib):
    raise SystemExit('subject sets differ')
g, l = sorted(b - a), sorted(a - b)
print(f'delivered base {len(a)} census {len(b)}: +{len(g)} / -{len(l)}')
for name, s, inf in (('gained', g, ib), ('lost', l, ib)):
    byp = collections.Counter(p for p, _ in s)
    print(name, len(s), dict(sorted(byp.items())))
    for k in s:
        print('  ', name, k[0], k[1], 'base', ia[k][:3], '-> census', ib[k][:3])
