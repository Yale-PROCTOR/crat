#!/usr/bin/env python3
"""famdiff141.py <base-census> <census>: r140 famdiff58pp.py with the two census dirs as arguments (r141); per column, the
subjects whose (family, delivery, emitted_form, model_kind, decision, reason) moved base -> census. Fails closed."""
import csv, glob, os, sys
csv.field_size_limit(10 ** 9)
def load(C):
    d = {}
    for f in glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv'):
        p = os.path.basename(f).split('.raw-boundary')[0]
        sub = {r['subject_key']: r for r in csv.DictReader(open(f.replace('subject-outcomes', 'subjects')), delimiter='\t')}
        for r in csv.DictReader(open(f), delimiter='\t'):
            s = sub.get(r['subject_key'], {})
            d[(p, r['subject_key'])] = (r['family'], r['delivery'], r['emitted_form'], s.get('model_kind'), s.get('decision'), s.get('reason'))
    return d
A, B = sys.argv[1].rstrip('/'), sys.argv[2].rstrip('/')
a, b = load(A), load(B)
if set(a) != set(b):
    print('subject sets differ: only base', len(set(a) - set(b)), 'only census', len(set(b) - set(a)))
    for k in sorted(set(a) ^ set(b))[:40]: print('   ', 'base-only' if k in a else 'census-only', *k)
print('subjects', len(a)) if len(a) == len(b) else print('subjects', len(a), len(b))
for i, n in enumerate(['family', 'delivery', 'emitted_form', 'model_kind', 'decision', 'reason']):
    mv = [(k, a[k][i], b[k][i]) for k in sorted(set(a) & set(b)) if a[k][i] != b[k][i]]
    print(n, 'moves ' + os.path.basename(A) + '->' + os.path.basename(B) + ':', len(mv))
    for x in mv: print('  ', *x)
