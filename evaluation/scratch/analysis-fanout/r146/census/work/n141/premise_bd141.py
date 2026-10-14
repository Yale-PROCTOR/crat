#!/usr/bin/env python3
"""premise_bd141.py <base-census> <census>: r140 g088b/premise_bd_58pp.py with both census dirs as arguments (r141; the
labels printed are the dirs' basenames, so on batch58 / batch58pp the output is r140's premise-bd-b58pp.out): P7 rows of
<p>.raw-boundary-premise-bridge-dereferenceable.tsv summed over the twenty, by site_kind, plus the row-level diff."""
import csv, glob, collections, os, sys
csv.field_size_limit(10**9)
def load(c):
    rows = []
    for f in sorted(glob.glob(f'{c}/*.raw-boundary-premise-bridge-dereferenceable.tsv')):
        rows += list(csv.DictReader(open(f), delimiter='\t'))
    return rows
A, B = sys.argv[1].rstrip('/'), sys.argv[2].rstrip('/')
na, nb = os.path.basename(A), os.path.basename(B)
a, b = load(A), load(B)
if not a or not b:
    raise SystemExit('empty P7 table')
for c, rs in [(na, a), (nb, b)]:
    print(c, 'total', len(rs), dict(sorted(collections.Counter(r['site_kind'] for r in rs).items())),
          'call-bridge formals', len({(r['program'], r['function'], r['binding']) for r in rs if r['site_kind'] == 'call-bridge'}))
    print('  by program', dict(sorted(collections.Counter(r['program'] for r in rs).items())))
k = lambda r: tuple(r.values())
A_, B_ = collections.Counter(map(k, a)), collections.Counter(map(k, b))
print('header', list(a[0].keys()))
print(f'rows only at {na}:'); [print('  ', x) for x in sorted(A_ - B_)]
print(f'rows only at {nb} (non-assignment kinds):'); [print('  ', x) for x in sorted(B_ - A_) if not x[2].startswith('assignment')]
print(f'rows only at {nb}, assignment kinds:', sum(v for x, v in (B_ - A_).items() if x[2].startswith('assignment')))
