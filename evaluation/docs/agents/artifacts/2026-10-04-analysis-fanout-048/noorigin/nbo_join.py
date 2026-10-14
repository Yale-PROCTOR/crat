"""nbo_join.py <nbo-all.tsv> <guards-all.tsv>: per distinct slot (program, kind slot), the union of the leaf kinds over every
no_borrow_origin entry that names it; split into the slots NoOrigin forbids (a NoBorrowOrigin guard exists) and the exempt
(nullable) ones; by slot kind (return / behind a parameter / field)."""
import collections, csv, sys
sys.path.insert(0, '.')
from nbo_kinds import primary
csv.field_size_limit(10**9)
leaves = collections.defaultdict(set); kind = {}
for r in csv.DictReader(open(sys.argv[1]), delimiter='\t'):
    k = (r['program'], r['slot'])
    leaves[k] |= set(x for x in r['leaves'].split(',') if x)
    kind[k] = 'field' if r['field'] != '-' else ('return' if r['slot'].endswith('::_0@d0') else 'behind-parameter' if r['root_dereferences'] != '0' else 'other')
g = {tuple(l.rstrip('\n').split('\t')) for l in open(sys.argv[2])}
missing = g - set(leaves)
print('guards', len(g), 'no_borrow_origin slots', len(leaves), 'guards without an entry', len(missing), sorted(missing)[:5])
for name, sel in (('FORBIDDEN (guarded)', lambda k: k in g), ('exempt (nullable)', lambda k: k not in g)):
    ks = [k for k in leaves if sel(k)]
    print(f'== {name}: {len(ks)}')
    print('  by primary:', dict(collections.Counter(primary(leaves[k]) for k in ks)))
    print('  by slot kind x primary:', dict(collections.Counter((kind[k], primary(leaves[k])) for k in ks)))
    print('  slots with each leaf kind:', dict(collections.Counter(x for k in ks for x in leaves[k])))
    print('  by program:', dict(collections.Counter(k[0] for k in ks)))
for k in sorted(leaves):
    if k in g and primary(leaves[k]) not in ('call-or-allocation-only',):
        print('  FORB', k[0], k[1], kind[k], ','.join(sorted(leaves[k])) or '-', primary(leaves[k]))
