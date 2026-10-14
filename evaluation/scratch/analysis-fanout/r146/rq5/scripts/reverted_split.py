"""Side read (not a key): batch 58's 34 reverted rows by function, attribution, family and the compiler codes of the
function or its class (final-reverts class_id; compiler-diagnostics function column)."""
import csv, collections, sys
csv.field_size_limit(10**9)
C = sys.argv[1]
PROGS = sys.argv[2:] or ('brotli', 'quadtree', 'libzahl')  # r141: programs as arguments (default = r140's three)
for p in PROGS:
    try: fr = {r['identity']: r for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-final-reverts.tsv'), delimiter='\t') if r['kind'] == 'function'}
    except FileNotFoundError: continue
    dg = collections.defaultdict(set)
    for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-compiler-diagnostics.tsv'), delimiter='\t'): dg[r['function']].add(r['error_code'])
    c = collections.Counter()
    for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-subject-outcomes.tsv'), delimiter='\t'):
        if r['delivery'] != 'reverted': continue
        f = fr.get(r['owner_fn'], {}); cid = f.get('class_id', '-')
        codes = sorted(dg.get(r['owner_fn'], set()) | dg.get('class#' + cid.rsplit(':', 1)[-1], set()))
        c[(p, r['owner_fn'].split('::')[-1], f.get('attribution'), r['family'], ','.join(codes) or 'none')] += 1
    for k, v in sorted(c.items()): print(v, *k, sep='\t')
    print(p, 'diagnostic functions:', {k: sorted(v) for k, v in dg.items()})
