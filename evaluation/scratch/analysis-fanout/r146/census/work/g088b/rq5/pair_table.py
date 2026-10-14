"""pair_table.py <census-dir>: relay 052 item 1 -- who decides each pair site (analysis-fanout 035).
Units: ROW = one argument position at a call with >=1 pointer peer (pairs.tsv row); RECEIPT = one (row, peer) entry;
PAIR SITE = one unordered argument pair at one call (a receipt carried by both rows counted once: per
(program, caller, callee, pair, kind) the larger of the two sides' row counts)."""
import csv, glob, collections, re, sys
csv.field_size_limit(10**9)
F = sys.argv[1]
R = []
for f in sorted(glob.glob(F + '/*.raw-boundary-pairs.tsv')):
    R += list(csv.DictReader(open(f), delimiter='\t'))
def kind(pr):
    v = pr.split(':', 1)[1]
    if v.startswith('overlapping'): return 'not-proven'
    if 'a5-proven-disjoint' in v: return 'classifier'
    m = re.match(r'clear:pair-disjoint:(.*):pair-disjointness-certificate', v)
    k = m.group(1)
    return 'allocator-contract' if k == 'distinct-roots:allocator-contract' else k
rows = collections.Counter(); per_kind_rows = collections.Counter(); rec = collections.Counter()
side = collections.defaultdict(lambda: collections.Counter())
prog = collections.defaultdict(collections.Counter)
for r in R:
    ks = [kind(p) for p in r['peer_receipts'].split(';') if p]
    for p in r['peer_receipts'].split(';'):
        if not p: continue
        k = kind(p); rec[k] += 1
        pair = p.split(':', 1)[0]
        a = pair.split('->')[0].split('/')
        side[(r['program'], r['caller'], r['callee'], pair, k)][r['argument_index']] += 1
    if r['verdict'] == 'overlapping':
        cat = 'not-proven'
    else:
        cl = 'classifier' in ks; ce = any(k not in ('classifier', 'not-proven') for k in ks)
        cat = 'classifier+certificate' if cl and ce else 'classifier' if cl else 'certificate'
    rows[cat] += 1; prog[r['program']][cat] += 1
    for k in set(ks): per_kind_rows[k] += 1
sites = collections.Counter()
for (p, c, ce, pair, k), s in side.items():
    sites[k] += max(s.values())
print('rows', len(R), dict(rows))
print('rows by role', collections.Counter((r['verdict'], r['role']) for r in R))
print('receipts', sum(rec.values()), dict(rec))
print('rows carrying each kind', dict(per_kind_rows))
print('pair sites (unordered, deduplicated)', sum(sites.values()), dict(sites))
for p in sorted(prog): print(p, dict(prog[p]))
