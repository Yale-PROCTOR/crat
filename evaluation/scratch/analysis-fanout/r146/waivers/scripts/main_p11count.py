#!/usr/bin/env python3
"""p11count.py <census> (main relay 322): P11's receipts by kind and program (<p>.raw-boundary-pair-premise.tsv; under
integers-only the global kinds must read 0) and R486-2's StaticVsEntryWaived certificates (pairs rows whose peer receipts
name pair-disjoint:static-vs-entry:exported-entry-static-waiver), rows and distinct call sites, by program."""
import csv, collections, glob, os, sys
csv.field_size_limit(10**9)
D = sys.argv[1]
kinds = collections.Counter(); kp = collections.defaultdict(collections.Counter)
for f in sorted(glob.glob(D + '/*.raw-boundary-pair-premise.tsv')):
    for r in csv.DictReader(open(f), delimiter='\t'):
        kinds[r['kind']] += 1; kp[r['kind']][r['program']] += 1
print('P11 pair-premise rows by kind: ' + ('; '.join(f"{k} {v} (" + ', '.join(f'{p} {n}' for p, n in kp[k].most_common()) + ')' for k, v in kinds.most_common()) or 'none'))
g = kinds.get('global-value', 0) + kinds.get('global-storage', 0)
print(f'P11 global kinds (global-value + global-storage): {g}')
rows = collections.Counter(); sites = collections.defaultdict(set)
for f in sorted(glob.glob(D + '/*.raw-boundary-pairs.tsv')):
    for r in csv.DictReader(open(f), delimiter='\t'):
        if 'exported-entry-static-waiver' in (r.get('peer_receipts') or ''):
            rows[r['program']] += 1; sites[r['program']].add((r['caller'], r['callee'], r['site']))
print(f'R486-2 StaticVsEntryWaived: rows {sum(rows.values())}, sites {sum(len(s) for s in sites.values())} (' + ', '.join(f'{p} {rows[p]}/{len(sites[p])}' for p in sorted(rows)) + ')')
