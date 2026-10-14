"""rq6_guarded.py <guarded-eighteen.tsv> <names.tsv>: relay 064 item 1 -- RQ6's `guarded` row (rq3-inator 008) read independently:
safe SLOTS of the analysis (ref + owning) on the eighteen, with guarded repair (the frame of record, `*_base`) against
unconditional repair (the row, `*_row`); checked against the per-slot names file (one line per slot whose kind moves)."""
import csv, collections, sys
rows = [r for r in csv.DictReader(open(sys.argv[1]), delimiter='\t') if r['program'] != 'TOTAL']
names = list(csv.DictReader(open(sys.argv[2]), delimiter='\t'))
SAFE = {'ref', 'owning'}
mv = collections.defaultdict(collections.Counter)
for n in names:
    mv[n['program']][(n['baseline'], n['row'])] += 1
tb = tr = 0; ahead = equal = behind = 0; out = []
for r in rows:
    sb = int(r['ref_base']) + int(r['owning_base']); sr = int(r['ref_row']) + int(r['owning_row'])
    assert sb == int(r['safe_base']) and sr == int(r['safe_row']), r['program']
    assert int(r['slots']) == sb + int(r['raw_base']) == sr + int(r['raw_row']), r['program']
    d = sr - sb
    # the names file must account for the delta: safe->raw counts -1, raw->safe +1
    dn = sum(n for (a, b), n in mv[r['program']].items() if a not in SAFE and b in SAFE) - sum(n for (a, b), n in mv[r['program']].items() if a in SAFE and b not in SAFE)
    assert dn == d, (r['program'], dn, d)
    tb += sb; tr += sr
    if d < 0: ahead += 1
    elif d == 0: equal += 1
    else: behind += 1
    out.append((r['program'], sb, sr, d, dict(mv[r['program']])))
for o in out: print(*o, sep='\t')
print(f'TOTAL guarded {tb} unconditional {tr} delta {tr - tb} ({100 * (tr - tb) / tb:.2f} %); guarded ahead {ahead}, equal {equal}, behind {behind}; programs {len(rows)}; names {len(names)}')
