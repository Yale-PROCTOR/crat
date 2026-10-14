#!/usr/bin/env python3
"""r146/trees: per-program measurement diffs 58''' (batch58pps39) -> 60s' (batch60sp) from the counter tables:
positions.tsv (form raw <-> non-raw by position key) and per-function uses (t4 full_roots; t5 as-emitted raw on CROWN's
population). Writes work/diffs.json and prints a readable summary."""
import csv, json, collections, sys
csv.field_size_limit(10**9)
T = 'scratch/analysis-fanout/r146/trees'
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
tsv = lambda f: list(csv.DictReader(open(f), delimiter='\t'))
raw = lambda f: f.startswith('raw')
out = {}
for p in PROGS:
    a = tsv(f'{T}/t4/out-ours-58pps39/ours/{p}/positions.tsv'); b = tsv(f'{T}/t4/out-ours-60sp/ours/{p}/positions.tsv')
    K = lambda r: (r['kind'], r['owner'], r['name'], r['idx'], r['synthetic'], r['depth'], r['layer'])
    ca = collections.Counter(K(r) for r in a); cb = collections.Counter(K(r) for r in b)
    if any(v > 1 for v in ca.values()) or any(v > 1 for v in cb.values()):
        raise SystemExit(f'duplicate position keys in {p}')
    A = {K(r): r for r in a}; B = {K(r): r for r in b}
    only_a = sorted(set(A) - set(B)); only_b = sorted(set(B) - set(A)); C = set(A) & set(B)
    to_safe = sorted(k for k in C if raw(A[k]['form']) and not raw(B[k]['form']))
    to_raw = sorted(k for k in C if not raw(A[k]['form']) and raw(B[k]['form']))
    form = sorted(k for k in C if A[k]['form'] != B[k]['form'] and raw(A[k]['form']) == raw(B[k]['form']))
    def fu(path, col, rule=None):
        r = collections.Counter()
        for x in tsv(path):
            r[(x['function'], x['twin'])] += rule(x) if rule else int(x[col])
        return r
    ua = fu(f'{T}/t4/out-ours-58pps39/ours/{p}/uses.tsv', 'full_roots'); ub = fu(f'{T}/t4/out-ours-60sp/ours/{p}/uses.tsv', 'full_roots')
    ae = lambda x: int(x['official_raw']) if x['twin'] == '-' else (int(x['official']) if x['twin'] == 'wrapper' else 0)
    da = fu(f'{T}/t5/out/ours58pps39/{p}/uses.tsv', None, ae); db = fu(f'{T}/t5/out/ours60sp/{p}/uses.tsv', None, ae)
    def delta(x, y):
        d = collections.Counter()
        for k in set(x) | set(y):
            v = y.get(k, 0) - x.get(k, 0)
            if v:
                d[k[0]] += v
        return {k: v for k, v in sorted(d.items(), key=lambda kv: (kv[1], kv[0])) if v}
    fmt = lambda k, r: f"{k[0]} {k[1].replace('src::', '')}::{k[2]} d{k[5]}L{k[6]} {r}"
    out[p] = dict(to_safe=[fmt(k, A[k]['form'] + '->' + B[k]['form']) for k in to_safe],
                  to_raw=[fmt(k, A[k]['form'] + '->' + B[k]['form']) for k in to_raw],
                  form_only=[fmt(k, A[k]['form'] + '->' + B[k]['form']) for k in form],
                  only_58ppp=[fmt(k, A[k]['form']) for k in only_a], only_60sp=[fmt(k, B[k]['form']) for k in only_b],
                  uses=delta(ua, ub), uses_net=sum(ub.values()) - sum(ua.values()),
                  decl_uses=delta(da, db), decl_uses_net=sum(db.values()) - sum(da.values()))
json.dump(out, open(f'{T}/work/diffs.json', 'w'), indent=1)
for p, o in out.items():
    if not (o['to_safe'] or o['to_raw'] or o['form_only'] or o['uses'] or o['decl_uses'] or o['only_58ppp'] or o['only_60sp']):
        continue
    print(f"== {p}: positions +{len(o['to_safe'])} / -{len(o['to_raw'])} (form-only {len(o['form_only'])}); "
          f"raw uses net {o['uses_net']:+d}; CROWN-population raw uses net {o['decl_uses_net']:+d}")
    for x in o['to_safe']: print('   +', x)
    for x in o['to_raw']: print('   -', x)
    for x in o['form_only']: print('   ~', x)
    for x in o['only_58ppp']: print('   <', x)
    for x in o['only_60sp']: print('   >', x)
    print('   uses:', {k.replace('src::', ''): v for k, v in o['uses'].items()})
    print('   decl-uses:', {k.replace('src::', ''): v for k, v in o['decl_uses'].items()})
