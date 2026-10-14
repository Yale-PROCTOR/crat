#!/usr/bin/env python3
"""r146/trees: per-key declaration moves 58''' -> 60s': Table 5 (t5r945 per-key, as emitted and twin) and Table 4
(t4r945 decls/ours-<p>.tsv, R945-1 column). Writes work/decl_diffs.json; prints the moves."""
import csv, json
csv.field_size_limit(10**9)
T = 'scratch/analysis-fanout/r146/trees'
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
safe = lambda x: x[1] == 'safe-form' or x[1].startswith('shape:')
out = {}
for p in PROGS:
    o = {}
    for tool in ('ours', 'ours-twin'):
        a = json.load(open(f'{T}/t5r945/per-key/{tool}-{p}.json')); b = json.load(open(f'{T}/t5r945-60sp/per-key/{tool}-{p}.json'))
        if set(a) != set(b):
            raise SystemExit(f't5 key sets differ {tool} {p}')
        o[f't5.{tool}.gained'] = sorted(k for k in a if not safe(a[k]) and safe(b[k]))
        o[f't5.{tool}.lost'] = sorted(k for k in a if safe(a[k]) and not safe(b[k]))
    rd = lambda f: {(r['kind'], r['owner'], r['name'], r['idx']): r for r in csv.DictReader(open(f), delimiter='\t')}
    a = rd(f'{T}/t4r945/decls/ours-{p}.tsv'); b = rd(f'{T}/t4r945-60sp/decls/ours-{p}.tsv')
    if set(a) != set(b):
        raise SystemExit(f't4 decl key sets differ {p}: {sorted(set(a) ^ set(b))[:5]}')
    fm = lambda k: f'{k[0]} {k[1].replace("src::", "")}::{k[2]}'
    o['t4.gained'] = sorted(fm(k) for k in a if a[k]['r945'] != 'yes' and b[k]['r945'] == 'yes')
    o['t4.lost'] = sorted(fm(k) for k in a if a[k]['r945'] == 'yes' and b[k]['r945'] != 'yes')
    if any(o.values()):
        out[p] = o
json.dump(out, open(f'{T}/work/decl_diffs.json', 'w'), indent=1)
for p, o in out.items():
    print('==', p, {k: len(v) for k, v in o.items()})
    for k, v in o.items():
        for x in v:
            print('  ', k, x.replace('src::', ''))
