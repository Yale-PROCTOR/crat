#!/usr/bin/env python3
"""analysis-fanout r125/b (relay 125, S31(b)): decl-uses under the twin reading vs as emitted, from the EXISTING
typed-counter outputs (rq2_pos_counter T2 uses.tsv) in r122/gtree/t5/out (read-only; nothing run).

  in25(p)      = sum `official` over input/<p>/uses.tsv            (CROWN's usage rule, 2025 form, on rs-crown)
  twin rem     = sum `official_raw` over <side>/<p>/uses.tsv       (keyed through the exposure twin: the
                 __crat_safe_<f> body read as <f>, the C-named wrapper unkeyed; raw-pointer roots only)
  as-emitted   = sum `official_raw` (twin == '-') + sum `official` (twin == 'wrapper')   (t5-verify emit.py, F1)
  rate         = (in25 - rem) / in25 ; median over programs with in25 > 0.
usage: decl_uses_twin.py <side> (ours56 | ours54p | ours14u)"""
import csv, json, os, statistics, sys

O = 'scratch/analysis-fanout/r146/trees/t5/out'  # r133: ours58 = main/batch58
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
side = sys.argv[1]


def rows(s, p):
    d = os.path.join(O, s, p)
    assert open(os.path.join(d, 'status.txt')).read().split()[0] == 'ok', (s, p)
    return list(csv.DictReader(open(os.path.join(d, 'uses.tsv')), delimiter='\t'))


pct = lambda a, b: f'{100.0 * a / b:.1f}%' if b else '---'
out, rt, ra = [], [], []
T = dict(in25=0, tw=0, ae=0)
for p in PROGS:
    i = sum(int(r['official']) for r in rows('input', p))
    u = rows(side, p)
    tw = sum(int(r['official_raw']) for r in u)
    ae = sum(int(r['official_raw']) for r in u if r['twin'] == '-') + \
        sum(int(r['official']) for r in u if r['twin'] == 'wrapper')
    T['in25'] += i; T['tw'] += tw; T['ae'] += ae
    if i:
        rt.append(100.0 * (i - tw) / i); ra.append(100.0 * (i - ae) / i)
    out.append(dict(program=p, in25=i, twin_rem=tw, ae_rem=ae, twin_deliv=i - tw, ae_deliv=i - ae,
                    twin_rate=pct(i - tw, i), ae_rate=pct(i - ae, i),
                    n_wrapper=sum(r['twin'] == 'wrapper' for r in u)))
w = csv.DictWriter(sys.stdout, fieldnames=list(out[0]), delimiter='\t', lineterminator='\n')
w.writeheader(); w.writerows(out)
print(f"TOTAL\t{T['in25']}\t{T['tw']}\t{T['ae']}\t{T['in25']-T['tw']}\t{T['in25']-T['ae']}\t"
      f"{pct(T['in25']-T['tw'],T['in25'])}\t{pct(T['in25']-T['ae'],T['in25'])}")
print(f"MEDIAN(n={len(rt)})\ttwin {statistics.median(rt):.4f}\tas-emitted {statistics.median(ra):.4f}")
