#!/usr/bin/env python3
"""r133/trees: Table 5 decl-uses, AS EMITTED (t5-verify emit.py / apply_116 F1 rule) and twin, per side.
Reconstructs r122/gtree/t5/as-emitted.out (written inline in r122; no script kept there) from the counter's uses.tsv:
  in25 = sum official on input; twin_rem = sum official_raw; ae_rem = sum official_raw (twin=='-') + sum official (twin=='wrapper')
usage: as_emitted.py SIDE [SIDE ...]  (reads out/<side>/<p>/uses.tsv; prints the table)"""
import csv, os, sys
O = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out')
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
pct = lambda a, b: f'{100.0 * a / b:.1f}%' if b else '---'
def rows(s, p):
    d = os.path.join(O, s, p)
    assert open(os.path.join(d, 'status.txt')).read().split()[0] == 'ok', (s, p)
    return list(csv.DictReader(open(os.path.join(d, 'uses.tsv')), delimiter='\t'))
print('program\tin25\tside\ttwin_rem\tae_rem\tdeliv_twin\tdeliv_ae\trate_twin\trate_ae\tn_wrapper\tn_twin')
for side in sys.argv[1:]:
    T = [0, 0, 0]
    for p in PROGS:
        i = sum(int(r['official']) for r in rows('input', p)); u = rows(side, p)
        tw = sum(int(r['official_raw']) for r in u)
        ae = sum(int(r['official_raw']) for r in u if r['twin'] == '-') + sum(int(r['official']) for r in u if r['twin'] == 'wrapper')
        nw = sum(r['twin'] == 'wrapper' for r in u); nt = sum(r['twin'] == 'twin' and '__crat_safe_' in r['function'] for r in u)
        T[0] += i; T[1] += tw; T[2] += ae
        print(f'{p}\t{i}\t{side}\t{tw}\t{ae}\t{i-tw}\t{i-ae}\t{pct(i-tw,i)}\t{pct(i-ae,i)}\t{nw}\t{nt}')
    print(f'TOTAL\t{T[0]}\t{side}\t{T[1]}\t{T[2]}\t{T[0]-T[1]}\t{T[0]-T[2]}\t{pct(T[0]-T[1],T[0])}\t{pct(T[0]-T[2],T[0])}')
