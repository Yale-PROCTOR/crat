#!/usr/bin/env python3
"""relay 130 t4: keys (strict beside R945-1) from per-program.json + decls/*.tsv; checks strict against the record copy
(read only). Writes keys.tsv, keys.json, table.md, credit-shapes.tsv, ours-absent.tsv, laertes-own-before.tsv."""
import csv, glob, json, os, re, statistics
HERE = os.path.dirname(os.path.abspath(__file__))
REC = 'tmp/scratchpad/wt067/paper/numbers-of-record.md'
rec = {}
for l in open(REC):
    m = re.match(r'^\| ([^ |]+) \|', l)
    if m:
        rec[m.group(1)] = [x.strip() for x in l.strip().strip('|').split('|')][1]
D = json.load(open(os.path.join(HERE, 'per-program.json')))
PROGS = list(D)
K = lambda p: p.replace('.', '')
pct = lambda a, b: f'{100.0 * a / b:.1f}%'
med = lambda xs: f'{statistics.median(xs):.1f}%'
rows = []


def add(key, strict, r945, num, den, note):
    rows.append({'key': key, 'strict': strict, 'r945': r945, 'numerator': num, 'denominator': den, 'note': note,
                 'record': rec.get(key, '')})


def tsv(path):
    return list(csv.DictReader(open(path), delimiter='\t'))


# ours: split the R945-1 gain by class (typed: no T1 row; source corroboration in decls/ours-*.tsv)
gain = {}
absent_rows = []
for p in PROGS:
    c = {'retyped': 0, 'removed': 0, 'foreign': 0, 'no-outer': 0}
    for r in tsv(f'{HERE}/decls/ours-{p}.tsv'):
        if r['class'] == 'a:absent':
            c['retyped' if r['source'] == 'kept-nonpointer' else 'removed'] += 1
            absent_rows.append([p, r['kind'], r['owner'], r['name'], r['idx'], r['input_outer'], 'made safe (R945-1)',
                                r['source'], r['emitted']])
        elif r['class'] == 'raw:foreign-declaration':
            c['foreign'] += 1
            absent_rows.append([p, r['kind'], r['owner'], r['name'], r['idx'], r['input_outer'], 'raw (counterpart kept)',
                                r['source'], r['emitted']])
        elif r['class'].startswith('n:'):
            c['no-outer'] += 1
    gain[p] = c
with open(f'{HERE}/ours-absent.tsv', 'w') as f:
    f.write('program\tkind\towner\tname\tidx\tinput_outer\tverdict\tsource\temitted\n')
    for a in absent_rows:
        f.write('\t'.join(a) + '\n')

R = {s: {'strict': [], 'r945': []} for s in ('ours', 'crown', 'laertes')}
for p in PROGS:
    r, k, b = D[p], K(p), D[p]['before']
    g = gain[p]
    s0, s1 = r['ours.strict'], r['ours.r945']
    note = (f'+{s1 - s0}: {g["retyped"]} re-typed to a non-pointer (c2rust freshN holding the pointee), '
            f'{g["removed"]} removed (binding merged / gone)' + (f'; {g["foreign"]} kept as a foreign declaration '
                                                                 f'(raw, not made safe)' if g['foreign'] else ''))
    add(f'rq1.{k}.alldecl.delivered', str(s0), str(s1), str(s1), str(b), note)
    add(f'rq1.{k}.alldecl.rate', pct(s0, b), pct(s1, b), str(s1), str(b), note)
    R['ours']['strict'].append(s0 / b)
    R['ours']['r945'].append(s1 / b)
    c0, c1 = r['crown.strict'], r['crown.r945']
    add(f'rq2.{k}.alldecl.crown', pct(c0, b), pct(c1, b), str(c1), str(b),
        'CROWN: 0 absent, 0 re-typed; no change' if c0 == c1 else f'+{c1 - c0}')
    R['crown']['strict'].append(c0 / b)
    R['crown']['r945'].append(c1 / b)
    if r['laertes.status'] != 'ok':
        add(f'rq2.{k}.alldecl.laertes', '0.0%', '0.0%', '0', str(b), 'R891-1: as CROWN\'s Table 2 reports it (no Laertes tree)')
        R['laertes']['strict'].append(0.0)
        R['laertes']['r945'].append(0.0)
        continue
    l0, l1 = r['laertes.strict'], r['laertes.r945']
    nb = r['laertes.cls'].get('x:absent-after-no-before-counterpart', 0)
    own = (f'; provenance only, against Laertes\'s own before tree: {r["own.r945"]}/{r["own.before"]} = '
           f'{pct(r["own.r945"], r["own.before"])}' if p in ('bzip2', 'genann', 'libcsv', 'libzahl', 'lil',
                                                              'robotfindskitten', 'tulipindicators', 'urlparser') else '')
    add(f'rq2.{k}.alldecl.laertes', pct(l0, b), pct(l1, b), str(l1), str(b),
        (f'{nb} input declarations with no counterpart in Laertes\'s before tree: not made safe' if nb else
         '0 removed / re-typed') + own)
    R['laertes']['strict'].append(l0 / b)
    R['laertes']['r945'].append(l1 / b)

TB = sum(D[p]['before'] for p in PROGS)
for v in ('strict', 'r945'):
    pass
s0 = sum(D[p]['ours.strict'] for p in PROGS)
s1 = sum(D[p]['ours.r945'] for p in PROGS)
add('rq1.total.alldecl.delivered', str(s0), str(s1), str(s1), str(TB), 'over the twenty')
add('rq1.total.alldecl.rate', pct(s0, TB), pct(s1, TB), str(s1), str(TB), 'pooled over the twenty')
add('rq1.median.alldecl.rate', med([100 * x for x in R['ours']['strict']]), med([100 * x for x in R['ours']['r945']]),
    '', '', 'median of the twenty per-program fractions')
c0 = sum(D[p]['crown.strict'] for p in PROGS)
c1 = sum(D[p]['crown.r945'] for p in PROGS)
add('rq2.total.alldecl.crown', pct(c0, TB), pct(c1, TB), str(c1), str(TB), 'pooled over the twenty')
add('rq2.median.alldecl.crown', med([100 * x for x in R['crown']['strict']]), med([100 * x for x in R['crown']['r945']]),
    '', '', 'median over the twenty')
L19 = [p for p in PROGS if D[p]['laertes.status'] == 'ok']
B19 = sum(D[p]['before'] for p in L19)
l0 = sum(D[p]['laertes.strict'] for p in L19)
l1 = sum(D[p]['laertes.r945'] for p in L19)
lm19s = [100 * D[p]['laertes.strict'] / D[p]['before'] for p in L19]
lm19r = [100 * D[p]['laertes.r945'] / D[p]['before'] for p in L19]
add('rq2.total.alldecl.laertes', pct(l0, TB), pct(l1, TB), str(l1), str(TB),
    f'over the twenty, brotli 0 / {D["brotli"]["before"]} (097); over the nineteen: {pct(l0, B19)} -> {pct(l1, B19)} '
    f'({l1}/{B19})')
add('rq2.median.alldecl.laertes', med([100 * x for x in R['laertes']['strict']]),
    med([100 * x for x in R['laertes']['r945']]), '', '',
    f'median over the twenty, brotli 0.0 (097); over the nineteen: {med(lm19s)} -> {med(lm19r)}')

# check strict against the record
for r in rows:
    r['strict_eq_record'] = 'yes' if r['strict'] == r['record'] else ('n/a' if not r['record'] else 'NO')
json.dump(rows, open(f'{HERE}/keys.json', 'w'), indent=1)
with open(f'{HERE}/keys.tsv', 'w') as f:
    f.write('key\tstrict\tr945\tnumerator\tdenominator\trecord\tstrict_eq_record\tnote\n')
    for r in rows:
        f.write('\t'.join(r[c] for c in ('key', 'strict', 'r945', 'numerator', 'denominator', 'record',
                                          'strict_eq_record', 'note')) + '\n')
bad = [r['key'] for r in rows if r['strict_eq_record'] != 'yes']
print(len(rows), 'keys; strict != record:', bad)

# credit shapes (Table 5's reading credits, Table 4's does not)
with open(f'{HERE}/credit-shapes.tsv', 'w') as f:
    f.write('tool\tprogram\tkind\towner\tname\tidx\tshape\temitted_depth0_type\n')
    n = {}
    for side in ('ours', 'crown', 'laertes'):
        n[side] = 0
        for path in sorted(glob.glob(f'{HERE}/decls/{side}-*.tsv')):
            p = path.rsplit('/', 1)[1][len(side) + 1:-4]
            for r in tsv(path):
                if r['credit'] != '-':
                    n[side] += 1
                    f.write('\t'.join([side, p, r['kind'], r['owner'], r['name'], r['idx'], r['credit'],
                                       r['out_depth0_type']]) + '\n')
print('credit shapes:', n)

# Laertes own-before (provenance only)
with open(f'{HERE}/laertes-own-before.tsv', 'w') as f:
    f.write('program\tlaertes_tree\tinput_population\tinput_made_safe\tinput_no_before_counterpart\t'
            'own_population\town_made_safe_strict\town_made_safe_r945\town_rate\town_pop_with_input_counterpart\n')
    for p in L19:
        r = D[p]
        f.write('\t'.join(map(str, [p, 'laertes-laertes' if p in ('bzip2', 'genann', 'libcsv', 'libzahl', 'lil',
                                                                      'robotfindskitten', 'tulipindicators', 'urlparser')
                                    else 'laertes-crown', r['before'], r['laertes.r945'],
                                    r['laertes.cls'].get('x:absent-after-no-before-counterpart', 0),
                                    r['own.before'], r['own.strict'], r['own.r945'],
                                    pct(r['own.r945'], r['own.before']), r['own.pop_in_input']])) + '\n')
