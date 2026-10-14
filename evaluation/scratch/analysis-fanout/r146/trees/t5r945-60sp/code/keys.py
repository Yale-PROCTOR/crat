#!/usr/bin/env python3
"""r130/t5: the Table 5 declaration keys, strict (the record, pre-R945-1) and R945-1, -> keys.tsv / keys.md."""
import json, re, statistics, sys
T5 = 'scratch/analysis-fanout/r146/trees/t5r945-60sp'
REC = 'tmp/scratchpad/wt067/paper/numbers-of-record.md'
rec = {}
for line in open(REC):
    m = re.match(r'^\| (rq[12]\.[^ |]+) \| ([^|]*)\| ([^|]*)\|', line)
    if m:
        rec[m.group(1)] = (m.group(2).strip(), m.group(3).strip())
per = json.load(open(f'{T5}/per-program.json'))
f1 = lambda x: f'{x:.1f}%'
rows = []


def add(k, new, num, den, note):
    strict = rec.get(k, ('(absent from the record)', ''))[0]
    rows.append((k, strict, new, num, den, note, 'moves' if strict != new else 'equal'))


B = sum(r['before'] for r in per)
for r in per:
    p, kk = r['program'], r['program'].replace('.', '')
    add(f'rq1.{kk}.decl.before', str(r['before']), str(r['before']), '-', 'before does not move (per MIR local on rs-crown = |U| = evaluation.tsv before)')
    add(f'rq1.{kk}.decl.delivered', str(r['ours_made']), str(r['ours_made']), str(r['before']), 'as emitted (twinned fn: wrapper params, twin locals)')
    add(f'rq1.{kk}.decl.rate', f1(100 * r['ours_made'] / r['before']), str(r['ours_made']), str(r['before']), 'as emitted')
    add(f'rq1.{kk}.decl-twin.rate', f1(100 * r['ours_twin_made'] / r['before']), str(r['ours_twin_made']), str(r['before']), 'twin reading')
    add(f'rq2.{kk}.decl.crown', f1(100 * r['crown_made'] / r['before']), str(r['crown_made']), str(r['before']), 'evaluation.tsv (CROWN binary) = typed counter under R945-1, 0 movers')
    if p == 'brotli':
        add(f'rq2.{kk}.decl.laertes', '0.0%', '-', '-', 'no Laertes tree; CROWN Table 2 dagger (R891-1)')
    else:
        add(f'rq2.{kk}.decl.laertes', f1(r['L_rate']), str(r['L_made']), str(r['L_U']),
            f"0 movers; no-counterpart keys kept not safe: {r['L_nocp']}; own-before provenance {r['L_own_before']-r['L_own_after']}/{r['L_own_before']} = {f1(r['L_own_rate'])}")
D = sum(r['ours_made'] for r in per)
DT = sum(r['ours_twin_made'] for r in per)
C = sum(r['crown_made'] for r in per)
L = sum(r['L_made'] for r in per if r['program'] != 'brotli')
add('rq1.total.decl.before', str(B), str(B), '-', '')
add('rq1.total.decl.delivered', str(D), str(D), str(B), 'as emitted')
add('rq1.total.decl.rate', f1(100 * D / B), str(D), str(B), 'as emitted')
add('rq1.median.decl.rate', f1(statistics.median(100 * r['ours_made'] / r['before'] for r in per)), '-', '-', 'median of 20')
add('rq1.total.decl-twin.rate', f1(100 * DT / B), str(DT), str(B), 'twin')
add('rq1.median.decl-twin.rate', f1(statistics.median(100 * r['ours_twin_made'] / r['before'] for r in per)), '-', '-', 'median of 20')
add('rq2.total.decl.twin-rate', f1(100 * DT / B), str(DT), str(B), '= rq1.total.decl-twin.rate (evaluation.tex:290)')
add('rq2.total.decl.crown', str(C), str(C), str(B), 'declarations CROWN makes safe')
add('rq2.total.decl.crown-rate', f1(100 * C / B), str(C), str(B), '')
add('rq2.median.decl.crown', f1(statistics.median(r['crown_rate'] for r in per)), '-', '-', 'median of 20')
add('rq2.total.decl.laertes', str(L), str(L), str(B), 'brotli counted 0 (dagger)')
add('rq2.total.decl.laertes-rate', f1(100 * L / B), str(L), str(B), '')
add('rq2.median.decl.laertes', f1(statistics.median([r['L_rate'] for r in per if r['program'] != 'brotli'] + [0.0])), '-', '-', 'median of 20, brotli 0.0 (dagger)')
with open(f'{T5}/keys.tsv', 'w') as f:
    f.write('key\tstrict(pre-R945-1, record)\tR945-1\tnumerator\tdenominator\tnote\tmove\n')
    for r in rows:
        f.write('\t'.join(r) + '\n')
for r in rows:
    if r[6] == 'moves' or 'total' in r[0] or 'median' in r[0]:
        print('\t'.join(r[:5]) + '\t' + r[6])
print(len(rows), 'keys;', sum(1 for r in rows if r[6] == 'moves'), 'move')
