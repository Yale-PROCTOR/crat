#!/usr/bin/env python3
"""analysis-fanout 112 (relay 138, D6): copy of r133 p1_count.py; ONLY change: the universe rule also admits a subject whose census decision (subjects.tsv `decision`) is a safe form, whatever its outcome (D6: a subject the analysis decided Box, or any safe form, is a safe decision). r122 g088a: section 1 of r110/p1-rq1/build_stage.py (count()) verbatim, run on a census dir given as argv[1]."""
import collections, csv, glob, os, re, sys
csv.field_size_limit(10 ** 9)
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
BOXF = ('box', 'box-slice', 'opt-box-slice')
R454F = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'
r454 = {(r['program'], r['owner'], r['binding']) for r in csv.DictReader(open(R454F), delimiter='\t')
        if r['counts_toward_N'] == 'true'}
assert len(r454) == 36
def count(C):
    n = deliv = safe = unmod = 0
    box = collections.Counter(); fam_und = collections.Counter(); r454hit = 0
    boxp = collections.Counter()
    for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        dec = {x['subject_key']: x['decision'] for x in csv.DictReader(open(f.replace('subject-outcomes', 'subjects')), delimiter='\t')}
        for r in csv.DictReader(open(f), delimiter='\t'):
            n += 1
            d = r['delivery'] == 'realized-as-predicted'
            deliv += d
            s = r['family'] in SAFE or d or dec[r['subject_key']] in SAFE  # D6
            safe += s
            unmod += r['family'] == 'unmodeled'
            if d and r['emitted_form'] in BOXF:
                box[r['emitted_form']] += 1; boxp[p] += 1
            if s and not d:
                fam_und[r['family']] += 1
            key = re.sub(r'#\d+$', '', r['subject_key'])
            owner, _, b = key.rpartition('::')
            if (p, owner, b) in r454:
                assert s and not d, (p, key)
                r454hit += 1
    return dict(n=n, deliv=deliv, safe=safe, unmod=unmod, box=box, fam_und=fam_und, r454=r454hit, boxp=boxp)
c = count(sys.argv[1])
D, N_, S = c['deliv'], c['n'], c['safe'] - c['r454']
print('n', N_, 'delivered', D, 'safe_raw', c['safe'], 'r454', c['r454'], 'safe', S, 'unmod', c['unmod'])
print('rate2', f'{D / S * 100:.2f}%', 'rate1', f'{D / S * 100:.1f}%')
print('box', sum(c['box'].values()), dict(c['box']))
print('box by program', dict(sorted(c['boxp'].items())))
print('modeled-fraction', f'{D / (N_ - c["unmod"] - 36) * 100:.1f}%', f'{D}/{N_ - c["unmod"] - 36}')
print('safe undelivered by family', dict(sorted(c['fam_und'].items())))
