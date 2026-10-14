#!/usr/bin/env python3
"""build_rq5_d6.py -> out/rq5-rows-58-d6.tsv   (analysis-fanout 112, relay 138 D6)

RQ5's row file at batch 58 under D6: r133c/rq5-rows-58.tsv (1,627 rows) WITH its verifier's 7 corrections
(r133c/verify/indep/diff-vs-r133c.tsv: side-condition -> undefined), plus the subjects D6 counts in: every
census subject whose census decision (subjects.tsv `decision`) is a safe form, that p1_count's rule left out
(family not safe, not delivered), less R454. At 58 these are exactly quadtree's 12 raw-family subjects decided
`box`, all reverted; each is a compile-gate revert (final-reverts attribution verify-reverted or its
closure:partition), so its cause is generator (R770-1; relay 138: 'a compile-check revert is a generator loss, as
the cascades are'). Read-only on the census and r133c; writes only out/rq5-rows-58-d6.tsv.
"""
import collections, csv, glob, os, re, sys
csv.field_size_limit(10 ** 9)
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
C = 'scratch/main/batch58'
R = 'scratch/analysis-fanout/r133c'
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
DELIV = 'realized-as-predicted'
R454F = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'
R454 = {(r['program'], r['owner'], r['binding']) for r in csv.DictReader(open(R454F), delimiter='\t')
        if r['counts_toward_N'] == 'true'}
assert len(R454) == 36

rows = list(csv.DictReader(open(f'{R}/rq5-rows-58.tsv'), delimiter='\t'))
cols = list(rows[0].keys())
vdiff = list(csv.DictReader(open(f'{R}/verify/indep/diff-vs-r133c.tsv'), delimiter='\t'))
assert len(rows) == 1627 and len(vdiff) == 7
over = {(d['program'], d['subject_key']): d['verifier'] for d in vdiff}
n = 0
for r in rows:
    k = (r['program'], r['subject_key'])
    if k in over:
        assert r['cause'] == 'side-condition', k
        r['cause'] = over[k]
        r['evidence'] = r['evidence'] + ' [verifier correction: ' + over[k] + ' (r133c/verify/indep/diff-vs-r133c.tsv)]'
        n += 1
assert n == 7
have = {(r['program'], r['subject_key']) for r in rows}

new = []
for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    sj = {r['subject_key']: r for r in csv.DictReader(open(f.replace('subject-outcomes', 'subjects')), delimiter='\t')}
    fr = list(csv.DictReader(open(f.replace('subject-outcomes', 'final-reverts')), delimiter='\t'))
    for o in csv.DictReader(open(f), delimiter='\t'):
        k = o['subject_key']
        s = sj[k]
        d = o['delivery'] == DELIV
        old_rule = o['family'] in SAFE or d
        if old_rule or s['decision'] not in SAFE:
            continue
        key = re.sub(r'#\d+$', '', k)
        owner, _, b = key.rpartition('::')
        if (p, owner, b) in R454:
            continue
        assert (p, k) not in have, k
        # final-reverts: the class row naming this subject, and the class row of its owner function
        named = [x for x in fr if k in x['named_subject'].split()]
        byfn = [x for x in fr if x['identity'] == o['owner_fn']]
        att = sorted({x['attribution'] for x in named + byfn})
        cls = sorted({x['class_id'] for x in named + byfn})
        assert o['delivery'] == 'reverted' and att and all(a in ('verify-reverted', 'closure:partition') for a in att), (k, att)
        sub = 'verify-reverted' if 'verify-reverted' in att else 'closure:partition'
        r = {c: '-' for c in cols}
        r.update(program=p, subject_key=k, family=o['family'], delivery=o['delivery'], kind='new (D6)',
                 label='verify-reverted' if sub == 'verify-reverted' else 'closure:partition',
                 reason_detail=s['reason_detail'], exclusion=o['exclusion'], b56_label='-', b56_cause='-',
                 cause='generator', sub=sub,
                 evidence=(f'D6 (relay 138): census decision {s["decision"]} (family {o["family"]}, model_kind '
                           f'{s["model_kind"]}), realized box at 56, reverted at 58 by the compile gate '
                           f'(final-reverts {",".join(cls)}: {",".join(att)}; class#103 quadtree_insert verify-reverted, '
                           f'7 x E0308); a compile-check revert is a generator loss (R770-1)'),
                 readingA='generator', readingB='generator', readingC='generator', main_map='generator')
        new.append(r)
assert len(new) == 12, len(new)
assert {r['program'] for r in new} == {'quadtree'}
out = rows + new
cause = collections.Counter(r['cause'] for r in out)
with open(f'{HERE}/out/rq5-rows-58-d6.tsv', 'w') as w:
    w.write('\t'.join(cols) + '\n')
    for r in out:
        w.write('\t'.join(str(r[c]).replace('\t', ' ') for c in cols) + '\n')
print('rows', len(out), dict(sorted(cause.items())))
print('new (D6):', ', '.join(f'{r["subject_key"]} [{r["sub"]}]' for r in new))
