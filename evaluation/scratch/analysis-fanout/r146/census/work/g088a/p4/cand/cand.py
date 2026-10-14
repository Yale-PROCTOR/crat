#!/usr/bin/env python3
"""cand.py CENSUS QFACTS.tsv FORMS_DUMP.tsv [--slots SLOTS_PER_PROGRAM_LOG]
rq1.strata.slice.cand / rq1.strata.cursor.cand (tab:rq1-strata: 'non-owning array-use candidates',
'candidates with possibly negative offset') from the model's own d0 QualifierFacts (streamed by qfacts_stream.py).

Candidate scope = strata.py's (r108 g3) candidate population: census subjects of form `owner::name#local`, family not
`unmodeled`, not an R454 binding (counts_toward_N), not a universe-exclusion row; the subject's d0 slot is
`owner::_local@d0` (the slot naming strata.py and rq5_forms use).
  array-like  = QualifierFacts fatness present:array-like at d0
  neg-or-unk  = QualifierFacts sign present:neg-or-unknown at d0 (two-way export: neg and unknown share the bit)
Variants are printed; FORMS_DUMP gives each decided-safe subject's RQ5 form (rq5_forms_ef.py), so containment
(decided subset of cand) is checked per variant. READ ONLY."""
import collections, csv, glob, os, re, sys
csv.field_size_limit(1 << 30)
C, QF, FD = sys.argv[1:4]
R454 = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'
ALLOC_REASON = None
def tsv(p):
    with open(p, newline='') as f:
        return list(csv.DictReader(f, delimiter='\t', quoting=csv.QUOTE_NONE))
excl = {(r['program'], r['owner'], r['binding']) for r in tsv(R454) if r['counts_toward_N'] == 'true'}
qf = {}
for r in tsv(QF):
    qf[(r['program'], r['slot'])] = r
form = {(r['program'], r['subject_key']): (r['form'], r['delivery']) for r in tsv(FD)}
n = collections.Counter(); per = collections.defaultdict(collections.Counter); ex = collections.defaultdict(list)
for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    subj = {r['subject_key']: r for r in tsv(f'{C}/{p}.raw-boundary-subjects.tsv')}
    for o in tsv(f):
        k = o['subject_key']; s = subj.get(k, {}); fam = s.get('family', o['family'])
        m = re.match(r'(.*)::([^:#]+)#(\d+)$', k)
        if not m:
            continue
        owner, name, loc = m.groups()
        if fam == 'unmodeled' or (p, o['owner_fn'], name) in excl or o['exclusion'].startswith('universe-exclusion'):
            continue
        n['scope'] += 1
        q = qf.get((p, f'{owner}::_{loc}@d0'))
        if q is None:
            n['scope.no-fact'] += 1; ex['no-fact'].append((p, k))
            fm0 = form.get((p, k), (None,))[0]
            if fm0 == 'slice': n['slice.cand.union'] += 1; n['slice.decided'] += 1; n['slice.decided.no-fact'] += 1
            if fm0 == 'cursor': n['cursor.cand.union'] += 1; n['cursor.decided'] += 1; n['cursor.decided.no-fact'] += 1
            continue
        arr = q['fatness_state'] == 'present' and q['fatness_value'] == 'array-like'
        neg = q['sign_state'] == 'present' and q['sign_value'] == 'neg-or-unknown'
        if q['sign_state'] != 'present':
            n['scope.sign-missing:' + q['sign_value']] += 1
        if q['fatness_state'] != 'present':
            n['scope.fat-missing:' + q['fatness_value']] += 1
        fm, dl = form.get((p, k), (None, o['delivery']))
        mk = s.get('model_kind', '-')
        owning = mk == 'owning' or fm in ('box', 'boxslice')
        n['scope.form.' + str(fm)] += 1
        if arr:
            n['arr'] += 1; per[p]['arr'] += 1
            n['arr.model_kind.' + mk] += 1
            n['arr.form.' + str(fm)] += 1
            if not owning:
                n['slice.cand'] += 1; per[p]['slice.cand'] += 1
        if neg:
            n['neg'] += 1; per[p]['neg'] += 1
            n['neg.form.' + str(fm)] += 1
            n['neg.arr' if arr else 'neg.not-arr'] += 1
            if not owning:
                n['cursor.cand'] += 1; per[p]['cursor.cand'] += 1
        if (arr and not owning) or fm == 'slice':
            n['slice.cand.union'] += 1; per[p]['slice.cand.union'] += 1
        if (neg and not owning) or fm == 'cursor':
            n['cursor.cand.union'] += 1; per[p]['cursor.cand.union'] += 1
        if arr and owning: n['arr.owning-excluded'] += 1
        if neg and owning: n['neg.owning-excluded'] += 1
        # containment
        if fm == 'slice':
            n['slice.decided'] += 1
            if not arr: n['slice.decided.not-arr'] += 1; ex['slice.decided.not-arr'].append((p, k, s.get('family'), mk))
        if fm == 'cursor':
            n['cursor.decided'] += 1
            if not neg: n['cursor.decided.not-neg'] += 1; ex['cursor.decided.not-neg'].append((p, k, q['sign_value'], q['fatness_value']))
            if not arr: n['cursor.decided.not-arr'] += 1
for k in sorted(n): print(k, n[k], sep='\t')
print('# per program', {p: dict(v) for p, v in sorted(per.items())})
for k, v in ex.items():
    print(f'# {k} ({len(v)})')
    for x in v[:40]: print('#   ', *x)
