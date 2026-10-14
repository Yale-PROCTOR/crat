#!/usr/bin/env python3
"""r141 conf: ec1.compiler-only variants at a census (beside the record's class-aware join ec1_ident.py):
 fnkey = reverted subjects with model kind ref/owning whose owner_fn itself carries a compiler diagnostic;
 d6    = the class-aware join with D6 (census decision a safe form) in place of the model kind.
usage: ec1_variants.py <census-batch-name>... ; fails closed (raise SystemExit)."""
import csv, glob, os, sys
csv.field_size_limit(10**9)
M = 'scratch/main/'
SAFE = lambda d: d not in ('raw', 'degraded', 'unmodeled', '-', '') and not d.startswith('raw')
for b in sys.argv[1:]:
    fk = set(); d6 = set(); decs = set()
    fs = sorted(glob.glob(M + b + '/*.raw-boundary-subject-outcomes.tsv'))
    if len(fs) != 20:
        raise SystemExit(f'{b}: {len(fs)} outcome tables')
    for f in fs:
        p = os.path.basename(f).split('.raw-boundary')[0]
        diagf = set(r['function'] for r in csv.DictReader(open(f'{M}{b}/{p}.raw-boundary-compiler-diagnostics.tsv'), delimiter='\t'))
        fr = list(csv.DictReader(open(f'{M}{b}/{p}.raw-boundary-final-reverts.tsv'), delimiter='\t'))
        idx = {}
        for r in fr:
            v = list(r.values())[13:]
            idx.setdefault(v[3], set()).add(v[2])
        fns = set(diagf)
        for cl, mem in idx.items():
            if mem & diagf: fns |= mem
        subj = {r['subject_key']: r for r in csv.DictReader(open(f'{M}{b}/{p}.raw-boundary-subjects.tsv'), delimiter='\t')}
        for r in csv.DictReader(open(f), delimiter='\t'):
            if r['delivery'] != 'reverted': continue
            s = subj[r['subject_key']]; decs.add(s['decision'])
            if s['model_kind'] in ('ref', 'owning') and r['owner_fn'] in diagf: fk.add((p, r['subject_key']))
            if SAFE(s['decision']) and r['owner_fn'] in fns: d6.add((p, r['subject_key']))
    print(f'{b}\tfnkey={len(fk)}\td6={len(d6)}\tdecisions_of_reverted={sorted(decs)}')
    for p, k in sorted(d6 ^ fk): print(f'#  {b} d6-xor-fnkey {p} {k}')
