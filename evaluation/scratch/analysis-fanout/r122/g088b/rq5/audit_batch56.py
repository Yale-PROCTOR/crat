#!/usr/bin/env python3
"""relay 122 g088b: RQ5's row-level cause (R777-2) at batch 56 (main/batch56, dc5b7d53c, frame14u's cache).
Base = the L01^14u row-level file of record (r110/p2-rq5/rows-final.tsv, 088). Same standard as 088's audit_frame14u.py:
a batch56 row whose (program, subject_key, label, family) equals frame14u's keeps frame14u's cause; a new / relabelled /
family-changed row is audited below. Writes rows-final-b56.tsv, audit-b56.tsv, left-b56.tsv, totals-b56.tsv."""
import csv, collections, sys
csv.field_size_limit(10**9)
R = 'scratch/analysis-fanout/r110/p2-rq5'
C = 'scratch/main/batch56'
D = 'scratch/analysis-fanout/r122/g088b/rq5'
rd = lambda f: list(csv.DictReader(open(f), delimiter='\t'))
key = lambda r: (r['program'], r['subject_key'])
old = {key(r): r for r in rd(f'{R}/rows-final.tsv')}
oldm = {key(r): r for r in rd(f'{R}/rows-frame14u-main.tsv')}
newm = {key(r): r for r in rd(f'{D}/rows-batch56-main.tsv')}
rows = rd(f'{D}/map56/rows.tsv')
A = {}
UD = 'undefined'
# the one new row: R857-2's backstop (released_indirect.rs) holds it; a reference to it is deallocated through
# (*m).free_func -> BrotliDefaultFreeFunc while its protector is live (UB under TB and SB; released_indirect.rs module doc,
# fan-out 074 Miri repro). R770-1: a subject freed through it is `undefined` (rq5_columns MECHANICAL: freed-slot -> undefined).
A[('brotli', 'src::enc::encode::BrotliEncoderDestroyInstance::state#1')] = (UD, 'released-through-indirect-call (a freed-slot through a function pointer)',
  'batch56 brotli.raw-boundary-subjects.tsv:1697 reason held:released-through-indirect-call, detail via=BrotliEncoderDestroyInstance:bb5:arg1->'
  'src::common::platform::BrotliDefaultFreeFunc; frame14u delivered it (optional, subject-outcomes:1697); the reference would be freed while '
  'protected (released_indirect.rs doc; fan-out 074): the freed-slot rule of R770-1 -> undefined. Label-level mapping (035) reads generator.')
out, audited = [], []
for r in rows:
    k = key(r); o = old.get(k)
    if o and o['label'] == r['label'] and oldm[k]['family'] == newm[k]['family']:
        out.append([r['program'], r['subject_key'], r['group'], r['label'], o['cause'], o['sub'], o['evidence']]); continue
    kind = 'new' if not o else ('relabelled' if o['label'] != r['label'] else 'family-changed')
    c, s, e = A[k]
    out.append([r['program'], r['subject_key'], r['group'], r['label'], c, s, e])
    audited.append([kind, r['program'], r['subject_key'], newm[k]['family'], r['label'], o['label'] if o else '-', o['cause'] if o else '-', r['cause'], c, s, e])
assert len(out) == 907, len(out)
here = {key(r) for r in rows}
def tab(p, t):
    return {r['subject_key']: r for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-{t}.tsv'), delimiter='\t')}
left = []
for k in sorted(old):
    if k in here: continue
    sj, so = tab(k[0], 'subjects')[k[1]], tab(k[0], 'subject-outcomes')[k[1]]
    state = 'delivered (' + so['emitted_form'] + ')' if so['delivery'] == 'realized-as-predicted' else f"model-{sj['model_kind']} (family {sj['family']}, reason {sj['reason']})"
    left.append([k[0], k[1], old[k]['label'], old[k]['cause'], state])
CAUSES = ['held', 'no-safe-form', 'undefined', 'type-system', 'side-condition', 'form-fact', 'generator']
w = csv.writer(open(f'{D}/rows-final-b56.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program', 'subject_key', 'group', 'label', 'cause', 'sub', 'evidence']); w.writerows(out)
w = csv.writer(open(f'{D}/audit-b56.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['kind', 'program', 'subject_key', 'family', 'label', 'f14u_label', 'f14u_cause', 'label_default', 'cause', 'sub', 'evidence']); w.writerows(sorted(audited))
w = csv.writer(open(f'{D}/left-b56.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program', 'subject_key', 'f14u_label', 'f14u_cause', 'b56_state']); w.writerows(left)
per = collections.defaultdict(collections.Counter); tot = collections.Counter()
for x in out: per[x[0]][x[4]] += 1; tot[x[4]] += 1
w = csv.writer(open(f'{D}/totals-b56.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program'] + CAUSES + ['total'])
for p in sorted(per): w.writerow([p] + [per[p][c] for c in CAUSES] + [sum(per[p].values())])
w.writerow(['total'] + [tot[c] for c in CAUSES] + [sum(tot.values())])
o = collections.Counter(r['cause'] for r in old.values())
print('cause\tframe14u\tbatch56'); [print(f'{c}\t{o[c]}\t{tot[c]}') for c in CAUSES]
print('audited', [(x[0], x[2], x[8]) for x in audited]); print('left', left)
