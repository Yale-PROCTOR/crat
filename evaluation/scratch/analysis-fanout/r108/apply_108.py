#!/usr/bin/env python3
"""Relay 108 / analysis-fanout 086: seed the (a) dispositions of the 85 cited placeholder keys
at the frame of record L01^14, note (c)/(d) in the empty rows' provenance, and add the three
replacement keys for superseded layer2 rows (rule 5). Statuses stay pending.

Usage: apply_108.py <numbers-of-record.md> <r108-result.json>
"""
import json, re, sys

REC, RES = sys.argv[1], sys.argv[2]
d = json.load(open(RES))
K, C = d['keys'], d['checks']

FRAME = ('at the frame of record L01^14 (code 4a47f16f7, census scratch/main/frame14, '
         'solve era5c-l01p14-restored-solve): analysis-fanout 086 (relay 108), ')

def clean(s):
    s = s.replace('|', '/').replace('\n', ' ')
    return re.sub(r'\s+', ' ', s).strip()

seed = {}      # key -> (value, provenance)
note = {}      # key -> provenance note for (c)/(d)/(b) rows left empty

# (a) as returned and verified
for k, v in K.items():
    if v['disposition'] == 'a' and not k.startswith('layer2.'):
        prov = v['provenance']
        if v.get('note'):
            prov += ' NOTE: ' + v['note']
        corr = (C.get(k) or {}).get('correction') or ''
        if corr and corr.strip().lower() not in ('none', 'none.', ''):
            prov += ' VERIFIER: ' + corr
        seed[k] = (v['value'], FRAME + prov)

# verifier correction: conf.retire.matched is (a), not a rename
v = K['conf.retire.matched']
seed['conf.retire.matched'] = ('382', FRAME + 'docs agents/artifacts/2026-10-06-wave-6o-130a/c2.txt (C2 RetainedLifecycle '
    'at census main/frame14): sum of matched= over the 20 programs = 382 (emitted_release_sites 382, unmatched_source 0, '
    'extra_emitted 0). The same checker field as ec2.mapped (382, analysis-fanout 071); re-seeded with it.')

# same quantity as an existing key of record: seeded equal, re-seeded with it
for k, other in [('rq1.strata.owning.delivered', 'rq1.frame14.delivered-box'),
                 ('rq1.strata.slice.decided', 'rq5.form.slice.decided'),
                 ('rq1.strata.slice.delivered', 'rq5.form.slice.delivered'),
                 ('rq1.strata.cursor.decided', 'rq5.form.cursor.decided'),
                 ('rq1.strata.cursor.delivered', 'rq5.form.cursor.delivered')]:
    v = K[k]
    seed[k] = (v['value'], FRAME + f'the same set as {other} (= {v["value"]} at L01^14); re-seeded with it. '
               + v['provenance'] + ((' NOTE: ' + v['note']) if v.get('note') else ''))

# rq1.strata.fields.cand: state the strict reading
p = seed['rq1.strata.fields.cand']
seed['rq1.strata.fields.cand'] = (p[0], p[1] + ' (270 if libtree glob_t.gl_pathv, a POSIX <glob.h> struct, is read as a '
                                  'system struct; the 2026-09-05 name list keeps it as program-defined.)')

# (c)/(d) and the one (b) left empty: say why in the row
for k, v in K.items():
    if k in seed or k.startswith('layer2.'):
        continue
    dis = {'c': '(c) not measurable at this frame', 'd': '(d) drop from the manuscript', 'b': '(b) renamed'}[v['disposition']]
    note[k] = f'analysis-fanout 086 (relay 108) disposition {dis}: ' + v['provenance'] + \
              ((' NOTE: ' + v['note']) if v.get('note') else '')

# rule 5: replacements for superseded layer2 rows
NEW = [
    ('hold.io-domain', K['layer2.held-stream']['value'], 'delivered', 'count',
     FRAME + 'replaces the superseded layer2.held-stream (whose 38 was the census typed_excluded column, the R454 '
     'let-ref-mut bindings, not streams). ' + K['layer2.held-stream']['provenance']),
    ('delivery.not-placed', K['layer2.not-placed']['value'], 'delivered', 'count',
     FRAME + 'replaces the superseded layer2.not-placed (whose 0 was the census frame field reverted_program). '
     + K['layer2.not-placed']['provenance'] + ' hold.io-domain (62) is a subset of these 905.'),
    ('delivery.programs-degraded', K['layer2.programs-degraded']['value'], 'delivered', 'count',
     FRAME + 'replaces the superseded layer2.programs-degraded (same definition). ' + K['layer2.programs-degraded']['provenance']),
]
note['layer2.reverted'] = None  # superseded: untouched; the manuscript cites rq5.form.total.reverted (b)

lines = open(REC).read().split('\n')
out, done = [], set()
for l in lines:
    c = [x.strip() for x in l.strip().strip('|').split('|')] if l.startswith('|') else None
    key = c[0] if c else None
    if key in seed:
        assert c[2] == 'pending' and not c[1], (key, c[1:3])
        val, prov = seed[key]
        c[1], c[5] = clean(val), clean(prov)
        l = '| ' + ' | '.join(c[:6]) + ' |'
        done.add(key)
    elif key in note and note[key]:
        assert c[2] == 'pending' and not c[1], (key, c[1:3])
        old = c[5]
        c[5] = clean((old + ' ' if old else '') + note[key])
        l = '| ' + ' | '.join(c[:6]) + ' |'
        done.add(key)
    out.append(l)
    if key == 'layer2.reverted':
        for nk, nv, layer, kind, prov in NEW:
            out.append(f'| {nk} | {clean(nv)} | pending | {layer} | {kind} | {clean(prov)} |')
            done.add(nk)
missing = (set(seed) | {k for k, v in note.items() if v} | {n[0] for n in NEW}) - done
assert not missing, missing
open(REC, 'w').write('\n'.join(out))
print('seeded', len(seed), 'noted', sum(1 for v in note.values() if v), 'new', len(NEW))
for k in sorted(seed):
    print('  a', k, '=', seed[k][0][:60])
