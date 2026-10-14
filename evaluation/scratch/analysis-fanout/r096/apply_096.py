#!/usr/bin/env python3
"""relay 096 (R852-1): seed the L01^14 frame's keys as of record from relay 095's verified staging, plus three new keys."""
import json, re, sys
NR = sys.argv[1]
ART = 'agents/artifacts/2026-10-06-analysis-fanout-069/'
S = 'scratch/analysis-fanout/r095/stage/'
DATE = '2026-10-06, R852-1 (USER, addendum 852; borrow-ownership 2b196a2ed -> 4a47f16f7)'
def fix(p):
    p = p.replace('<DATE>', DATE).replace(S, ART + 'stage/')
    p = p.replace('docs/', '').replace('dev/', '')
    return p.replace('|', '/').replace('\n', ' ')
rows = {}
for part in ['rq5', 'rq1', 'rq4']:
    for r in json.load(open(S + part + '/stage.verified.json')):
        assert r['key'] not in rows, r['key']
        rows[r['key']] = r
F = ('at the frame of record L01^14 (landed ' + DATE + '): census main/frame14 (code 4a47f16f7, analysis frame era5c-l01p14-v1; '
     'ended 2026-10-06 07:23Z, data=true, delivery=clean); analysis-fanout 069 (relays 095 / 096). ')
new = {
 'rq1.frame14.delivered-box': ('183', 'delivered', 'count', F + 'Box-family subjects delivered: Box 78 (rq5.form.box.delivered) + boxed slices 105 (rq5.form.boxslice.delivered: opt-box-slice 92 + box-slice 13), from the census subject-outcomes emitted_form column; main 179b and the landing record print the same 183. Replaces the superseded layer2.delivered-box for this frame.'),
 'analysis.copy-lend.locals.listed': ('48', 'decided', 'count', F + 'The locals of the 24 copy-lend pairs era-5c 144 section 3 lists (24 pairs x 2 locals; brotli 20 pairs, binn 3, heman 1); read with analysis.copy-lend.swaps (24 pairs, model slots).'),
 'analysis.copy-lend.locals.moved-at-census': ('44', 'decided', 'count', F + 'Of the 48 listed locals, those the frame census sees move as listed between 55 (main/b55) and the frame (one ref->raw, the other raw->ref): 44 = 22 pairs whole (brotli 20, binn 1, heman 1); 0 moves off the list. The other four (binn binn_is_valid #12, #16, #20, #21) have no census subject row, so the census neither confirms nor contradicts them. main 179b: 44 / 48, 0 off-list.'),
 'rq5.undelivered-licensed': ('596', 'decided', 'count', F + 'Licensed but not delivered: rq5.licensed 3,957 - delivered 3,361 = 596 on the row-level audit of record (R777-2; the definition of rq5.licensed). Under main\'s per-label cause mapping (rq5_columns.py labels, side-condition 290) licensed is 3,985 and this count 624 (the relay\'s figure); the 28 rows between are rows the row-level audit reads as side-condition (319 -> 318 after one row, brotli ReadHuffmanCode::s#5, read as undefined) where the label reads otherwise. The split by root cause is the rq5.cause.* keys.'),
}
lines = open(NR).read().split('\n')
idx = {}
for i, l in enumerate(lines):
    m = re.match(r'^\| ([A-Za-z][A-Za-z0-9._-]*) \|', l)
    if m: idx[m.group(1)] = i
done = []
for k, r in rows.items():
    assert k in idx, ('staged key not in file', k)
    cells = [c.strip() for c in lines[idx[k]].split(' | ')]
    old_status = lines[idx[k]].split('|')[3].strip()
    v = str(r['value']); assert '|' not in v
    status = 'pending' if old_status != 'superseded' else 'superseded'
    assert status == 'pending', (k, old_status)
    lines[idx[k]] = f"| {k} | {v} | pending | {r['layer']} | {r['unit'].replace('|','/')} | {fix(r['provenance'])} |"
    done.append((k, r.get('was', ''), v))
for k, (v, l, u, p) in new.items():
    assert k not in idx, k
    lines.insert(len(lines) - (1 if lines[-1] == '' else 0), f'| {k} | {v} | pending | {l} | {u} | {p} |')
    done.append((k, '(new)', v))
open(NR, 'w').write('\n'.join(lines).rstrip('\n') + '\n')
for k, w, v in sorted(done): print(f'{k}\t{w!s:.40}\t{v}')
print(len(done), 'rows')
