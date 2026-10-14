#!/usr/bin/env python3
"""ownpref141.py <FRAME>: analysis.owners-by-preference and its delivered overlap (r110/p5 ownpref_diff.py's definition;
r140 ownpref_overlap_58pp.py's overlap). Owners by preference = slots Owning in the terms-on cache (L01^14,
era5c-l01p14-restored-solve) and not Owning in the frame's cache (58pp: L01^14u; s39: the S39 row). Kinds from
cache/heads/models.tsv (bounded head reads of the three caches); classes and behind-delivered from the frame's keymap141
reverse-index. Fails closed via SystemExit."""
import collections, csv, sys
F = sys.argv[1]
if F not in ('s39', '60sp'):  # r146
    raise SystemExit('FRAME')
H = 'scratch/analysis-fanout/r146/census/cache/heads/models.tsv'
RI = f'scratch/analysis-fanout/r146/census/work/g088b/keymap141/{F}/reverse-index.tsv'
col = {'s39': 'kinds39', '60sp': 'kind60sp'}[F]  # r146
ri = {(r['program'], r['slot_key']): r for r in csv.DictReader(open(RI), delimiter='\t')}
rows = list(csv.DictReader(open(H), delimiter='\t'))
moved = [r for r in rows if r['kind14'] == 'owning' and r[col] != 'owning']
gained = [r for r in rows if r['kind14'] != 'owning' and r[col] == 'owning']
cls = collections.Counter((r[col], ri[(r['program'], r['slot'])]['slot_kind_class'] if (r['program'], r['slot']) in ri else 'unjoined') for r in moved)
behind = [(r['program'], r['slot']) for r in moved if ri.get((r['program'], r['slot']), {}).get('behind_delivered') == '1']
print(f'frame {F} ({col}): owning at L01^14 = {sum(r["kind14"] == "owning" for r in rows)}, owning at the frame = {sum(r[col] == "owning" for r in rows)}')
print(f'owners by preference (owning at L01^14, not at the frame): {len(moved)}; gained (owning only at the frame): {len(gained)}')
print('  by (frame kind, slot class):', dict(sorted(cls.items())))
print('  by program:', dict(sorted(collections.Counter(r['program'] for r in moved).items())))
print(f'  behind a delivered declaration at the frame\'s census (keymap141/{F} reverse-index behind_delivered=1): {len(behind)} {behind[:10]}')
if F == 's39':
    u = {(r['program'], r['slot']) for r in rows if r['kind14'] == 'owning' and r['kind14u'] != 'owning'}
    s = {(r['program'], r['slot']) for r in moved}
    print(f'  against the L01^14u set ({len(u)}): same slots {len(u & s)}, only L01^14u {len(u - s)}, only S39 {len(s - u)}')
    kd = collections.Counter((r['kind14u'], r['kinds39']) for r in rows if (r['program'], r['slot']) in (u & s) and r['kind14u'] != r['kinds39'])
    print('  of the shared slots, kind moved L01^14u -> S39:', dict(kd))
    o14u = {(r['program'], r['slot']) for r in rows if r['kind14u'] == 'owning'}
    os39 = {(r['program'], r['slot']) for r in rows if r['kinds39'] == 'owning'}
    print(f'  Owning slots L01^14u {len(o14u)}, S39 {len(os39)}, equal sets: {o14u == os39}')
if F == '60sp':  # r146: against the S39 set (58''')
    u = {(r['program'], r['slot']) for r in rows if r['kind14'] == 'owning' and r['kinds39'] != 'owning'}
    s = {(r['program'], r['slot']) for r in moved}
    print(f'  against the S39 set ({len(u)}): same slots {len(u & s)}, only S39 {len(u - s)}, only 60sp {len(s - u)}')
    kd = collections.Counter((r['kinds39'], r['kind60sp']) for r in rows if (r['program'], r['slot']) in (u | s) and r['kinds39'] != r['kind60sp'])
    print('  of the union, kind moved S39 -> 60sp:', dict(kd))
    os39 = {(r['program'], r['slot']) for r in rows if r['kinds39'] == 'owning'}
    o60 = {(r['program'], r['slot']) for r in rows if r['kind60sp'] == 'owning'}
    print(f'  Owning slots S39 {len(os39)}, 60sp {len(o60)}, S39 subset of 60sp: {os39 <= o60}')
with open(f'scratch/analysis-fanout/r146/census/work/n141/ownpref-moved-{F}.tsv', 'w') as w:
    w.write('program\tslot\tkind14\tkind_frame\tslot_kind_class\tbehind_delivered\n')
    for r in moved:
        x = ri.get((r['program'], r['slot']), {})
        w.write(f"{r['program']}\t{r['slot']}\t{r['kind14']}\t{r[col]}\t{x.get('slot_kind_class', 'unjoined')}\t{x.get('behind_delivered', '?')}\n")
