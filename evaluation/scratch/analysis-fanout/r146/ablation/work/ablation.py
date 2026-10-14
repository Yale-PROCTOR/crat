#!/usr/bin/env python3
"""ablation.py <base census> <new census>: the 224 section-0 sentences, measured from the delivered-kinds slot tables
(model_kind, delivered_kind, cause by (program, subject_key)) and, for the brotli overlap loss, the subject-outcomes
identity join (census_by_identity's key and reason) plus the final-reverts attribution of each reverted row's function."""
import csv, glob, os, re, sys, collections, json
csv.field_size_limit(10**9)
D = 'realized-as-predicted'
def slots(d):
    out = {}
    for f in glob.glob(d + '/*.raw-boundary-delivered-kinds.tsv'):
        for r in csv.DictReader(open(f), delimiter='\t'):
            k = (r['program'], r['subject_key'])
            if k in out: raise SystemExit(f'duplicate slot {k} in {d}')
            out[k] = r
    if not out: raise SystemExit(f'no slot tables in {d}')
    return out
def tab(d, p, t):
    f = f'{d}/{p}.raw-boundary-{t}.tsv'
    return list(csv.DictReader(open(f), delimiter='\t')) if os.path.exists(f) else []
key = lambda k: re.sub(r'#\d+$', '', k)
A, B = sys.argv[1], sys.argv[2]
a, b = slots(A), slots(B)
if set(a) != set(b): raise SystemExit('slot universes differ')
res = collections.OrderedDict(); split = collections.defaultdict(collections.Counter); names = collections.defaultdict(list)
def add(name, p, k=None):
    split[name][p] += 1
    if k: names[name].append(f'{p} {k}')
for k in sorted(a):
    p = k[0]; ra, rb = a[k], b[k]
    ma, mb = ra['model_kind'], rb['model_kind']
    if ma == 'raw' and mb == 'owning':
        add('raw-to-owning', p, k[1]); add('raw-to-owning.depth' + rb['depth'], p)
        dk, c = rb['delivered_kind'], rb['cause']
        if dk == 'owning': add('raw-to-owning.box', p, k[1])
        elif dk == 'ref': add('raw-to-owning.ref', p)
        else:
            add('raw-to-owning.undelivered', p); add('raw-to-owning.undelivered.' + c, p, k[1] if c != 'degraded' else None)
    if ma == 'ref' and mb == 'owning':
        add('ref-to-owning', p, k[1]); add('ref-to-owning.delivered-' + rb['delivered_kind'], p, k[1])
    if ma != mb and 'ref' in (ma, mb):
        add('ref-moves', p)
        if (ma, mb) == ('ref', 'raw'): add('ref-to-raw', p, k[1])
        if (ma, mb) == ('raw', 'ref'): add('raw-to-ref', p, k[1])
        da, db = ra['delivered_kind'] == 'ref', rb['delivered_kind'] == 'ref'
        if not da and db: add('ref-moves.becomes-delivered-ref', p, k[1])
        if da and not db: add('ref-moves.leaves-delivered-ref', p, k[1] + ' -> ' + rb['delivered_kind'] + '/' + rb['cause'])
    if ma == 'ref': add('ref-slots.before', p)
    if mb == 'ref': add('ref-slots.after', p)
    if ra['delivered_kind'] == 'ref': add('delivered-ref.before', p)
    if rb['delivered_kind'] == 'ref': add('delivered-ref.after', p)
# the brotli loss by identity, every lost row labelled
lab = collections.Counter(); lostnames = []
p = 'brotli'
oa = {key(r['subject_key']): r for r in tab(A, p, 'subject-outcomes')}
ob = {key(r['subject_key']): r for r in tab(B, p, 'subject-outcomes')}
sb = {key(r['subject_key']): r for r in tab(B, p, 'subjects')}
fr = {}
for r in tab(B, p, 'final-reverts'):
    if r['kind'] == 'function': fr[r['identity']] = r['attribution']
for k in sorted(oa):
    if oa[k]['delivery'] != D: continue
    y = ob.get(k)
    if y and y['delivery'] == D: continue
    if y is None: lbl = 'absent'
    elif y['delivery'] == 'reverted':
        own = y['owner_fn']
        if own not in fr: raise SystemExit(f'reverted row without a function final-revert row: {k} owner {own}')
        lbl = 'fn-reverted:' + fr[own]
    else:
        lbl = y['exclusion'] if y['exclusion'] not in (None, '', '-') else (sb.get(k, {}).get('reason') or '-')
    lab[lbl] += 1; lostnames.append((k, lbl))
pair = lambda l: bool(re.search(r'pair-(not-shown-disjoint|proven-overlap|raw-view|pending|ref-beside)|overlap', l))
res_pair = [(k, l) for k, l in lostnames if pair(l)]
out = {'counts': {n: sum(c.values()) for n, c in split.items()}, 'split': {n: dict(sorted(c.items())) for n, c in split.items()},
       'names': names, 'brotli_lost_total': len(lostnames), 'brotli_lost_by_label': dict(lab.most_common()),
       'brotli_lost_pair_labelled': len(res_pair), 'brotli_lost_pair_rows': res_pair}
json.dump(out, open(sys.argv[3], 'w'), indent=1)
for n in sorted(out['counts']): print(f'{n}\t{out["counts"][n]}\t{out["split"][n]}')
print('brotli lost', len(lostnames), 'pair/overlap-labelled', len(res_pair))
for l, n in lab.most_common(): print(f'  {n}\t{l}')
