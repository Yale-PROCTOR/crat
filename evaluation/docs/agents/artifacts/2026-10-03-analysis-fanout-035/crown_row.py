#!/usr/bin/env python3
"""analysis-fanout 035 (relay 050, R770-3): CROWN's realization row reproduced with this lane's tools.
Denominator: CROWN's analysis labels (rs-crown-transformed/<prog>/analysis_results/ownership.json fn_data, depth 0).
Numerator: the typed counter's reading of CROWN's emitted program (031's r043/out/crown/<prog>/positions.tsv; param/local,
depth 0, layer 0; all bindings of the name must carry the form)."""
import csv, json, sys
from collections import Counter, defaultdict
sys.path.insert(0, 'docs/agents/tools'); import seed_numbers as SN
B = 'crat/benchmarks/rs-crown-transformed'
O = 'scratch/analysis-fanout/r043/out/crown'
csv.field_size_limit(10**9)
tot = Counter(); per = defaultdict(Counter); forms = Counter(); unmatched = []
SAFE_BOX = {'box', 'opt-box', 'box-slice', 'opt-box-slice'}
SAFE_REF = {'ref', 'mut-ref', 'opt-ref', 'opt-mut-ref', 'slice-ref', 'slice-mut', 'opt-slice-ref', 'opt-slice-mut', 'str-ref', 'opt-str-ref'}
for p in SN.PROGRAMS:
    a = f'{B}/{p}/analysis_results'
    own = json.load(open(f'{a}/ownership.json'))['fn_data']
    mut = json.load(open(f'{a}/mutability.json'))['fn_data']
    fat = json.load(open(f'{a}/fatness.json'))['fn_data']
    pos = defaultdict(list)
    for r in csv.DictReader(open(f'{O}/{p}/positions.tsv'), delimiter='\t'):
        if r['kind'] in ('param', 'local') and r['depth'] == '0' and r['layer'] == '0':
            pos[f"{r['owner']}::{r['name']}"].append(r['form'])
    for fn, vs in own.items():
        for v, labels in vs.items():
            if not labels:
                continue
            k = f'{fn}::{v}'
            tot['declarations'] += 1
            if labels[0] != 'Owning':
                continue
            tot['owning'] += 1; per[p]['owning'] += 1
            m = (mut.get(fn, {}).get(v) or ['?'])[0]; f = (fat.get(fn, {}).get(v) or ['?'])[0]
            fs = pos.get(k)
            if not fs:
                cls = 'unmatched'; unmatched.append(k)
            elif all(x in SAFE_BOX for x in fs):
                cls = 'box'
            elif all(x in SAFE_REF | SAFE_BOX for x in fs):
                cls = 'reference'
            else:
                cls = 'raw:' + ('array' if f == 'Arr' else ('thin-mut' if m == 'Mut' else 'thin-imm'))
            tot[cls] += 1; per[p][cls] += 1
            forms[tuple(sorted(set(fs or ['-'])))] += 1
print('declarations (fn_data, depth 0, labelled):', tot['declarations'])
print('Owning:', tot['owning'])
print({k: v for k, v in tot.items() if k not in ('declarations', 'owning')})
d = tot['box'] + tot['reference']
print(f"delivered safe: {d} = box {tot['box']} + reference {tot['reference']} -> {100.0 * d / tot['owning']:.1f} %")
print('raw by program (thin-mut):', {p: c['raw:thin-mut'] for p, c in per.items() if c['raw:thin-mut']})
print('forms:', forms.most_common(12))
print('unmatched:', unmatched[:10])
