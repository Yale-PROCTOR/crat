#!/usr/bin/env python3
"""relay 118: stage.json from per-program.json (alldecl.py). The record is read only (to fill `was`)."""
import json, re, statistics
TW = 'tmp/scratchpad/wt067'
rec = {}
for l in open(TW + '/paper/numbers-of-record.md'):
    m = re.match(r'^\| ([^ |]+) \|', l)
    if m:
        rec[m.group(1)] = [x.strip() for x in l.strip().strip('|').split('|')][1]
D = json.load(open('per-program.json'))
PROGS = list(D)
K = lambda p: p.replace('.', '')
pct = lambda a, b: f'{100.0 * a / b:.1f}%'
NOLAERTES = "no Laertes output in the artifact (CROWN's Table 2: †)"
HEAD = ('at the frame of record L01^14u (landed 2026-10-07, R869-1; borrow-ownership 897426dae): census main/frame14u; '
        'analysis-fanout 095 (relay 118), ')
METHOD = ('Table 4\'s declaration population and rule (relay 118, the paper\'s rule: the outermost level): the PRE-BUILT '
          'typed counter rq2_pos_counter (rustc nightly-2025-06-23; no binary run for 095) T1 tables positions.tsv, '
          'aggregated by declaration (kind, owner, name, idx = pos_census.py\'s layer key less depth/layer; field = '
          'struct name, once per struct; byref bindings and statics excluded); population = every param / return / '
          'local (named or c2rust temporary) / field of the c2rust input (benchmarks/rs-crown) whose depth-0 pointer '
          'layer(s) outside a function-pointer signature include a raw layer (raw-*, opt-raw-*, nonnull, opt-nonnull); '
          'safe in an emitted program = the joined declaration\'s depth-0 pointer layer(s) (fn-pointer signatures '
          'excluded) are all &, &mut, slice / str references, Box, Box<[T]>, Option of these, or the cursor forms, '
          'whatever the inner levels; an absent declaration (no join: exact key, unique-last-segment fallback; ours = '
          'the twin reading) counts not made safe; inputs scratch/analysis-fanout/r065/out/{input,crown,laertes} '
          '(the 031a run), ours r116/t4/out-ours-14u/ours (frame14u emitted trees), Laertes libzahl r117/out (relay '
          '117\'s adapted tree, R882-1); scripts r118/stage/alldecl.py + build_stage.py; independent verifier '
          'r118/stage/verify.py (imports neither) 138/138 (before, safe, absent per program and side); ')
rows = []


def add(k, v, layer, unit, note):
    rows.append({'key': k, 'value': v, 'status': 'pending', 'layer': layer, 'unit': unit,
                 'provenance': HEAD + METHOD + note, 'was': rec.get(k, '')})


rates = {'ours': [], 'crown': [], 'laertes': []}
LAERTES = [p for p in PROGS if D[p]['laertes.status'] == 'ok']
for p in PROGS:
    r, k, b = D[p], K(p), D[p]['before']
    st = r['stats']
    s = r['ours.safe']
    add(f'rq1.{k}.alldecl.before', str(b), 'n/a', 'count',
        f'{b} input declarations ({", ".join(f"{n} {kk}" for kk, n in sorted(r["kinds"].items()))}); excluded: '
        f'{st.get("static.raw-any", 0)} static, {st.get("fnptr-only", 0)} fn-pointer-only, '
        f'{st.get("byref.raw-any", 0)} byref bindings over a raw place')
    add(f'rq1.{k}.alldecl.delivered', str(s), 'delivered', 'count',
        f'{s}/{b} safe at the outermost level in our emitted tree; {r["ours.absent"]} absent from it, counted not safe')
    add(f'rq1.{k}.alldecl.rate', pct(s, b), 'n/a', 'percent', f'{s}/{b}')
    rates['ours'].append(100.0 * s / b)
    for side in ('crown', 'laertes'):
        if r[f'{side}.status'] != 'ok':
            add(f'rq2.{k}.alldecl.{side}', NOLAERTES, 'n/a', 'percent',
                'R882-1 item 2: the artifact ships no Laertes tree for brotli; Laertes never run on our side (R858-3)')
            continue
        n = r[f'{side}.safe']
        who = ("CROWN's emitted program (benchmarks/rs-crown-transformed, as distributed)" if side == 'crown' else
               "the artifact's Laertes output" + {
                   'libzahl': ' (relay 117\'s adapted tree: feature-gate shim + 29 llvm_asm! sites, R882-1)',
                   'libcsv': ' (laertes-laertes, as distributed)',
                   **{q: ' (laertes-laertes, counted through the r043 feature-gate shim: const_raw_ptr_to_usize_cast, main removed)'
                      for q in ('bzip2', 'genann', 'lil', 'robotfindskitten', 'tulipindicators', 'urlparser')}}.get(
                   p, ' (laertes-crown, as distributed)'))
        tail = f'; {r[side + ".absent"]} absent from it, counted not safe' if r[side + '.absent'] else ''
        add(f'rq2.{k}.alldecl.{side}', pct(n, b), 'n/a', 'percent', f'{n}/{b} safe at the outermost level in {who}{tail}')
        rates[side].append(100.0 * n / b)

S = lambda f, ps=PROGS: sum(f(D[p]) for p in ps)
tb, ts, ta = S(lambda r: r['before']), S(lambda r: r['ours.safe']), S(lambda r: r['ours.absent'])
add('rq1.total.alldecl.before', str(tb), 'n/a', 'count', 'the twenty inputs')
add('rq1.total.alldecl.delivered', str(ts), 'delivered', 'count', f'{ts}/{tb} over the twenty ({ta} absent, counted not safe)')
add('rq1.total.alldecl.rate', pct(ts, tb), 'n/a', 'percent', f'{ts}/{tb} over the twenty (pooled)')
add('rq1.median.alldecl.rate', f'{statistics.median(rates["ours"]):.1f}%', 'n/a', 'percent',
    'median of the twenty per-program rates (every population non-empty)')
for side, ps, why in (('crown', PROGS, 'over the twenty'),
                      ('laertes', LAERTES, f'over the {len(LAERTES)} programs with a Laertes tree in the artifact '
                                           '(brotli: none; libzahl counted on relay 117\'s adapted tree, R882-1)')):
    b = S(lambda r: r['before'], ps)
    n = S(lambda r: r[side + '.safe'], ps)
    add(f'rq2.total.alldecl.{side}', pct(n, b), 'n/a', 'percent', f'{n}/{b} {why} (pooled)')
    add(f'rq2.median.alldecl.{side}', f'{statistics.median(rates[side]):.1f}%', 'n/a', 'percent', f'median {why}')
assert all(r['status'] == 'pending' for r in rows) and len({r['key'] for r in rows}) == len(rows)
json.dump(rows, open('stage.json', 'w'), indent=1, ensure_ascii=False)
print(len(rows), 'rows; already in the record:', [r['key'] for r in rows if r['key'] in rec])
alt = pct(ts + ta, tb)
print('alternative rq1.total.alldecl.rate (absent counted safe):', alt, f'({ts + ta}/{tb})')
for r in rows:
    if '.total.' in r['key'] or '.median.' in r['key']:
        print(r['key'], r['value'])
