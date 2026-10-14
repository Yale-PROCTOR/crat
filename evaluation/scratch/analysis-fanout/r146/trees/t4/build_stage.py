#!/usr/bin/env python3
"""relay 116 S25a: stage.json for Table 4 (tab:rq1). Reads out-ours-14u (frozen), out-laertes-before, ctl-54p;
the record read-only. Every row `pending`."""
import csv, json, os, re, statistics, sys
TW = 'tmp/scratchpad/wt067'
sys.path.insert(0, TW + '/agents/tools/rq2')
import pos_census as P
NOR = TW + '/paper/numbers-of-record.md'
D = 'scratch/analysis-fanout/r146/trees/t4'
OUTSUB = os.environ['OUTSUB']
rec = {}
for l in open(NOR):
    m = re.match(r'^\| ([^ |]+) \|', l)
    if m:
        c = [x.strip() for x in l.strip().strip('|').split('|')]
        rec[c[0]] = c
pp = {r['program']: r for r in csv.DictReader(open(f'{D}/{OUTSUB}/per-program.tsv'), delimiter='\t')}
num = lambda r, c: int(r[c]) if r.get(c, '-') not in ('-', '') else None
pct = lambda a, b: f'{100.0 * a / b:.1f}%'
key = lambda p: p.replace('.', '')
seedpos = {}
for l in open(f'{D}/{OUTSUB}/seed_pos.out'):
    k, v, note = (l.rstrip('\n').split('\t') + [''])[:3]
    seedpos[k] = (v, note)

PRE = ('at the frame of record L01^14u (landed 2026-10-07, R869-1; borrow-ownership 897426dae): census main/frame14u; '
       'analysis-fanout 094 (relay 116), ')
RUN = ('the typed counter (docs agents/tools/rq2/pos_census.py at docs origin/main 07ec534, unchanged since 2c21123; build() '
       'replaced by the prebuilt binary r043/target/release/rq2_pos_counter sha256 5f9710a2..., rustc nightly-2025-06-23; '
       'r116/t4/run_nobuild.py run --side ours --census scratch/main/frame14u, then summarize) -> '
       'scratch/analysis-fanout/r116/t4/out-ours-14u/per-program.tsv; the input / CROWN / Laertes sides = the 031a '
       'outputs r043/out (frozen copies in out-ours-14u/{input,crown,laertes}; counter, rs-crown inputs and the artifact '
       'unchanged since 2026-10-02); values by seed_pos.py\'s rules (out-ours-14u/seed_pos.out); control: the same run on '
       '54\'s trees (main/b54p) reproduces r065/out byte for byte and the record\'s 171 seed_pos values 171/171; ')
UNITS = {}
stage = []

def add(k, v, note, layer=None, unit=None, prov_mid=RUN):
    old = rec.get(k)
    if old:
        layer = layer or old[3]; unit = unit or old[4]; was = old[1]
    else:
        was = '(new key)'
    stage.append(dict(key=k, value=v, status='pending', layer=layer, unit=unit,
                      provenance=PRE + prov_mid + note, was=was))

# (1) rq1 keys from seed_pos at frame14u
for p in P.PROGRAMS:
    for f in ('pos', 'uses'):
        for s in ('before', 'delivered', 'rate'):
            k = f'rq1.{key(p)}.{f}.{s}'
            v, note = seedpos[k]
            if s == 'rate':
                a = seedpos[f'rq1.{key(p)}.{f}.delivered'][0]; b = seedpos[f'rq1.{key(p)}.{f}.before'][0]
                note = f'{a}/{b}'
            if s == 'before':
                note += ' (input side; unchanged from 54\'s value, frame-independent)'
            if f == 'uses' and s != 'before':
                w = num(pp[p], 'ours.t2.full_roots_in_wrappers')
                if w:
                    note += f' (the remaining count includes {w} uses in the C-named wrappers)'
            add(k, v, note)
for f in ('pos', 'uses'):
    for s in ('before', 'delivered', 'rate'):
        k = f'rq1.total.{f}.{s}'
        v, note = seedpos[k]
        if s == 'rate':
            note = f"{seedpos[f'rq1.total.{f}.delivered'][0]}/{seedpos[f'rq1.total.{f}.before'][0]} over the twenty"
        add(k, v, note)
    k = f'rq1.median.{f}.rate'
    add(k, seedpos[k][0], seedpos[k][1])

# (2) per-program use rates of CROWN and Laertes (the whole-tree rule of record: (input T2 - tool T2) / input T2)
USE = ('rate of raw-pointer uses made safe = (input T2 - tool T2) / input T2, T2 = full_roots of the typed counter on the '
       'tool\'s emitted tree as the artifact distributes it (the rule of rq2.total.uses.*, seed_r065.py); ')
cr, lr = {}, {}
for p in P.PROGRAMS:
    r = pp[p]
    iu, cu, lu = num(r, 'input.t2.full_roots'), num(r, 'crown.t2.full_roots'), num(r, 'laertes.t2.full_roots')
    cr[p] = 100.0 * (iu - cu) / iu
    add(f'rq2.{key(p)}.uses.crown', pct(iu - cu, iu),
        f'({iu} - {cu})/{iu}; CROWN\'s tree benchmarks/rs-crown-transformed/{p} (the artifact\'s output; the same functions as the input, so the function-joined rule gives the same value)',
        layer='n/a', unit='count', prov_mid=RUN + USE)
B_TXT = "no Laertes output in the artifact (CROWN's Table 2: †)"
for p in P.PROGRAMS:
    r = pp[p]
    iu, lu = num(r, 'input.t2.full_roots'), num(r, 'laertes.t2.full_roots')
    if p == 'brotli':
        add('rq2.brotli.uses.laertes', B_TXT, 'R882-1 item 2: the artifact ships no Laertes tree for brotli (comparison/laertes-crown/after and laertes-path have none; README: Laertes crashes on brotli); Laertes is never run on our side (R858-3); the paper prints the dagger',
            layer='n/a', unit='count', prov_mid='')
        continue
    if p == 'libzahl':
        add('rq2.libzahl.uses.laertes', '4.6%',
            '(868 - 828)/868 on the 73 functions both trees define (exact path join, less src::): relay 117\'s adapted tree (R882-1 item 1: 29 llvm_asm! sites in 21 files -> asm!, r117/libzahl-laertes-adaptation.diff; counter run written to r043/out/laertes/libzahl at 13:23:44Z), reproduced here from its uses.tsv; '
            'NOT the whole-tree rule of the other eighteen: that rule gives (1015 - 2926)/1015 = -188.3 %, because the Laertes tree is libzahl with its asm paths and the header inlines in every module (454 functions vs the input\'s 108); 147 input uses in 35 functions have no counterpart; a definition question for the seat (094 notes Q1)',
            layer='n/a', unit='count', prov_mid=RUN)
        lr[p] = 4.6
        continue
    lr[p] = 100.0 * (iu - lu) / iu
    note = f'({iu} - {lu})/{iu}; Laertes tree ' + os.path.relpath(P.SR.laertes_root(p)[0], P.SR.ARTIFACT)
    shim = f'{D}/{OUTSUB}/laertes/{p}/shim.txt'
    if os.path.exists(shim):
        note += ' (' + open(shim).readline().strip() + ', a shim copy)'
    own = json.load(open(f'{D}/rows.json'))
    ob = [x['laertes_own_before'] for x in own if x['program'] == p][0]
    if ob is not None and pct(ob - lu, ob) != pct(iu - lu, iu):
        note += f'; on Laertes\'s own input tree (the artifact\'s before/, same translation): ({ob} - {lu})/{ob} = {pct(ob - lu, ob)} (094 notes Q1)'
    add(f'rq2.{key(p)}.uses.laertes', pct(iu - lu, iu), note, layer='n/a', unit='count', prov_mid=RUN + USE)
add('rq2.median.uses.crown', f'{statistics.median(cr.values()):.1f}%', 'median of the twenty rq2.<p>.uses.crown',
    layer='n/a', unit='count', prov_mid=RUN + USE)
l18 = [v for p, v in lr.items() if p != 'libzahl']
add('rq2.median.uses.laertes', f'{statistics.median(lr.values()):.1f}%',
    f'median of the nineteen printed rq2.<p>.uses.laertes (libzahl by its joined rate; brotli has no tree); over the eighteen without libzahl: {statistics.median(l18):.1f}%',
    layer='n/a', unit='count', prov_mid=RUN + USE)
progs = P.PROGRAMS
T = lambda c, ps: sum(num(pp[p], c) for p in ps)
ub, uc = T('input.t2.full_roots', progs), T('crown.t2.full_roots', progs)
add('rq2.total.uses.crown', pct(ub - uc, ub), f'({ub} - {uc})/{ub} over the twenty (recomputed; unchanged)', prov_mid=RUN + USE)
L18 = [p for p in progs if p not in ('brotli', 'libzahl')]
ub18, ul18 = T('input.t2.full_roots', L18), T('laertes.t2.full_roots', L18)
add('rq2.total.uses.laertes', pct(ub18 - ul18, ub18),
    f'({ub18} - {ul18})/{ub18} over the same eighteen programs as its provenance (recomputed; unchanged); libzahl outside this total (its whole-tree count is not comparable; with its joined 868/828 added: {pct(ub18 - ul18 + 40, ub18 + 868)} over nineteen; 094 notes Q1)',
    prov_mid=RUN + USE)

# (3) the empty position cells
add('rq2.brotli.pos.laertes', B_TXT, 'R882-1 item 2: the artifact ships no Laertes tree for brotli (comparison/laertes-crown/after and laertes-path have none; README: "the tool in [14] crashes on this benchmark"); Laertes never run on our side (R858-3)',
    prov_mid='')
d, b, un = (num(pp['libzahl'], f'laertes.pos.{c}') for c in ('delivered', 'before', 'unmatched'))
add('rq2.libzahl.pos.laertes', pct(d, b),
    f'{d}/{b} input raw layers non-raw in the Laertes output ({un} unmatched, counted not delivered), on relay 117\'s adapted tree (R882-1 item 1: feature-gate shim + 29 llvm_asm! sites -> asm!; adaptation adds no declaration), reproduced here by pos_census summarize over the frozen copy',
    prov_mid=RUN)
L19 = [p for p in progs if p != 'brotli']
add('rq2.total.pos.laertes', pct(T('laertes.pos.delivered', L19), T('laertes.pos.before', L19)),
    f"{T('laertes.pos.delivered', L19)}/{T('laertes.pos.before', L19)} over the nineteen programs with a Laertes tree (libzahl counted under R882-1; was 736/5215 over eighteen)", prov_mid=RUN)
add('rq2.median.pos.laertes', seedpos['rq2.median.pos.laertes'][0], seedpos['rq2.median.pos.laertes'][1] + ' (libzahl counted under R882-1; was over eighteen)', prov_mid=RUN)
# frame-dependent rows re-pointed (same derivations as their 54' provenance)
add('rq2.wins.pos', seedpos['rq2.wins.pos'][0], 'programs where our position rate is strictly the highest of the three (brotli against CROWN only; libzahl now against both); ties: none', prov_mid=RUN)
add('rq2.total.pos.as-emitted-rate', pct(T('ours.pos.delivered_no_twin', progs), T('input.t1.raw', progs)),
    f"{T('ours.pos.delivered_no_twin', progs)}/{T('input.t1.raw', progs)}: our position rate as emitted (the C-named wrapper's raw signature counted raw); the headline is the twin reading, rq1.total.pos.rate", prov_mid=RUN)

keys = [s['key'] for s in stage]
assert len(keys) == len(set(keys))
for s in stage:
    assert s['status'] in ('pending', 'measured', 'superseded') and s['layer'] and s['unit']
json.dump(stage, open(f'{D}/{OUTSUB}/stage.json', 'w'), indent=1, ensure_ascii=False)
moved = [s for s in stage if s['was'] != s['value']]
print(len(stage), 'rows;', len(moved), 'with a value different from the record')
for s in moved:
    print(f"  {s['key']}: {s['was']!r} -> {s['value']!r}")
