#!/usr/bin/env python3
"""analysis-fanout 045 (relay 065): 034's RQ2 seeder re-pointed at the census of record 54′ (r065 outputs).
(1) rq1.<prog>.decl.{delivered,rate}, rq1.total.decl.{delivered,rate}, rq1.median.decl.rate := CROWN's declaration counter run
    unchanged on our trees, as emitted (030a: the walker, frame 13); rq2.total.decl.twin-rate := the twin reading (1,049);
    rq2.wins.decl recomputed on the as-emitted column (strictly above CROWN and Laertes; brotli's Laertes cell the published one).
(2) rq2.total.decl.laertes, rq2.total.pos.{crown,laertes,as-emitted-rate}, rq2.total.uses.{crown,laertes}.
All rows `pending`, provenance `provisional:` (values at frame 13; final at the last landing).
usage: seed_r048.py NOR [--write]"""
import csv, re, sys, statistics
NOR = sys.argv[1]; WRITE = '--write' in sys.argv
W = 'scratch/analysis-fanout/r065/decl/per-program.tsv'
P = 'scratch/analysis-fanout/r065/out/per-program.tsv'
Q = 'tmp/scratchpad/rq2-table.tsv'  # seed_rq2 (015)
key = lambda p: p.replace('.', '')
pct = lambda a, b: f'{100.0 * a / b:.1f}%'
w = {r['program']: r for r in csv.DictReader(open(W), delimiter='\t')}
pp = {r['program']: r for r in csv.DictReader(open(P), delimiter='\t')}
q = {r['program']: r for r in csv.DictReader(open(Q), delimiter='\t')}
progs = sorted(w)
seed = {}
PW = ('provisional: analysis-fanout 045 (relay 065, the census of record 54′): CROWN\'s declaration counter (crown_artifact_inventory, unchanged; '
      'decl_walker_vs_census.py, 030a) run on the trees of 54′ AS EMITTED (the C-named wrapper read as the function), batch 54′ landed 2b196a2ed (census head 5948d74f6, census main/b54p, analysis frame L01^13 '
      'era5c-l01p13-v1); ')
rates = {}
tb = td = 0
for p in progs:
    b = int(w[p]['before']); d = int(w[p]['walker_ref']) + int(w[p]['walker_box'])
    tb += b; td += d; rates[p] = 100.0 * d / b
    seed[f'rq1.{key(p)}.decl.delivered'] = (str(d), PW + f'{d}/{b}')
    seed[f'rq1.{key(p)}.decl.rate'] = (pct(d, b), PW + f'{d}/{b}')
seed['rq1.total.decl.delivered'] = (str(td), PW + f'{td}/{tb} over the twenty')
seed['rq1.total.decl.rate'] = (pct(td, tb), PW + f'{td}/{tb} over the twenty')
seed['rq1.median.decl.rate'] = (f'{statistics.median(rates.values()):.1f}%', PW + 'median of the twenty')
twin = sum(int(w[p]['twin_walker_safe']) for p in progs)
seed['rq2.total.decl.twin-rate'] = (pct(twin, tb), 'provisional: analysis-fanout 045 (54′, census b54p, frame L01^13): the same counter with each `__crat_safe_<f>` body read under its C '
                                    f'name (the twin reading; 030a): {twin}/{tb} at 54′ (equal slot for slot to the census\'s realized-as-predicted)')
# wins on the as-emitted column
wins, ties = 0, []
for p in progs:
    cr = float(q[p]['crown_rate']); la = float(q[p]['laertes_rate'])
    o = rates[p]
    if o > max(cr, la) + 1e-9: wins += 1
    elif abs(o - max(cr, la)) < 1e-9: ties.append(p)
seed['rq2.wins.decl'] = (str(wins), 'provisional: analysis-fanout 045 (54′, census b54p): programs where our as-emitted declaration rate (CROWN\'s counter, '
                         'unchanged) is strictly above both CROWN\'s and Laertes\'s (015; brotli\'s Laertes cell the published figure); '
                         f'ties: {", ".join(ties) or "none"}')
# Laertes declaration total (015's measurement; brotli the published 0.0 % under the dagger)
lb = sum(int(q[p]['laertes_universe']) for p in progs if q[p]['laertes_source'] == 'measured')
ls = sum(int(q[p]['laertes_universe']) - int(q[p]['laertes_after']) for p in progs if q[p]['laertes_source'] == 'measured')
seed['rq2.total.decl.laertes'] = (str(ls), f'provisional: analysis-fanout 034 (frame-independent: the Laertes outputs of the artifact): declarations Laertes makes safe, CROWN\'s counter unchanged on the '
                                  f'artifact\'s Laertes outputs (015), {ls}/{lb} = {pct(ls, lb)} over the 19 programs it ships (brotli: no '
                                  f'output, the dagger); a count, as its sibling rq2.total.decl.crown (703)')
# positions and uses (031a)
n = lambda r, c: int(r[c]) if r.get(c, '-') not in ('-', '') else None
T = lambda c, ps: sum(n(pp[p], c) for p in ps)
PP = 'provisional: analysis-fanout 045 (54′) from the typed counter (pos_census.py over r065/out: inputs, CROWN and Laertes as 031a; ours = census b54p, twin reading): '
L = [p for p in progs if n(pp[p], 'laertes.pos.delivered') is not None]
seed['rq2.total.pos.crown'] = (pct(T('crown.pos.delivered', progs), T('input.t1.raw', progs)),
                               PP + f"{T('crown.pos.delivered', progs)}/{T('input.t1.raw', progs)} input raw layers made safe in CROWN's outputs")
seed['rq2.total.pos.laertes'] = (pct(T('laertes.pos.delivered', L), T('laertes.pos.before', L)),
                                 PP + f"{T('laertes.pos.delivered', L)}/{T('laertes.pos.before', L)} over the {len(L)} programs Laertes ships "
                                 "and that compile (brotli, libzahl: the daggers)")
seed['rq2.total.pos.as-emitted-rate'] = (pct(T('ours.pos.delivered_no_twin', progs), T('input.t1.raw', progs)),
                                         PP + f"{T('ours.pos.delivered_no_twin', progs)}/{T('input.t1.raw', progs)}: our position rate as emitted "
                                         "(the C-named wrapper's raw signature counted raw); the headline is the twin reading, rq1.total.pos.rate")
ub, uc = T('input.t2.full_roots', progs), T('crown.t2.full_roots', progs)
seed['rq2.total.uses.crown'] = (pct(ub - uc, ub), PP + f'raw-pointer uses removed: ({ub} - {uc})/{ub} (T2 full_roots)')
ub18, ul = T('input.t2.full_roots', L), T('laertes.t2.full_roots', L)
seed['rq2.total.uses.laertes'] = (pct(ub18 - ul, ub18), PP + f'raw-pointer uses removed: ({ub18} - {ul})/{ub18} over the {len(L)} programs '
                                  f'(T2 full_roots; CROWN on the same {len(L)}: {pct(ub18 - T("crown.t2.full_roots", L), ub18)})')
for k, (v, note) in seed.items():
    print(k, v, note[-140:], sep='\t')
NEW = {'rq2.total.decl.twin-rate': ('rq2.total.decl.crown', 'percent'), 'rq2.total.decl.laertes': ('rq2.total.decl.crown', 'count'),
       'rq2.total.pos.crown': ('rq2.total.pos.as-emitted-rate', 'percent'), 'rq2.total.pos.laertes': ('rq2.total.pos.as-emitted-rate', 'percent'),
       'rq2.total.uses.crown': ('rq2.total.pos.as-emitted-rate', 'percent'), 'rq2.total.uses.laertes': ('rq2.total.pos.as-emitted-rate', 'percent')}
if WRITE:
    lines = open(NOR).read().split('\n')
    have = {re.match(r'^\| ([^ |]+) \|', l).group(1): i for i, l in enumerate(lines) if re.match(r'^\| ([^ |]+) \|', l)}
    for k, (after, unit) in NEW.items():
        if k not in have:
            i = [j for j, l in enumerate(lines) if l.startswith(f'| {after} |')][0]
            lines.insert(i + 1, f'| {k} | | pending | n/a | {unit} | |')
            have = {re.match(r'^\| ([^ |]+) \|', l).group(1): j for j, l in enumerate(lines) if re.match(r'^\| ([^ |]+) \|', l)}
    done = set()
    for i, l in enumerate(lines):
        m = re.match(r'^\| ([^ |]+) \|', l)
        if m and m.group(1) in seed:
            c = [x.strip() for x in l.strip().strip('|').split('|')]
            if c[2] == 'measured':
                sys.exit(f'{m.group(1)} is measured; nothing written')
            c[1], c[2], c[5] = seed[m.group(1)][0], 'pending', seed[m.group(1)][1]
            lines[i] = '| ' + ' | '.join(c) + ' |'
            done.add(m.group(1))
    miss = set(seed) - done
    if miss:
        sys.exit(f'absent: {sorted(miss)}')
    open(NOR, 'w').write('\n'.join(lines))
    print(f'wrote {len(done)} rows ({len([k for k in NEW if k])} new)', file=sys.stderr)
