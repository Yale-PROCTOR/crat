#!/usr/bin/env python3
"""relay 116 / S25b: seeds the decl-uses family (Table 5's Uses columns) from t5/out into t5/stage.json.
Run after run_t5.py (sides input, crown, ours14u, ours54p, laertes_before, laertes_after, derived, derived_pre814)
and the urlparser key-normalization run (out/urlparser-roottest). Fails closed on the controls."""
import csv, json, os, statistics, subprocess

T5 = 'scratch/analysis-fanout/r146/trees/t5'
OURS = os.environ['OURS']
OUT = os.path.join(T5, 'out')
CRAT = 'crat'
PROGRAMS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
            'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
PAPER_LAERTES_USES = {'brotli': 0.0}   # CROWN's paper (arXiv 2303.10515v1) p. 17, Table 2, #uses / Laertes column
EXE = 'scratch/analysis-fanout/r043/target/release/rq2_pos_counter'
PRE = ('at the frame of record L01^14u (landed 2026-10-07, R869-1; borrow-ownership 897426dae): census main/frame14u; '
       'analysis-fanout 094 (relay 116), ')
INSTR = (f'the PRE-BUILT typed counter rq2_pos_counter ({EXE}; analysis-fanout 031; rustc nightly-2025-06-23; nothing '
         'built) run per program by scratch/analysis-fanout/r116/t5/run_t5.py <side> (pos_census.run unchanged '
         'but for the prebuilt binary; nice 10), its T2 `official` column = Q12\'s registered usage rule (one '
         'occurrence per visited place rooted at a debug-named local whose key is in CROWN\'s 2,414-slot universe, '
         'the fn_data d0 Mut∩Ptr keys of the artifact, with a Deref in its projection; mir_drops_elaborated) and '
         '`official_raw` = the same keyed through the exposure wrapper\'s twin and restricted to raw-pointer-typed '
         'roots (the remaining raw uses on an output); seeded by r116/t5/seed_t5.py')


def git_show(path):
    return subprocess.run(['git', '-C', f'{CRAT}/docs', 'show', f'origin/main:{path}'], capture_output=True,
                          text=True, check=True).stdout


def uses(side, p, col, base=OUT):
    d = os.path.join(base, side, p)
    if not os.path.exists(os.path.join(d, 'uses.tsv')):
        return None
    assert open(os.path.join(d, 'status.txt')).read().split()[0] == 'ok', (side, p)
    return sum(int(r[col]) for r in csv.DictReader(open(os.path.join(d, 'uses.tsv')), delimiter='\t'))


def unmapped(side, p, base=OUT):
    return {l for l in open(os.path.join(base, side, p, 'universe-unmapped.txt')).read().splitlines() if l}


def pct(a, b):
    return f'{100.0 * a / b:.1f}%' if b else '---'


def main():
    ev = {}
    for r in csv.reader(open(f'{CRAT}/benchmarks/rs-crown-transformed/evaluation.tsv')):
        if r and r[0] != 'Benchmark Name':
            ev[r[0]] = (int(r[4]), int(r[5]))
    val = {r['program']: r for r in csv.DictReader(git_show(
        'agents/tasks/2026-07-28-crown-usage-metric-validation.csv').splitlines())}
    c25 = {r['program']: int(r['observed_usage']) for r in csv.DictReader(git_show(
        'agents/tasks/2026-07-28-crown-usage-metric-candidates.csv').splitlines()) if r['candidate'] == 'deref-debug-roots'}

    # ---- controls (fail closed)
    assert all(int(val[p]['observed_usage']) == int(val[p]['official_usage_before']) == ev[p][0] for p in PROGRAMS)
    assert sum(ev[p][0] for p in PROGRAMS) == 12448
    in25 = {p: uses('input', p, 'official') for p in PROGRAMS}
    assert all(in25[p] == c25[p] and not unmapped('input', p) for p in PROGRAMS), 'the 2025 row does not reproduce'
    assert sum(in25.values()) == 12172
    r065 = 'scratch/analysis-fanout/r065/out'
    for s, t in (('input', 'input'), ('crown', 'crown'), ('ours54p', 'ours')):
        for p in PROGRAMS:
            assert open(f'{OUT}/{s}/{p}/uses.tsv').read() == open(f'{r065}/{t}/{p}/uses.tsv').read(), (s, p)
    assert sum(uses('input', p, 'full_roots') for p in PROGRAMS) == 27663          # the record's rq1.total.uses.before
    assert sum(uses('ours54p', p, 'full_roots') for p in PROGRAMS) == 27663 - 13467  # rq1.total.uses.delivered at 54'

    rows, stage = {}, []

    def add(key, value, layer, unit, prov):
        stage.append(dict(key=key, value=value, status='pending', layer=layer, unit=unit, provenance=prov, was=''))

    for p in PROGRAMS:
        k = p.replace('.', '')
        b23, a23 = ev[p]
        ours = uses(OURS, p, 'official_raw')
        crown25 = uses('crown', p, 'official_raw')
        r = dict(p=p, b23=b23, a23=a23, in25=in25[p], ours=ours, deliv=in25[p] - ours, crown25=crown25,
                 ours54=uses('ours54p', p, 'official_raw'))
        # Laertes: own before tree (the tree Laertes transformed; CROWN's artifact does the same, evaluate.sh
        # ORIGINAL=comparison/laertes-*/before), the same universe; a universe key the Laertes tree does not hold
        # counts as NOT made safe (the decl column's rule): its uses on rs-crown are added to the denominator
        if p == 'urlparser':
            base = os.path.join(OUT, 'urlparser-roottest')
            lb, la = uses('laertes_before', p, 'official', base), uses('laertes_after', p, 'official_raw', base)
            assert not unmapped('laertes_before', p, base) and not unmapped('laertes_after', p, base)
            r['lstate'] = 'counted (feature-gate shim; universe keys read without the root file\'s `test::` segment)'
            U = 0
        else:
            lb, la = uses('laertes_before', p, 'official'), uses('laertes_after', p, 'official_raw')
            U = 0
            if lb is not None:
                ub, ua = unmapped('laertes_before', p), unmapped('laertes_after', p)
                assert ub == ua, p
                if ub:
                    keys = [l for l in open(f'{OUT}/universe/{p}.txt').read().split() if l]
                    st = lambda q: q[5:] if q.startswith('src::') else q
                    fk = {}
                    for q in keys:
                        fk.setdefault(q.rsplit('::', 1)[0], []).append(st(q) in ub)
                    iu = {x['function']: int(x['official'])
                          for x in csv.DictReader(open(f'{OUT}/input/{p}/uses.tsv'), delimiter='\t')}
                    U = sum(iu.get(f, 0) for f, v in fk.items() if all(v))
                r['lunm'] = len(ub)
                shim = 'feature-gate shim' if 'removed feature gates' in open(f'{OUT}/laertes_after/{p}/cmd.txt').read() else ''
                adapted = os.path.isdir(f'{T5}/adapted/laertes_after/{p}')
                r['lstate'] = ('adapted-and-counted (llvm_asm!, relay 117\'s adapter; ' + shim + ')') if adapted else (
                    f'counted ({shim})' if shim else 'counted')
            else:
                r['lstate'] = 'no tree'
        r.update(lb=lb, la=la, lU=U)
        rows[p] = r

        add(f'rq1.{k}.decl-uses.before', str(b23), 'n/a', 'count',
            PRE + f'CROWN\'s own usage counter (the Q12 instrument, docs agents/tasks/2026-07-28-crown-usage-metric.md: '
            f'nightly-2023-01-26 optimized MIR over the 2,414 declarations of rq1.total.decl.before) on benchmarks/'
            f'rs-crown: {b23}, = the artifact\'s evaluation.tsv BEFORE usage cell, which Q12 reproduced 20/20 (12,448; '
            f'validation csv, observed {val[p]["observed_usage"]}); frame-independent (the input). Not re-run here: the '
            f'2023 instrument has no built binary on this host and this relay builds nothing; the counter that runs '
            f'here (2025, below) reads {in25[p]} on the same input (Q12\'s registered 2025 row, reproduced exactly).')
        note_cmp = (f'{in25[p]} on benchmarks/rs-crown (`official`) minus {ours} on frame14u/emitted-trees/{p} '
                    f'(`official_raw`, the twin reading)')
        add(f'rq1.{k}.decl-uses.delivered', str(in25[p] - ours), 'delivered', 'count',
            PRE + INSTR + '; ' + note_cmp + f' = {in25[p] - ours} uses of CROWN\'s population no longer on a raw '
            f'pointer, IN THE 2025 COUNTER\'S UNITS (its before is {in25[p]}, not the 2023 cell {b23}); never print it '
            f'as "of" rq1.{k}.decl-uses.before. CONTROL: the same run on main/b54p (54′) gives {r["ours54"]} remaining; '
            f'the counter\'s outputs on rs-crown, CROWN\'s outputs and b54p equal r065/out byte for byte (20/20).')
        add(f'rq1.{k}.decl-uses.rate', pct(in25[p] - ours, in25[p]), 'n/a', 'percent',
            PRE + INSTR + '; ' + note_cmp + f': {pct(in25[p] - ours, in25[p])} (one counter both sides; '
            + ('0 uses in the input: CROWN\'s Table 2 prints "-"' if not in25[p] else
               f'at 54′ the same reads {pct(in25[p] - r["ours54"], in25[p])}') + ').')
        cr = pct(b23 - a23, b23)
        add(f'rq2.{k}.decl-uses.crown', cr, 'n/a', 'percent',
            PRE + f'CROWN\'s own counter on CROWN\'s output, verbatim: benchmarks/rs-crown-transformed/evaluation.tsv '
            f'(SHA-256 7aa16d5b…, the artifact\'s #Unsafe Mutable Non-Array Usages {b23} -> {a23}) = {cr}'
            + (' (CROWN\'s Table 2: "-")' if not b23 else '') + f'; frame-independent. CONTROL (the counter of the '
            f'other columns, 2025, run here on rs-crown-transformed/{p}): {in25[p]} -> {crown25} = '
            f'{pct(in25[p] - crown25, in25[p])}.')
        if r['lstate'] == 'no tree':
            v = f'{PAPER_LAERTES_USES[p]:.1f}%'
            add(f'rq2.{k}.decl-uses.laertes', v, 'n/a', 'percent',
                'from the paper (CROWN Table 2): ' + PRE + f'no Laertes output in the artifact (comparison/laertes-crown/after '
                f'and comparison/laertes-path hold no {p}; R882-1 (2)); Laertes is not run on our side (R858-3); the '
                f'figure is CROWN\'s Table 2 #uses/Laertes cell for {p}, {v} (CROWN, arXiv 2303.10515v1 p. 17, text '
                f'extracted into scratch/analysis-fanout/r116/t5/crown-paper.txt; that text carries no dagger '
                f'glyph, the mark is the manuscript\'s); print it with the dagger, as rq2.{k}.decl.laertes.')
        else:
            den = lb + U
            v = pct(lb - la, den)
            add(f'rq2.{k}.decl-uses.laertes', v, 'n/a', 'percent',
                PRE + INSTR + f'; the artifact\'s Laertes trees ({r["lstate"]}): {lb} on its BEFORE tree (`official`; '
                f'the tree Laertes transformed, as CROWN\'s evaluate.sh does) minus {la} on its AFTER tree '
                f'(`official_raw`)' + (f', over {lb} + {U} (the rs-crown uses of the {r.get("lunm")} universe keys '
                                       f'the Laertes translation does not hold, counted as not made safe, the decl '
                                       f'column\'s rule; over the mapped keys alone: {pct(lb - la, lb)})'
                                       if r.get('lunm') else '') + f' = {v}'
                + (' (0 uses: "-")' if not den else '') + '; frame-independent.')

    # ---- totals and medians
    T = lambda f: sum(f(r) for r in rows.values())
    tb, ti, to = T(lambda r: r['b23']), T(lambda r: r['in25']), T(lambda r: r['ours'])
    add('rq1.total.decl-uses.before', str(tb), 'n/a', 'count',
        PRE + 'CROWN\'s own usage counter (Q12, 2023) on the twenty inputs = evaluation.tsv BEFORE usages, 12,448 '
        '(Q12 reproduced 20/20); the 2025 counter reads 12,172 on the same inputs (Q12\'s registered 2025 row).')
    add('rq1.total.decl-uses.delivered', str(ti - to), 'delivered', 'count',
        PRE + INSTR + f'; {ti} - {to} remaining on frame14u = {ti - to}, in the 2025 counter\'s units (of {ti}, not '
        f'of {tb}). CONTROL: 54′ reads {ti} - {T(lambda r: r["ours54"])}.')
    add('rq1.total.decl-uses.rate', pct(ti - to, ti), 'n/a', 'percent',
        PRE + INSTR + f'; {ti - to}/{ti} = {pct(ti - to, ti)} (pooled; at 54′ {pct(ti - T(lambda r: r["ours54"]), ti)}).')
    cb, ca = tb, T(lambda r: r['a23'])
    add('rq2.total.decl-uses.crown', pct(cb - ca, cb), 'n/a', 'percent',
        PRE + f'evaluation.tsv verbatim, pooled: ({cb} - {ca})/{cb} = {pct(cb - ca, cb)}; CONTROL (2025 counter): '
        f'({ti} - {T(lambda r: r["crown25"])})/{ti} = {pct(ti - T(lambda r: r["crown25"]), ti)}.')
    L = [r for r in rows.values() if r['lb'] is not None]
    lnum, lden = sum(r['lb'] - r['la'] for r in L), sum(r['lb'] + r['lU'] for r in L)
    add('rq2.total.decl-uses.laertes', pct(lnum, lden), 'n/a', 'percent',
        PRE + INSTR + f'; pooled over the {len(L)} programs the artifact ships a Laertes tree for (brotli: none, as '
        f'rq2.total.decl.laertes-rate): {lnum}/{lden} = {pct(lnum, lden)} (over the mapped keys alone '
        f'{pct(lnum, sum(r["lb"] for r in L))}).')
    med = lambda xs: f'{statistics.median(xs):.1f}%'
    ours_rates = [100.0 * r['deliv'] / r['in25'] for r in rows.values() if r['in25']]
    crown_rates = [100.0 * (r['b23'] - r['a23']) / r['b23'] for r in rows.values() if r['b23']]
    lae_rates = []
    for r in rows.values():
        if r['lb'] is None:
            lae_rates.append(PAPER_LAERTES_USES[r['p']])
        elif r['lb'] + r['lU']:
            lae_rates.append(100.0 * (r['lb'] - r['la']) / (r['lb'] + r['lU']))
    add('rq1.median.decl-uses.rate', med(ours_rates), 'n/a', 'percent',
        PRE + INSTR + f'; statistics.median of the {len(ours_rates)} per-program rates of programs with uses '
        '(robotfindskitten has 0: excluded, as CROWN\'s Table 2 median and rq1.median.uses.rate).')
    add('rq2.median.decl-uses.crown', med(crown_rates), 'n/a', 'percent',
        PRE + f'evaluation.tsv verbatim: statistics.median of the {len(crown_rates)} per-program rates (robotfindskitten '
        'excluded, 0 uses); reproduces CROWN\'s paper (p. 17: "median ... raw pointer uses ... 62.1%").')
    add('rq2.median.decl-uses.laertes', med(lae_rates), 'n/a', 'percent',
        PRE + INSTR + f'; statistics.median of the {len(lae_rates)} per-program Laertes rates (robotfindskitten '
        'excluded, 0 uses; brotli = CROWN\'s Table 2 figure 0.0%, from the paper, as rq2.median.decl.laertes).')
    assert med(crown_rates) == '62.1%'
    json.dump(stage, open(os.path.join(T5, OURS + '-stage.json'), 'w'), indent=1, ensure_ascii=False)
    json.dump(rows, open(os.path.join(T5, OURS + '-rows.json'), 'w'), indent=1)
    print(len(stage), 'rows staged')
    print('program\tb23\tin25\tours\trate\tcrown(ev)\tcrown25\tL.lb\tL.la\tL.U\tL.rate\tL.state')
    for r in rows.values():
        lr = '-' if r['lb'] is None else pct(r['lb'] - r['la'], r['lb'] + r['lU'])
        print('\t'.join(map(str, (r['p'], r['b23'], r['in25'], r['ours'], pct(r['deliv'], r['in25']),
                                  pct(r['b23'] - r['a23'], r['b23']), pct(r['in25'] - r['crown25'], r['in25']),
                                  r['lb'], r['la'], r['lU'], lr, r['lstate']))))
    for s in stage:
        if '.total.' in s['key'] or '.median.' in s['key']:
            print(s['key'], s['value'])


if __name__ == '__main__':
    main()
