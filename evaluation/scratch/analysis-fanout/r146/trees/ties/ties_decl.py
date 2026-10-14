#!/usr/bin/env python3
"""analysis-fanout r108 g4-rq2: rq2.ties.decl (and the wins it is read beside) at a census frame.

usage: ties_decl.py <census dir> [--out <dir>] [--label <text>]

The manuscript (sections/evaluation.tex, RQ2): "On CROWN's population, counted as emitted, <ours> delivers the
strictly highest rate on \\nr{rq2.wins.decl} of the \\nr{setup.programs} programs and ties for the highest on
\\nr{rq2.ties.decl} more."  So rq2.ties.decl = the number of programs where our as-emitted declaration rate EQUALS
max(CROWN's rate, Laertes's rate) (not strictly above it).

Method = analysis-fanout 045's seed_r065.py wins/ties loop, re-run end to end without building anything:
- the counter is CROWN's official declaration counter (crown_artifact_inventory, unchanged) through the PRE-BUILT
  rq2_decl_driver (docs agents/tools/rq2/decl_driver, built 2026-10-02 05:49Z; this script never runs cargo);
- control first, fail-closed: CROWN's own twenty outputs reproduce benchmarks/rs-crown-transformed/evaluation.tsv,
  plain and with inline-mods;
- CROWN's rate: the counter on CROWN's emitted program (seed_rq2.py, 015);
- Laertes's rate: the counter on the Laertes output CROWN's artifact distributes (R858-3: never a Laertes run of
  ours); where the artifact ships none (brotli), CROWN's published Table 2 figure (seed_rq2.py's PUBLISHED_LAERTES);
- ours: the counter on <census>/emitted-trees/<p> AS EMITTED with inline-mods (decl_walker_vs_census.py, 030a),
  rate = (eliminated_ref + eliminated_box) / universe, exact;
- win: ours > max(crown, laertes) + 1e-9; tie: |ours - max(crown, laertes)| < 1e-9 (seed_r065.py lines 38-43).
Writes <out>/ties-decl.tsv (key, value, provenance) and <out>/per-program-decl.tsv."""
import argparse, csv, os, subprocess, sys

EXE = os.environ.get('RQ2_DECL_DRIVER',
                     'scratch/analysis-fanout/r10/target-tool/release/rq2_decl_driver')
BENCH = os.environ.get('CRAT_BENCH', 'crat/benchmarks')
CROWN = os.path.join(BENCH, 'rs-crown-transformed')
ARTIFACT = os.environ.get('CROWN_ARTIFACT', 'crown-artifact')
# CROWN paper Table 2, the Laertes column (copied verbatim from docs agents/tools/rq2/seed_rq2.py)
PUBLISHED_LAERTES = {'avl': 0.0, 'binn': 46.6, 'brotli': 0.0, 'bst': 0.0, 'buffer': 0.0, 'bzip2': 14.3,
                     'genann': 0.0, 'heman': 30.3, 'ht': 33.3, 'json.h': 2.3, 'libcsv': 65.0, 'libtree': 29.2,
                     'libzahl': 2.2, 'lil': 9.2, 'lodepng': 46.3, 'quadtree': 0.0, 'rgba': 83.3,
                     'robotfindskitten': 0.0, 'tulipindicators': 0.0, 'urlparser': 0.0}


def measure(emitted, analysis, flags=()):
    out = subprocess.run([EXE, emitted, analysis] + list(flags), check=True, capture_output=True,
                         text=True).stdout.split()
    d = dict(x.split('=') for x in out)
    return {k: (float(v) if k == 'rate' else int(v)) for k, v in d.items()}


def laertes_root(prog):
    lc = os.path.join(ARTIFACT, 'comparison/laertes-crown/after', prog)
    if os.path.isdir(lc):
        return lc, False
    for line in open(os.path.join(ARTIFACT, 'comparison/laertes-path')):
        line = line.strip()
        if line.split('/')[0] == prog:
            return os.path.join(ARTIFACT, 'comparison/laertes-laertes/after', os.path.dirname(line)), True
    return None, False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('census')
    ap.add_argument('--out', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out'))
    ap.add_argument('--label', default='')
    a = ap.parse_args()
    if not os.access(EXE, os.X_OK):
        sys.exit(f'no pre-built driver at {EXE}; this script never builds; nothing written')
    ev = {}
    for r in csv.reader(open(os.path.join(CROWN, 'evaluation.tsv'))):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]))
    progs = sorted(ev)
    rows = []
    for p in progs:
        t = os.path.join(CROWN, p)
        ar = os.path.join(t, 'analysis_results')
        for flags in ((), ('inline-mods',)):
            c = measure(t, ar, flags)
            if (c['universe'], c['after']) != ev[p] or c['parse_failures']:
                sys.exit(f'control failed on {p} {flags}: {c} vs evaluation.tsv {ev[p]}; nothing written')
        crate = 100.0 * (c['universe'] - c['after']) / c['universe']
        root, flat = laertes_root(p)
        if root:
            l = measure(root, ar, ('strip-src',) if flat else ())
            lrate, lsrc = 100.0 * (l['universe'] - l['after']) / l['universe'], 'measured'
        else:
            lrate, lsrc = PUBLISHED_LAERTES[p], 'published'
        tree = os.path.join(a.census, 'emitted-trees', p)
        if not os.path.isdir(tree):
            sys.exit(f'{p}: no emitted tree in {a.census}; nothing written')
        o = measure(tree, ar, ('inline-mods',))
        if o['universe'] != c['universe']:
            sys.exit(f'{p}: our universe {o["universe"]} != CROWN universe {c["universe"]}; nothing written')
        osafe = o['eliminated_ref'] + o['eliminated_box']
        orate = 100.0 * osafe / o['universe']
        best = max(crate, lrate)
        verdict = 'win' if orate > best + 1e-9 else ('tie' if abs(orate - best) < 1e-9 else 'below')
        rows.append({'program': p, 'universe': c['universe'], 'ours_safe': osafe, 'ours_rate': f'{orate:.4f}',
                     'ours_parse_failures': o['parse_failures'], 'crown_safe': c['universe'] - c['after'],
                     'crown_rate': f'{crate:.4f}', 'laertes_rate': f'{lrate:.4f}', 'laertes_source': lsrc,
                     'verdict': verdict})
    os.makedirs(a.out, exist_ok=True)
    with open(os.path.join(a.out, 'per-program-decl.tsv'), 'w') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    wins = [r['program'] for r in rows if r['verdict'] == 'win']
    ties = [r['program'] for r in rows if r['verdict'] == 'tie']
    base = (f'r108 g4-rq2 ties_decl.py {a.census} {a.label}: CROWN declaration counter (crown_artifact_inventory, '
            f'pre-built rq2_decl_driver, control 20/20 vs evaluation.tsv) on the emitted trees AS EMITTED vs CROWN '
            f'artifact output and the artifact-distributed Laertes output (brotli: CROWN Table 2, dagger); ')
    with open(os.path.join(a.out, 'ties-decl.tsv'), 'w') as f:
        f.write('key\tvalue\tprovenance\n')
        f.write(f'rq2.ties.decl\t{len(ties)}\t{base}ties = ours equal to max(CROWN, Laertes): {", ".join(ties) or "none"}\n')
        f.write(f'rq2.wins.decl\t{len(wins)}\t{base}strictly above both: {", ".join(wins) or "none"}\n')
    print(open(os.path.join(a.out, 'ties-decl.tsv')).read())


if __name__ == '__main__':
    main()
