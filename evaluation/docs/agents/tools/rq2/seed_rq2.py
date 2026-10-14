#!/usr/bin/env python3
"""Seed the paper's RQ2 keys (docs/paper/numbers-of-record.md) from CROWN's artifact (analysis-fanout 015).

  rq2.<prog>.decl.crown    CROWN's emitted program, CROWN's population (mutable non-array function slots),
                           rate of the Before count whose safe form is in the emitted program
  rq2.<prog>.decl.laertes  the same metric on the Laertes output the CROWN artifact ships for the program,
                           against CROWN's analysis universe of the same program; where the artifact ships no
                           Laertes output (brotli), CROWN's published Table 2 figure, marked for a dagger
  rq2.median.decl.{crown,laertes}, rq2.total.decl.crown (declarations CROWN makes safe, summed)
  rq2.wins.decl            programs where our rq1.<prog>.decl.rate is strictly the highest of the three
                           (only when every rq1.<prog>.decl.rate is measured)
  rq2.*.pos.*              NOT seeded: the all-positions walker is not settled (report 015 STOP 1)

The metric is the crown_artifact_inventory library's official-declaration counter, unmodified; decl_driver/
only lets the (universe, emitted program) pair vary. Every run re-checks the control: the driver on CROWN's
own twenty outputs must reproduce the artifact's evaluation.tsv before/after 20 / 20, else nothing is written.

Usage: seed_rq2.py [--write] [--table OUT.tsv]
  (paths default to this checkout: benchmarks/, crown-artifact, docs/paper/)
"""
import argparse, csv, os, re, statistics, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
CRAT = os.path.abspath(os.path.join(HERE, '../../../..'))
BENCH = os.path.join(CRAT, 'benchmarks')
ARTIFACT = os.environ.get('CROWN_ARTIFACT', 'crown-artifact')
NOR = os.path.join(CRAT, 'docs/paper/numbers-of-record.md')
TARGET = os.environ.get('RQ2_TARGET', 'scratch/analysis-fanout/r10/target-tool')

# CROWN paper, Table 2 (Zhang et al.): #ptrs and the Laertes declaration rate, for the dagger fallback and
# the cross-check of our Laertes measurement.
PUBLISHED_LAERTES = {'avl': 0.0, 'binn': 46.6, 'brotli': 0.0, 'bst': 0.0, 'buffer': 0.0, 'bzip2': 14.3,
                     'genann': 0.0, 'heman': 30.3, 'ht': 33.3, 'json.h': 2.3, 'libcsv': 65.0, 'libtree': 29.2,
                     'libzahl': 2.2, 'lil': 9.2, 'lodepng': 46.3, 'quadtree': 0.0, 'rgba': 83.3,
                     'robotfindskitten': 0.0, 'tulipindicators': 0.0, 'urlparser': 0.0}


def driver():
    exe = os.path.join(TARGET, 'release', 'rq2_decl_driver')
    subprocess.run(['cargo', 'build', '--release', '--offline', '--quiet', '--manifest-path',
                    os.path.join(HERE, 'decl_driver', 'Cargo.toml'), '--target-dir', TARGET], check=True)
    return exe


def measure(exe, emitted, analysis, strip=False):
    out = subprocess.run([exe, emitted, analysis] + (['strip-src'] if strip else []), check=True,
                         capture_output=True, text=True).stdout.split()
    d = dict(x.split('=') for x in out)
    return {k: (float(v) if k == 'rate' else int(v)) for k, v in d.items()}


def laertes_root(prog):
    """The Laertes output directory the artifact ships for prog, and whether its layout is flat."""
    lc = os.path.join(ARTIFACT, 'comparison/laertes-crown/after', prog)
    if os.path.isdir(lc):
        return lc, False
    for line in open(os.path.join(ARTIFACT, 'comparison/laertes-path')):
        line = line.strip()
        if line.split('/')[0] == prog:
            return os.path.join(ARTIFACT, 'comparison/laertes-laertes/after', os.path.dirname(line)), True
    return None, False


def key(prog):
    return prog.replace('.', '')


def fmt(x):
    return f'{x:.1f}%'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--table')
    a = ap.parse_args()
    exe = driver()
    ev = {}
    for r in csv.reader(open(os.path.join(BENCH, 'rs-crown-transformed/evaluation.tsv'))):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]))
    progs = sorted(ev)
    rows, seed = [], {}
    for p in progs:
        t = os.path.join(BENCH, 'rs-crown-transformed', p)
        c = measure(exe, t, os.path.join(t, 'analysis_results'))
        if (c['universe'], c['after']) != ev[p] or c['parse_failures']:
            sys.exit(f'control failed on {p}: {c} vs evaluation.tsv {ev[p]}; nothing written')
        c['rate'] = 100.0 * (c['universe'] - c['after']) / c['universe']      # exact, not the driver's rounding
        root, flat = laertes_root(p)
        if root:
            l = measure(exe, root, os.path.join(t, 'analysis_results'), strip=flat)
            lrate, lsrc = 100.0 * (l['universe'] - l['after']) / l['universe'], 'measured'
            lnote = f"{l['universe'] - l['after']}/{l['universe']} made safe in the artifact's Laertes output"
        else:
            l, lrate, lsrc = None, PUBLISHED_LAERTES[p], 'published'
            lnote = "the artifact ships no Laertes output; CROWN's published Table 2 figure (dagger)"
        rows.append({'program': p, 'crown_before': c['universe'], 'crown_after': c['after'], 'crown_rate': c['rate'],
                     'laertes_source': lsrc, 'laertes_rate': lrate, 'laertes_published': PUBLISHED_LAERTES[p],
                     'laertes_universe': l['universe'] if l else '-', 'laertes_after': l['after'] if l else '-'})
        seed[f'rq2.{key(p)}.decl.crown'] = (fmt(c['rate']),
            f"{c['universe'] - c['after']}/{c['universe']} made safe in CROWN's emitted program; reproduces the "
            f"artifact's evaluation.tsv")
        seed[f'rq2.{key(p)}.decl.laertes'] = (fmt(lrate), lnote + (
            f"; CROWN's Table 2 reads {fmt(PUBLISHED_LAERTES[p])}" if lsrc == 'measured' and
            abs(PUBLISHED_LAERTES[p] - round(lrate, 1)) > 0.05 else ''))
    seed['rq2.median.decl.crown'] = (fmt(statistics.median(r['crown_rate'] for r in rows)), 'median of the 20 programs')
    seed['rq2.median.decl.laertes'] = (fmt(statistics.median(r['laertes_rate'] for r in rows)),
                                       'median of the 20 programs (brotli the published figure)')
    seed['rq2.total.decl.crown'] = (str(sum(r['crown_before'] - r['crown_after'] for r in rows)),
                                    'declarations CROWN makes safe over the 20 programs')
    # wins: only when our side is measured for every program
    text = open(NOR).read()
    ours = {}
    for p in progs:
        m = re.search(r'^\| rq1\.' + re.escape(key(p)) + r'\.decl\.rate \| ([^|]*)\| measured \|', text, re.M)
        if m:
            ours[p] = float(m.group(1).strip().rstrip('%'))
    if len(ours) == len(progs):
        wins = sum(1 for r in rows if ours[r['program']] > max(r['crown_rate'], r['laertes_rate']))
        seed['rq2.wins.decl'] = (str(wins), 'programs where our rq1 decl rate is strictly the highest of the three')
    if a.table:
        with open(a.table, 'w') as f:
            cols = list(rows[0])
            f.write('\t'.join(cols) + '\n')
            for r in rows:
                f.write('\t'.join(str(r[c]) for c in cols) + '\n')
    prov_base = 'analysis-fanout report 015; docs/agents/tools/rq2/seed_rq2.py over CROWN\'s artifact ({})'
    for k, (v, note) in seed.items():
        print(k, v, note, sep='\t')
    if a.write:
        lines = open(NOR).read().split('\n')
        done = set()
        for i, line in enumerate(lines):
            m = re.match(r'^\| (rq2\.[^ |]+) \|', line)
            if m and m.group(1) in seed:
                cells = [c.strip() for c in line.strip().strip('|').split('|')]
                v, note = seed[m.group(1)]
                cells[1], cells[2] = v, 'measured'
                cells[5] = prov_base.format(note)
                lines[i] = '| ' + ' | '.join(cells) + ' |'
                done.add(m.group(1))
        missing = set(seed) - done
        if missing:
            sys.exit(f'keys absent from numbers-of-record: {sorted(missing)}; nothing written')
        open(NOR, 'w').write('\n'.join(lines))
        print(f'wrote {len(done)} rows', file=sys.stderr)


if __name__ == '__main__':
    main()
