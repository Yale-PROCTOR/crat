#!/usr/bin/env python3
"""Seed the &inator side of RQ3 (docs/paper/numbers-of-record.md) from the rq3-inator lane's TSVs.

  rq3.inator.<prog>.reported-s  &inator's paper, arXiv 2604.17261v2 (PACMPL 10 PLDI, Art. 192) Table 3,
                                the program's row: Analysis + Solving, as printed (a "<0.1s" analysis
                                counts 0); their host: Xeon Platinum 8268, Z3 4.13.3, mean of five
  rq3.inator.<prog>.host-s      &inator on the measuring host ($RQ3_HOST): the minimum over the program's clean ok trials of the
                                artifact's own analysis + solving timers summed (times.txt; R677-5), the
                                in-container and outer walls in the provenance; tisp, on which the shipped
                                image panics, from the diagnostic source build (R677-5); a program with no
                                ok trial otherwise gets its last row's `failed:<reason>`

`<prog>` is the registry name: the artifact's `running-example` is `example`. The loc key is
analysis-fanout's (relay 022); this tool never touches it. Rows stay `pending` (relay 004); a row
that is not `pending` is skipped and named.

  --ours TSV (relay rq3-inator 036): seed ONLY our side, from an 018a-protocol `rq3-trials.tsv`
  (`rq3_trials.py run`: stages substrate / solve / emit per trial), and nothing of &inator's:
  rq3.inator.<prog>.analysis-s  min over the program's trials of the substrate + S1 solve process walls
  rq3.inator.<prog>.emit-s      min over the program's trials of the census child's process wall
  The two minima are taken independently, as the rows seeded from 018a were. --ours-note is the
  provenance's text for the head, the binary and the window.

Usage: seed_rq3_inator.py [--write] [--tsv-dir DIR]
       seed_rq3_inator.py [--write] --ours TSV --ours-note TEXT
  (default DIR: agents/artifacts/2026-09-29-rq3-inator/results beside this checkout)
"""
import argparse, csv, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOCS = os.environ.get('DOCS_ROOT', os.path.abspath(os.path.join(HERE, '../../../docs')))  # the documentation repository
HOST = os.environ.get('RQ3_HOST', 'host-b')  # the name the provenance gives the measuring host
NOR = os.environ.get('RECORD', os.path.join(DOCS, 'paper/numbers-of-record.md'))
TSV_DIR = os.path.join(DOCS, 'agents/artifacts/2026-09-29-rq3-inator/results')
DIAG_DIR = os.path.join(DOCS, 'agents/artifacts/2026-09-29-rq3-inator/diag/results')
# programs whose host-s comes from the diagnostic source build when the artifact image fails (R677-5)
DIAG = {'tisp': ('the pinned source 4f1d6a5 built with the artifact\'s own unmodified Dockerfile '
                 '(refinator-src@sha256:5d290ece…; report 002 section 3: it times example / ulidgen / carrays '
                 'within 0-5% of the image)')}

PROGS = ['running-example', 'ulidgen', 'leftpad', 'amp', 'nandc', 'rbtree', 'carrays', 'jccc', 'tisp']
REGISTRY = {'running-example': 'example'}
# Table 3 (p. 20): program -> (row label, Analysis as printed, Solving as printed), seconds
TABLE3 = {
    'running-example': ('Fig. 2(a)', '<0.1', '0.6'),
    'ulidgen': ('ulidgen', '0.1', '33'),
    'leftpad': ('leftpad', '0.1', '7.8'),
    'amp': ('amp', '0.1', '17'),
    'nandc': ('nandc', '0.1', '9.9'),
    'rbtree': ('rbtree', '2.1', '1,100'),
    'carrays': ('carrays', '0.7', '150'),
    'jccc': ('jccc', '4.2', '17,000'),
    'tisp': ('tisp', '7.1', '25,000'),
}


def num(s):
    return 0.0 if s.startswith('<') else float(s.replace(',', ''))


def ours(path, note):
    """relay rq3-inator 036: analysis-s / emit-s from an 018a-protocol rq3-trials.tsv."""
    rows = list(csv.DictReader(open(path), delimiter='\t'))
    tsv = os.path.relpath(os.path.abspath(path), DOCS)
    values = {}
    for prog in PROGS:
        name = REGISTRY.get(prog, prog)
        trials = {}
        for r in rows:
            if r['program'] == prog and r['trial'] != '-':
                trials.setdefault(r['trial'], {})[r['stage']] = r
        ok = {t: s for t, s in trials.items() if all(k in s and s[k]['exit'] == '0' for k in ('substrate', 'solve', 'emit'))}
        if not ok:
            continue
        an = {t: float(s['substrate']['wall_s']) + float(s['solve']['wall_s']) for t, s in ok.items()}
        em = {t: float(s['emit']['wall_s']) for t, s in ok.items()}
        ta, te = min(an, key=an.get), min(em, key=em.get)
        order = sorted(ok, key=int)
        values[f'rq3.inator.{name}.analysis-s'] = (
            f'{an[ta]:.2f}',
            f'{HOST} (rq3-inator 021, relay 036): min over {len(ok)} ok trial(s) of {len(trials)} of substrate + S1 '
            f'solve process walls (/usr/bin/time -v); trials {", ".join(f"{an[t]:.2f}" for t in order)}; min trial {ta}: '
            f'substrate {float(ok[ta]["substrate"]["wall_s"]):.3f} + solve {float(ok[ta]["solve"]["wall_s"]):.3f}; {note}; {tsv}')
        values[f'rq3.inator.{name}.emit-s'] = (
            f'{em[te]:.2f}',
            f'{HOST} (rq3-inator 021, relay 036): min over {len(ok)} ok trial(s) of {len(trials)} of the census child '
            f'(raw-boundary-census, cache-only) process walls (/usr/bin/time -v); trials '
            f'{", ".join(f"{em[t]:.2f}" for t in order)}; min trial {te}; {note}; {tsv}')
    return values


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--tsv-dir', default=TSV_DIR)
    ap.add_argument('--diag-dir', default=DIAG_DIR)
    ap.add_argument('--ours')
    ap.add_argument('--ours-note', default='')
    a = ap.parse_args()

    values = ours(a.ours, a.ours_note) if a.ours else {}
    for prog in ([] if a.ours else PROGS):
        name = REGISTRY.get(prog, prog)
        row, an, sv = TABLE3[prog]
        values[f'rq3.inator.{name}.reported-s'] = (
            f'{num(an) + num(sv):g}',
            f'arXiv 2604.17261v2 Table 3 row "{row}": Analysis {an}s + Solving {sv}s '
            f'(their host: Xeon Platinum 8268 2.9 GHz, LLVM 17.0.6, Z3 4.13.3; mean of five)')
        path = os.path.join(a.tsv_dir, f'inator-{prog}.tsv')
        if not os.path.exists(path):
            continue
        rows = list(csv.DictReader(open(path), delimiter='\t'))
        ok = [r for r in rows if r['status'] == 'ok']
        build = 'the artifact image refinator@sha256:ce24df0e…'
        tsv = os.path.relpath(path, DOCS)
        failed_note = ''
        if not ok and prog in DIAG:
            # R677-5 (relay 007): the shipped image panics on tisp before analysis; the pinned
            # source built with the artifact's own Dockerfile stands in, one stated trial
            failed_note = (f'the artifact image fails {len(rows)}/{len(rows)} ({rows[-1]["status"]}); ')
            dpath = os.path.join(a.diag_dir, f'inator-{prog}.tsv')
            rows = list(csv.DictReader(open(dpath), delimiter='\t'))
            ok = [r for r in rows if r['status'] == 'ok']
            build = DIAG[prog]
            tsv = os.path.relpath(dpath, DOCS)
        # a trial with a `note` (host contention, e.g. rbtree trial 1) stays a row but sets host-s
        # only when no clean ok trial exists
        noted = [r['trial'] for r in ok if r.get('note')]
        ok = [r for r in ok if not r.get('note')] or ok
        if ok:
            # R677-5: host-s = the artifact's own analysis + solving timers summed (times.txt),
            # like-for-like with reported-s; the walls stay in the provenance and the TSV
            sums = [float(r['internal_total_s']) for r in ok]
            best = min(ok, key=lambda r: float(r['internal_total_s']))
            values[f'rq3.inator.{name}.host-s'] = (
                f'{min(sums):.2f}',
                f'{HOST} (rq3-inator): {failed_note}min over {len(ok)} ok trial(s) of {len(rows)} of the '
                f'artifact\'s own analysis + solving timers (times.txt), {build}, Z3 4.15.4; trials '
                f'{", ".join(f"{s:.2f}" for s in sums)}; min trial {best["trial"]}: in-container GNU time wall '
                f'{float(best["wall_s"]):.2f}, outer docker-run wall {float(best["outer_wall_s"]):.2f}'
                + (f'; trial(s) {", ".join(noted)} excluded (host contention, see the TSV note)'
                   if noted and all(r['trial'] not in noted for r in ok) else '') + f'; {tsv}')
        elif rows:
            values[f'rq3.inator.{name}.host-s'] = (
                rows[-1]['status'], f'{HOST} (rq3-inator): all {len(rows)} trial(s) failed; {tsv}')

    lines = open(NOR).read().split('\n')
    seen, skipped = set(), []
    for i, line in enumerate(lines):
        if not line.startswith('| '):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if len(cells) < 6 or cells[0] not in values:
            continue
        if cells[2] != 'pending':
            skipped.append(f'{cells[0]} ({cells[2]})')
            continue
        seen.add(cells[0])
        cells[1], cells[5] = values[cells[0]][0], values[cells[0]][1].replace('|', '/')
        lines[i] = '| ' + ' | '.join(cells) + ' |'
    for k in sorted(values):
        print(f'{k}\t{values[k][0]}\t{values[k][1]}')
    absent = sorted(set(values) - seen - {s.split(' ')[0] for s in skipped})
    print(f'# {"seeded" if a.write else "would seed"} {len(seen)} rows (status stays pending); '
          f'skipped {len(skipped)} (not pending): {skipped}; absent from the record: {absent}')
    if a.write:
        open(NOR, 'w').write('\n'.join(lines))


if __name__ == '__main__':
    sys.exit(main())
