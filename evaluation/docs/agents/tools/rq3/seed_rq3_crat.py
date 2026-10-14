#!/usr/bin/env python3
"""Seed the crat side of RQ3 (docs/paper/numbers-of-record.md) from analysis-fanout's trial TSV (relays 022-025).

  rq3.inator.<prog>.loc         cloc 2.00 code lines over the benchmark directory's .c/.h files at
                                PLaSSticity/refinator-impl 4fdf3309 (= Table 3's C LoC on 8 of 9; amp 96 vs 99),
                                from agents/artifacts/2026-09-29-analysis-fanout-016/loc.tsv
  rq3.inator.<prog>.analysis-s  our pipeline on host-a: the minimum over the program's trials of
                                (substrate wall + solve wall), each a `/usr/bin/time -v` process wall:
                                substrate = `crat --pass expand,extern,preprocess` (release), solve = S1
                                (`e5c_inner_solve_named_source`, the frame's identity env)
  rq3.inator.<prog>.emit-s      the minimum over trials of the census child's process wall
                                (`boc1_run_one`, raw-boundary-census, cache-only): the rewrite + the verify
                                rounds + the child's custody

Every trial is in the TSV (with a high-resolution wall beside /usr/bin/time's 10 ms one). Rows stay
`pending`; a row that is not `pending` is skipped and named. The timing keys are written only with
--timings (relay 023: the bst equivalence receipt precedes any timing key); --write alone seeds `loc`.
`<prog>` is the registry name: `running-example` is `example`.

Usage: seed_rq3_crat.py [--write] [--timings] [--tsv PATH] [--frame TEXT] [--provisional TEXT]
"""
import argparse, csv, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOCS = os.path.abspath(os.path.join(HERE, '../../..'))
NOR = os.path.join(DOCS, 'paper/numbers-of-record.md')
LOC = os.path.join(DOCS, 'agents/artifacts/2026-09-29-analysis-fanout-016/loc.tsv')
TSV = os.path.join(DOCS, 'agents/artifacts/2026-09-30-analysis-fanout-018/rq3-trials.tsv')
PROGS = ['running-example', 'ulidgen', 'leftpad', 'amp', 'nandc', 'rbtree', 'carrays', 'jccc', 'tisp']
REGISTRY = {'running-example': 'example'}


def token(note):
    """`failed:<reason>` for the value cell: the first word of the note after `failed:`."""
    rest = note.split('failed:', 1)[-1]
    return 'failed:' + rest.replace(':', ' ').split()[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--timings', action='store_true')
    ap.add_argument('--tsv', default=TSV)
    ap.add_argument('--frame', default='code frame 4feea9176 (L01^9 analyses, Mode-A repair), release profile')
    ap.add_argument('--provisional', default='', help='text prefixed as "provisional: <text>; " to every timing row')
    a = ap.parse_args()
    rel = os.path.relpath(a.tsv, DOCS)
    seed = {}
    for r in csv.DictReader(open(LOC), delimiter='\t'):
        k = REGISTRY.get(r['program'], r['program'])
        seed[f'rq3.inator.{k}.loc'] = (r['cloc_code'], f"analysis-fanout 016: cloc 2.00 code lines over the .c/.h files of "
                                       f"benchmarks/{r['program']} at refinator-impl 4fdf3309 (Table 3: {r['table3_c_loc']}); "
                                       f"agents/artifacts/2026-09-29-analysis-fanout-016/loc.tsv")
    rows = list(csv.DictReader(open(a.tsv), delimiter='\t'))
    for prog in PROGS:
        k = REGISTRY.get(prog, prog)
        mine = [r for r in rows if r['program'] == prog]
        fail = [r for r in mine if r['stage'] == 'prep']
        trials = {}
        for r in mine:
            if r['stage'] in ('substrate', 'solve', 'emit'):
                trials.setdefault(r['trial'], {})[r['stage']] = r
        okan = {t: s for t, s in trials.items() if all(s.get(g, {}).get('exit') == '0' for g in ('substrate', 'solve'))}
        okem = {t: s for t, s in trials.items() if s.get('emit', {}).get('exit') == '0'}
        def failure(stages):
            notes = [r['note'] for r in mine if r['stage'] in stages and r['note'].startswith('failed:')]
            notes = notes or [r['note'] for r in fail]
            return notes[-1] if notes else 'failed:no-complete-ok-trial'
        if okan:
            an = {t: float(s['substrate']['wall_s']) + float(s['solve']['wall_s']) for t, s in okan.items()}
            ta = min(an, key=an.get)
            seed[f'rq3.inator.{k}.analysis-s'] = (f'{an[ta]:.2f}', (
                f"host-a (analysis-fanout): min over {len(okan)} ok trial(s) of {len(trials)} of substrate + S1 solve "
                f"process walls (/usr/bin/time -v); trials {', '.join(f'{an[t]:.2f}' for t in sorted(an))}; min trial {ta}: "
                f"substrate {okan[ta]['substrate']['wall_s']} + solve {okan[ta]['solve']['wall_s']}; {a.frame}; {rel}"))
        else:
            why = failure(('substrate', 'solve'))
            seed[f'rq3.inator.{k}.analysis-s'] = (token(why), f'host-a (analysis-fanout): {why}; {a.frame}; {rel}')
        if okem:
            em = {t: float(s['emit']['wall_s']) for t, s in okem.items()}
            te = min(em, key=em.get)
            st = okem[te]['emit']['note'].split('rb=')[-1].split(' ')[0]
            seed[f'rq3.inator.{k}.emit-s'] = (f'{em[te]:.2f}', (
                f"host-a (analysis-fanout): min over {len(okem)} ok trial(s) of {len(trials)} of the census child's "
                f"process wall (rewrite + verify rounds + custody); trials {', '.join(f'{em[t]:.2f}' for t in sorted(em))}; "
                f"child status {st}; {a.frame}; {rel}"))
        else:
            why = failure(('emit',))
            seed[f'rq3.inator.{k}.emit-s'] = (token(why), f'host-a (analysis-fanout): {why}; {a.frame}; {rel}')
    for key, (v, prov) in seed.items():
        print(key, v, prov, sep='\t')
    if not a.write:
        return
    lines = open(NOR).read().split('\n')
    done, skipped = set(), []
    for i, line in enumerate(lines):
        cells = [c.strip() for c in line.strip().strip('|').split('|')] if line.startswith('| rq3.inator.') else None
        if not cells or cells[0] not in seed:
            continue
        if cells[0].endswith(('.analysis-s', '.emit-s')) and not a.timings:
            continue
        if cells[2] != 'pending':
            skipped.append(cells[0])
            continue
        v, prov = seed[cells[0]]
        if a.provisional and cells[0].endswith(('.analysis-s', '.emit-s')):
            prov = f'provisional: {a.provisional}; ' + prov
        cells[1], cells[5] = v, prov
        lines[i] = '| ' + ' | '.join(cells) + ' |'
        done.add(cells[0])
    open(NOR, 'w').write('\n'.join(lines))
    print(f'wrote {len(done)} rows; skipped (not pending): {skipped}', file=sys.stderr)


if __name__ == '__main__':
    main()
