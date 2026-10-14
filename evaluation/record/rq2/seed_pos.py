#!/usr/bin/env python3
"""seed_pos.py — analysis-fanout 031 (relay 043, R753-1): write the position / use keys from a pos_census.py run.

  seed_pos.py --out DIR [--write] [--label TEXT]

Every row is written `pending` with a `provisional:` provenance (the evaluation stays blank until the freeze; `measured`
only on the seat's word). Keys filled from the four sides that exist in DIR:
  rq2.<prog>.pos.{crown,laertes}, rq2.median.pos.{crown,laertes}        (CROWN's / Laertes's outputs)
  rq1.<prog>.pos.before, rq1.<prog>.uses.before, rq1.total.{pos,uses}.before   (the inputs)
  rq1.<prog>.pos.{delivered,rate}, rq1.<prog>.uses.{delivered,rate}, rq1.total.*, rq1.median.*, rq2.wins.pos
                                                                        (our trees: only when the `ours` side exists)
Definitions (pos_census.py's header; analysis-fanout 031's definition of record):
  pos.before   the input's raw pointer layers (T1, full scope; the input's duplicated header structs counted once;
               `byref` bindings excluded)
  pos.<side>   the share of those layers whose position holds a non-raw form in the side's output (ours: the twin
               reading); an unmatched position counts as not delivered
  uses.before  the input's T2 (`full_roots`); uses.delivered = before - ours (`full_roots` on our tree)"""
import argparse, csv, os, re, statistics, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'positions-uses'))
import pos_census as P  # noqa: E402

NOR = os.environ.get('NOR', os.path.join(P.CRAT, 'docs/paper/numbers-of-record.md'))


def key(p):
    return p.replace('.', '')


def pct(a, b):
    return f'{100.0 * a / b:.1f}%' if b else '---'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--label', default='')
    a = ap.parse_args()
    rows = {r['program']: r for r in csv.DictReader(open(os.path.join(a.out, 'per-program.tsv')), delimiter='\t')}
    num = lambda r, c: int(r[c]) if r.get(c, '-') not in ('-', '') else None
    seed = {}
    rates = {'crown': [], 'laertes': []}
    ours = os.path.isdir(os.path.join(a.out, 'ours'))
    tb = tu = 0
    for p in P.PROGRAMS:
        r = rows[p]
        before = num(r, 'input.t1.raw')
        ub = num(r, 'input.t2.full_roots')
        tb, tu = tb + before, tu + ub
        seed[f'rq1.{key(p)}.pos.before'] = (str(before), 'raw pointer layers in the c2rust input (T1)')
        seed[f'rq1.{key(p)}.uses.before'] = (str(ub), 'raw-pointer uses in the c2rust input (T2 full_roots)')
        for s in ('crown', 'laertes'):
            d, b, un = num(r, f'{s}.pos.delivered'), num(r, f'{s}.pos.before'), num(r, f'{s}.pos.unmatched')
            if d is None:
                why = ('the artifact ships no Laertes output' if p == 'brotli' else
                       'the Laertes output does not compile under nightly-2025-06-23 (llvm_asm!)'
                       if p == 'libzahl' else 'not run')
                seed[f'rq2.{key(p)}.pos.{s}'] = ('', why)
                continue
            rates[s].append(100.0 * d / b)
            note = f'{d}/{b} input raw layers non-raw in the output' + (f' ({un} unmatched)' if un else '')
            shim = os.path.join(a.out, s, p, 'shim.txt')
            if os.path.exists(shim):
                note += '; ' + open(shim).readline().strip() + ' (a shim copy)'
            seed[f'rq2.{key(p)}.pos.{s}'] = (pct(d, b), note)
        if ours:
            d = num(r, 'ours.pos.delivered')
            seed[f'rq1.{key(p)}.pos.delivered'] = (str(d), 'input raw layers non-raw in our tree (twin reading)')
            seed[f'rq1.{key(p)}.pos.rate'] = (pct(d, before), '')
            ua = num(r, 'ours.t2.full_roots')
            seed[f'rq1.{key(p)}.uses.delivered'] = (str(ub - ua), f'{ub} - {ua} raw-pointer uses remaining')
            seed[f'rq1.{key(p)}.uses.rate'] = (pct(ub - ua, ub), '')
    seed['rq1.total.pos.before'] = (str(tb), 'the twenty inputs')
    seed['rq1.total.uses.before'] = (str(tu), 'the twenty inputs')
    if ours:
        td = sum(num(rows[p], 'ours.pos.delivered') for p in P.PROGRAMS)
        tua = sum(num(rows[p], 'ours.t2.full_roots') for p in P.PROGRAMS)
        seed['rq1.total.pos.delivered'] = (str(td), 'input raw layers non-raw in our trees (twin reading)')
        seed['rq1.total.pos.rate'] = (pct(td, tb), '')
        seed['rq1.total.uses.delivered'] = (str(tu - tua), f'{tu} - {tua} raw-pointer uses remaining')
        seed['rq1.total.uses.rate'] = (pct(tu - tua, tu), '')
        pr = [100.0 * num(rows[p], 'ours.pos.delivered') / num(rows[p], 'input.t1.raw') for p in P.PROGRAMS]
        ur = [100.0 * (num(rows[p], 'input.t2.full_roots') - num(rows[p], 'ours.t2.full_roots'))
              / num(rows[p], 'input.t2.full_roots') for p in P.PROGRAMS if num(rows[p], 'input.t2.full_roots')]
        seed['rq1.median.pos.rate'] = (f'{statistics.median(pr):.1f}%', 'median of the 20 programs')
        seed['rq1.median.uses.rate'] = (f'{statistics.median(ur):.1f}%', f'median of the {len(ur)} programs with uses')
        # wins (015 STOP 2's rule): ours strictly above CROWN and Laertes; a dagger program compares with CROWN only
        wins, ties = 0, []
        for p in P.PROGRAMS:
            r = rows[p]
            o = num(r, 'ours.pos.delivered') / num(r, 'input.t1.raw')
            others = [num(r, f'{x}.pos.delivered') / num(r, f'{x}.pos.before') for x in ('crown', 'laertes')
                      if num(r, f'{x}.pos.delivered') is not None]
            if o > max(others):
                wins += 1
            elif o == max(others):
                ties.append(p)
        seed['rq2.wins.pos'] = (str(wins), f'programs where our position rate is strictly the highest of the three '
                                           f'(brotli / libzahl against CROWN only); ties: {", ".join(ties) or "none"}')
    for s in ('crown', 'laertes'):
        seed[f'rq2.median.pos.{s}'] = (f'{statistics.median(rates[s]):.1f}%', f'median over {len(rates[s])} programs')
    text = open(NOR).read()
    prov = (f'provisional: analysis-fanout 031, docs/agents/tools/rq2/pos_census.py + seed_pos.py '
            f'(rustc nightly-2025-06-23 typed counter; {a.label}); ')
    for k, (v, note) in seed.items():
        print(k, v, note, sep='\t')
    if a.write:
        lines = text.split('\n')
        done = set()
        for i, line in enumerate(lines):
            m = re.match(r'^\| ([^ |]+) \|', line)
            if m and m.group(1) in seed:
                cells = [c.strip() for c in line.strip().strip('|').split('|')]
                if cells[2] == 'measured':
                    continue
                v, note = seed[m.group(1)]
                cells[1], cells[2], cells[5] = v, 'pending', prov + note
                lines[i] = '| ' + ' | '.join(cells) + ' |'
                done.add(m.group(1))
        missing = sorted(set(seed) - done)
        if missing:
            sys.exit(f'keys absent (or measured) in numbers-of-record: {missing}; nothing written')
        open(NOR, 'w').write('\n'.join(lines))
        print(f'wrote {len(done)} rows (pending)', file=sys.stderr)


if __name__ == '__main__':
    main()
