#!/usr/bin/env python3
"""seed_numbers.py — seed the paper's numbers of record (paper/numbers-of-record.md) from a landed census.

Relay main/215 (R668-1): main seeds, from the landed census of record at the freeze (and provisionally from each
landing, so the paper session can see the values move), the keys main owns:

  setup.<prog>.sloc, setup.sloc, setup.programs, setup.largest-name, setup.largest-sloc, rq3.rest.sloc
  rq3.largest.{analysis-s,emit-s,verify-rounds}, rq3.rest.{analysis-s,emit-s}

R768-2 (10-03): `rq1.<prog>.decl.{before,delivered,rate}`, `rq1.total.decl.*` and `rq1.median.decl.rate` are NOT
written here any more: the manuscript's declaration column is CROWN's counter run unchanged on each system's output,
the analysis fan-out's verbatim walker, which owns those keys. The census-derived reading below (`decl`) is printed as a
note only (it is the fan-out's `rq2.total.decl.twin-rate`).

One command per landing:

  seed_numbers.py --census <census dir> --label '<batch NN at <head>, landed <date>>' --solve <frame solve dir>

Provisional by default: the value is written, the status STAYS `pending` (the manuscript renders the red placeholder,
the user's 2026-09-28 rule: the evaluation stays blank until the final measurement) and the provenance says
`provisional`. `--measured` (the freeze only) flips the seeded rows to `measured`. A row already `measured` or
`superseded` is never touched. `--dry-run` prints the rows and writes nothing.

Definitions (main 132; each is the seat's to change):
  sloc       non-blank lines that are not wholly comment, over the program's `.rs` files except `build.rs`, in the
             c2rust output as distributed (`benchmarks/rs-crown/<prog>`; the table caption: "Lines count the c2rust
             output"). The derived substrate's count is printed beside it, not seeded.
  decl       CROWN's published population (the inventory walker's universe, task 2026-07-27): `fn_data` pointer
             depth 0 with mutability `Mut` and fatness `Ptr` in the CROWN artifact's analysis JSONs. `before` must
             reproduce every BEFORE integer of `evaluation.tsv` (corpus 2,414), else the tool aborts. `delivered`:
             the declaration's census subjects (`subject_key` less its `#N`) are ALL `realized-as-predicted`; a
             declaration with no census subject counts as not delivered and is listed.
  rate       delivered / before, percent, one decimal.
  analysis-s the frame solve's `progress.jsonl` `wall_s` (the last complete record per program): the largest
             program, and the sum over the rest.
  emit-s     the census's `per-program.kv` `worker_wall_s` (the census worker's wall: loading the cached model,
             emission, verification and recovery; written for a typed-failure row too): the largest program, and the
             sum over the rest.
  verify-rounds  the census's `raw-boundary-outcome.tsv` `verify_rounds` for the largest program.
Keys this tool does not fill (pos, uses, check-s, rounds, the form rows, tests) stay as they are."""
import argparse, csv, glob, json, os, re, statistics, sys

csv.field_size_limit(10**9)
CRAT = 'crat'
RECORD = f'{CRAT}/docs/paper/numbers-of-record.md'
DISTRIBUTED = f'{CRAT}/benchmarks/rs-crown'
DERIVED = f'{CRAT}/benchmarks/rs-crown-derived'
CROWN = f'{CRAT}/benchmarks/rs-crown-transformed'
PROGRAMS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
            'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']


def key(prog):
    return prog.replace('.', '')


def sloc_of_text(text):
    n, block = 0, 0
    for line in text.splitlines():
        s, code, i = line, False, 0
        while i < len(s):
            if block:
                j, k = s.find('*/', i), s.find('/*', i)
                if k != -1 and (j == -1 or k < j):
                    block, i = block + 1, k + 2
                elif j != -1:
                    block, i = block - 1, j + 2
                else:
                    break
            elif s.startswith('//', i):
                break
            elif s.startswith('/*', i):
                block, i = 1, i + 2
            elif s[i].isspace():
                i += 1
            else:
                code = True
                # skip a string literal whole, so `"//"` is not read as a comment
                if s[i] == '"':
                    j = i + 1
                    while j < len(s) and s[j] != '"':
                        j += 2 if s[j] == '\\' else 1
                    i = j + 1
                else:
                    i += 1
        n += code
    return n


def sloc(root):
    files = [f for f in glob.glob(f'{root}/**/*.rs', recursive=True) if os.path.basename(f) != 'build.rs']
    return sum(sloc_of_text(open(f, errors='replace').read()) for f in files), len(files)


def crown_universe(prog):
    base = f'{CROWN}/{prog}/analysis_results'
    mut = json.load(open(f'{base}/mutability.json'))['fn_data']
    fat = json.load(open(f'{base}/fatness.json'))['fn_data']
    out = set()
    for fn, variables in mut.items():
        for var, labels in variables.items():
            if labels[:1] == ['Mut'] and fat.get(fn, {}).get(var, [])[:1] == ['Ptr']:
                out.add(f'{fn}::{var}')
    return out


def crown_before():
    rows = {}
    for line in open(f'{CROWN}/evaluation.tsv'):
        cells = line.strip().split(',')
        if cells and cells[0] in PROGRAMS:
            rows[cells[0]] = int(cells[1])
    return rows


def table(census, prog, name):
    path = f'{census}/{prog}.raw-boundary-{name}.tsv'
    return list(csv.DictReader(open(path), delimiter='\t')) if os.path.exists(path) else None


def pct(a, b):
    return f'{100.0 * a / b:.1f}%' if b else '---'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--census', required=True)
    ap.add_argument('--label', required=True)
    ap.add_argument('--solve', required=True)
    ap.add_argument('--record', default=RECORD)
    ap.add_argument('--measured', action='store_true')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    values, notes = {}, []

    # --- setup / sloc
    per = {}
    for p in PROGRAMS:
        per[p], files = sloc(f'{DISTRIBUTED}/{p}')
        derived, _ = sloc(f'{DERIVED}/{p}')
        values[f'setup.{key(p)}.sloc'] = per[p]
        notes.append(f'sloc\t{p}\tdistributed={per[p]} ({files} files)\tderived={derived}')
    largest = max(PROGRAMS, key=per.get)
    values['setup.programs'] = len(PROGRAMS)
    values['setup.sloc'] = sum(per.values())
    values['setup.largest-name'] = largest
    values['setup.largest-sloc'] = per[largest]
    values['rq3.rest.sloc'] = sum(v for p, v in per.items() if p != largest)

    # --- decl (CROWN's population), fail-closed on the BEFORE control
    before = crown_before()
    rates, tb, td = [], 0, 0
    for p in PROGRAMS:
        universe = crown_universe(p)
        if len(universe) != before[p]:
            sys.exit(f'decl control: {p} universe {len(universe)} != evaluation.tsv BEFORE {before[p]}')
        outcomes = table(a.census, p, 'subject-outcomes')
        if outcomes is None:
            sys.exit(f'{p}: no subject-outcomes table in {a.census}')
        by = {}
        for r in outcomes:
            by.setdefault(re.sub(r'#\d+(@d\d+)?$', '', r['subject_key']), []).append(r['delivery'])
        delivered = {d for d in universe if by.get(d) and all(x == 'realized-as-predicted' for x in by[d])}
        unmapped = sorted(d for d in universe if d not in by)
        tb, td = tb + len(universe), td + len(delivered)
        if universe:
            rates.append(100.0 * len(delivered) / len(universe))
        notes.append(f'decl\t{p}\tbefore={len(universe)}\tdelivered={len(delivered)}\tunmapped={len(unmapped)}'
                     + (f'\t{" ".join(unmapped)}' if unmapped else ''))
    if tb != sum(before.values()):
        sys.exit(f'decl control: corpus {tb} != {sum(before.values())}')
    notes.append(f'decl\ttotal\tbefore={tb}\tdelivered={td}\trate={pct(td, tb)}\t'
                 f'median={statistics.median(rates):.1f}%\t(a note: R768-2, the keys are the fan-out\'s)')

    # --- rq3 cost: the frame solve (analysis) and the census (emission, verification)
    wall = {}
    for line in open(f'{a.solve}/progress.jsonl'):
        e = json.loads(line)
        if e.get('event') == 'program' and e.get('status') == 'complete':
            wall[e['program']] = (e['wall_s'], e.get('peak_rss_kib'))
    missing = [p for p in PROGRAMS if p not in wall]
    if missing:
        sys.exit(f'solve {a.solve}: no complete record for {missing}')
    values['rq3.largest.analysis-s'] = round(wall[largest][0])
    values['rq3.rest.analysis-s'] = round(sum(w for p, (w, _) in wall.items() if p != largest))
    worker = {}
    for line in open(f'{a.census}/per-program.kv'):
        kv = dict(f.split('=', 1) for f in line.split() if '=' in f)
        if kv.get('program') in PROGRAMS and 'worker_wall_s' in kv:
            worker[kv['program']] = float(kv['worker_wall_s'])
    if len(worker) == len(PROGRAMS):
        values['rq3.largest.emit-s'] = round(worker[largest])
        values['rq3.rest.emit-s'] = round(sum(w for p, w in worker.items() if p != largest))
    else:
        notes.append(f'cost	emit-s not seeded: no worker_wall_s for {sorted(set(PROGRAMS) - set(worker))}')
    outcome = table(a.census, largest, 'outcome')
    if outcome:
        values['rq3.largest.verify-rounds'] = int(outcome[0]['verify_rounds'])
    notes.append(f'cost\tanalysis peak RSS (GiB)\t{largest}={wall[largest][1] / 1048576:.1f}\trest max='
                 f'{max(r for p, (_, r) in wall.items() if p != largest) / 1048576:.1f}')

    # --- write
    status = 'measured' if a.measured else 'pending'
    prov = (('' if a.measured else 'provisional: ') + f'agents/tools/seed_numbers.py over {a.label} '
            f'(census {os.path.basename(a.census.rstrip("/"))}, solve {os.path.basename(a.solve.rstrip("/"))})')
    lines = open(a.record).read().split('\n')
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
        cells[1], cells[2], cells[5] = str(values[cells[0]]), status, prov
        lines[i] = '| ' + ' | '.join(cells) + ' |'
    absent = sorted(set(values) - seen - {s.split(' ')[0] for s in skipped})
    for n in notes:
        print('#', n)
    for k in sorted(values):
        print(f'{k}\t{values[k]}')
    print(f'# seeded {len(seen)} rows as {status}; skipped {len(skipped)} (not pending): {skipped}; '
          f'absent from the record: {absent}')
    if not a.dry_run:
        open(a.record, 'w').write('\n'.join(lines))


if __name__ == '__main__':
    main()
