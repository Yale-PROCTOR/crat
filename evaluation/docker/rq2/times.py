#!/usr/bin/env python3
"""Table scale's running times, from the translate pass's own receipts.

The artifact's translate step runs, per program and one at a time, `jobcrat --pass translate --inplace` on the PREPARED
input (`jobcrat --pass prepare` runs before it and is not timed) and leaves in RECEIPTS / TIMES (default
$RESULTS/rq2/runs):
  <p>.receipt  the pass's receipt (--bo-receipt); its first line ends `solve=SolveReceipt { ..., solve_wall_s: "<s>" }`
  <p>.time     GNU time -v around the pass
  <p>.wall     optional: the wall in seconds around the same invocation; without it, GNU time's "Elapsed (wall clock)"
               line is read (it truncates to 10 ms)
The comparison tools' times come from THIRD_PARTY/times.tsv (key, trials, min, status: `min` is the time when the status
is `ok`; otherwise the status itself is the cell, e.g. `crash`).

Writes RESULTS/rq2/keys.txt (`key = value`; `skipped (<why>)` where a key was not produced) and RESULTS/rq2/runs.tsv.
The definitions, as the paper's values were derived:
  rq3.<p>.total-s              the wall of the translate pass: the solve and the code generation, in one process
  rq3.<p>.solve-s              the receipt's solve_wall_s
  rq3.<p>.codegen-s            total-s - solve-s
  rq3.total.{total,solve,codegen}-s   the sums of the unrounded per-program values
  rq3.largest.analysis-s       brotli's solve-s (the largest of the twenty by lines)
  the twenty print to 0.1 s and the eight to 0.01 s (`format(x, '.1f')` / `'.2f'`)
  rq3.<p>.{crown,laertes}-s, rq3.inator.<q>.{host,c2rust}-s   the third-party times, printed to 0.01 s; their totals sum
                               the printed values (Laertes's over the programs it completes)
  rq3.inator.<q>.with-c2rust-s c2rust-s + total-s, both as printed (the total the same way)
  rq3.inator.total.vs-inator-with-c2rust.factor   host-s total / with-c2rust-s total, rounded half up to a whole number
usage: times.py   (environment: SRC, RESULTS, RECEIPTS, TIMES, THIRD_PARTY; SMALL=1 under --small)"""
import os, re, sys
from decimal import Decimal as D, ROUND_HALF_UP

SRC = os.path.abspath(os.environ.get('SRC', os.getcwd()))
RESULTS = os.path.abspath(os.environ.get('RESULTS', os.path.join(SRC, 'results')))
OUT = os.path.join(RESULTS, 'rq2')
RECEIPTS = os.path.abspath(os.environ.get('RECEIPTS', os.path.join(OUT, 'runs')))
TIMES = os.path.abspath(os.environ.get('TIMES', os.path.join(OUT, 'runs')))
THIRD_PARTY = os.path.abspath(os.environ.get('THIRD_PARTY', os.path.join(RESULTS, 'third-party')))
SMALL = os.environ.get('SMALL', '0') == '1'

TWENTY = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
          'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
LARGE = ('lil', 'brotli')          # not translated under --small (nor by CROWN / Laertes there)
LARGEST = 'brotli'                 # the largest of the twenty by lines
EIGHT = ['ulidgen', 'leftpad', 'amp', 'nandc', 'rbtree', 'carrays', 'jccc', 'tisp']
INATOR_LARGE = ('rbtree', 'jccc', 'tisp')    # &inator does not run them under --small
SOLVE_RE = re.compile(r'solve_wall_s: "?([0-9.]+)')
ELAPSED_RE = re.compile(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)')
NUM_RE = re.compile(r'[0-9]+(\.[0-9]+)?')
STATUS = 'no total (a status in place of a time)'


def K(p):
    return p.replace('.', '')


def dec(cell):
    """A printed cell as a Decimal, or None when it is a word (`crash`, `skipped (...)`, `failed (...)`)."""
    return D(cell) if NUM_RE.fullmatch(cell) else None


def reason(*cells):
    """Why a value built from these cells is not a number: the first `failed` / `skipped` cell, else STATUS (a status
    word such as `crash` where the paper has a time; compare.py reads it as a difference, not as skipped)."""
    words = [c for c in cells if dec(c) is None]
    return next((c for c in words if c.startswith(('failed', 'skipped', 'no total'))), STATUS)


def show(x, places):
    return format(float(x), f'.{places}f') if isinstance(x, D) else x


def read_run(p):
    """(wall, solve) as Decimals, or one `skipped (...)` / `failed (...)` word for both; and runs.tsv's row."""
    rec, tim, wal = (os.path.join(RECEIPTS, f'{p}.receipt'), os.path.join(TIMES, f'{p}.time'),
                     os.path.join(TIMES, f'{p}.wall'))
    row = {'program': p}
    if not os.path.exists(rec) and not os.path.exists(tim):
        why = 'skipped (--small)' if SMALL and p in LARGE else 'skipped (not run)'
        return why, why, row
    tv = open(tim, errors='replace').read() if os.path.exists(tim) else ''
    sig = re.search(r'Command terminated by signal (\d+)', tv)      # GNU time then still prints "Exit status: 0"
    m = re.search(r'Exit status: (\d+)', tv)
    row['exit'] = f'signal {sig.group(1)}' if sig else (m.group(1) if m else '-')
    m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', tv)
    row['max_rss_gib'] = f'{int(m.group(1)) / 1048576:.1f}' if m else '-'
    first = open(rec, errors='replace').readline() if os.path.exists(rec) else ''
    kv = dict(re.findall(r'(\w+)=(\S+)', first.split(' solve=')[0]))
    for k in ('outcome', 'verify_rounds', 'reverted', 'files_changed'):
        row[k] = kv.get(k, '-')
    wall = None
    if os.path.exists(wal):
        row['wall_from'] = 'wall'
        w = open(wal, errors='replace').read().split()
        wall = D(w[0]) if w and NUM_RE.fullmatch(w[0]) else None
    else:
        row['wall_from'] = 'time'
        m = ELAPSED_RE.search(tv)
        if m:
            wall = D(0)
            for part in m.group(1).split(':'):
                wall = wall * 60 + D(part)
    sw = SOLVE_RE.search(first)
    if not tv:
        why = 'failed (no time file)'
    elif row['exit'] != '0':
        why = f"failed (exit {row['exit']})"
    elif kv.get('outcome') != 'emitted':
        why = f"failed (outcome {kv.get('outcome', 'missing')})"
    elif not sw:
        why = 'failed (no solve time in the receipt)'
    elif wall is None:
        why = 'failed (no wall time)' if row['wall_from'] == 'time' else 'failed (unreadable wall file)'
    else:
        solve = D(str(float(sw.group(1))))
        row['wall_s'], row['solve_wall_s'] = str(wall), str(solve)
        return wall, solve, row
    return why, why, row


def third_party():
    """{key: cell} from times.tsv (the time printed to 0.01 s, or the status word), or None when it is absent."""
    f = os.path.join(THIRD_PARTY, 'times.tsv')
    if not os.path.exists(f):
        return None
    cells = {}
    for n, line in enumerate(open(f, encoding='utf-8'), 1):
        c = [x.strip() for x in line.rstrip('\n').split('\t')]
        if c[0] in ('', 'key') or c[0].startswith('#'):
            continue
        if len(c) < 4:
            print(f'rq2: times.tsv line {n} has {len(c)} of 4 columns; read as absent', file=sys.stderr)
            continue
        key, _trials, low, status = c[:4]
        if status in ('ok', ''):
            cells[key] = format(float(low), '.2f') if NUM_RE.fullmatch(low) else 'failed (times.tsv: ok without a time)'
        else:
            cells[key] = status
    return cells


def measured(v, keys, places):
    """Per program: total-s, solve-s, codegen-s from the runs; returns the unrounded values for the totals."""
    tot = {'total': [], 'solve': [], 'codegen': []}
    rows = []
    for key, p in keys:
        wall, solve, row = read_run(p)
        rows.append(row)
        code = wall - solve if isinstance(wall, D) else wall
        for fam, x in (('total', wall), ('solve', solve), ('codegen', code)):
            v[f'{key}.{fam}-s'] = show(x, places)
            tot[fam].append(x)
    return tot, rows


def unrounded_total(xs, places):
    words = [x for x in xs if not isinstance(x, D)]
    return reason(*words) if words else show(sum(xs, D(0)), places)


def printed_total(cells, completing=False):
    """The sum of printed cells; with `completing`, a status word (e.g. `crash`) is left out of the sum."""
    words = [c for c in cells if dec(c) is None and not (completing and not c.startswith(('skipped', 'failed')))]
    return reason(*words) if words else format(sum((dec(c) for c in cells if dec(c) is not None), D(0)), '.2f')


def main():
    os.makedirs(OUT, exist_ok=True)
    v = {}
    tp = third_party()

    def tp_cell(key, p):
        if tp is None:
            return 'skipped (no third-party)'
        left_out = p in LARGE or (key.endswith('.host-s') and p in INATOR_LARGE)
        return tp.get(key, 'skipped (--small)' if SMALL and left_out else 'skipped (not in times.tsv)')

    # the twenty (0.1 s), and CROWN's and Laertes's times on them
    tot, rows = measured(v, [(f'rq3.{K(p)}', p) for p in TWENTY], 1)
    for fam in tot:
        v[f'rq3.total.{fam}-s'] = unrounded_total(tot[fam], 1)
    v['rq3.largest.analysis-s'] = v[f'rq3.{K(LARGEST)}.solve-s']
    for tool in ('crown', 'laertes'):
        cells = [tp_cell(f'rq3.{K(p)}.{tool}-s', p) for p in TWENTY]
        for p, c in zip(TWENTY, cells):
            v[f'rq3.{K(p)}.{tool}-s'] = c
        v[f'rq3.total.{tool}-s'] = printed_total(cells, completing=(tool == 'laertes'))
    if SMALL:      # the totals over the twenty need lil and brotli
        for k in ['rq3.total.total-s', 'rq3.total.solve-s', 'rq3.total.codegen-s', 'rq3.largest.analysis-s',
                  'rq3.total.crown-s', 'rq3.total.laertes-s']:
            v[k] = 'skipped (--small)'

    # the eight (0.01 s), with c2rust's translation and &inator's time
    tot8, rows8 = measured(v, [(f'rq3.inator.{q}', q) for q in EIGHT], 2)
    rows += rows8
    for fam in tot8:
        v[f'rq3.inator.total.{fam}-s'] = unrounded_total(tot8[fam], 2)
    for fam in ('c2rust', 'host'):
        cells = [tp_cell(f'rq3.inator.{q}.{fam}-s', q) for q in EIGHT]
        for q, c in zip(EIGHT, cells):
            v[f'rq3.inator.{q}.{fam}-s'] = c
        v[f'rq3.inator.total.{fam}-s'] = printed_total(cells)
    for q in EIGHT + ['total']:
        c, t = v[f'rq3.inator.{q}.c2rust-s'], v[f'rq3.inator.{q}.total-s']
        v[f'rq3.inator.{q}.with-c2rust-s'] = format(dec(c) + dec(t), '.2f') if dec(c) is not None and dec(t) is not None else reason(t, c)
    h, w = v['rq3.inator.total.host-s'], v['rq3.inator.total.with-c2rust-s']
    v['rq3.inator.total.vs-inator-with-c2rust.factor'] = (
        str((dec(h) / dec(w)).quantize(D(1), rounding=ROUND_HALF_UP)) if dec(h) is not None and dec(w) is not None
        else reason(h, w))

    with open(os.path.join(OUT, 'keys.txt'), 'w') as f:
        for k in sorted(v):
            f.write(f'{k} = {v[k]}\n')
    cols = ['program', 'exit', 'outcome', 'verify_rounds', 'reverted', 'files_changed', 'wall_s', 'wall_from',
            'solve_wall_s', 'max_rss_gib']
    with open(os.path.join(OUT, 'runs.tsv'), 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for r in rows:
            f.write('\t'.join(str(r.get(c, '-')) for c in cols) + '\n')
    n = len(v)
    s = sum(1 for x in v.values() if x.startswith('skipped'))
    print(f'rq2: {n} keys, {n - s} produced, {s} skipped -> {os.path.join(OUT, "keys.txt")}')


if __name__ == '__main__':
    main()
