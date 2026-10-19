#!/usr/bin/env python3
"""Table scale from rq2's keys (times.py must have run) and rq1's size keys:
  results/tables/scale.csv   both halves, one row per program and the totals:
                             the twenty: Rust lines, Laertes, CROWN, ours;
                             the eight: C lines, &inator, C2Rust + ours, ours
  results/tables/scale.tex   rq2's produced keys as the paper's numbers.tex rows (skipped keys are absent)
The sizes (setup.<p>.sloc, setup.sloc, rq3.inator.<q>.loc, rq3.inator.total.loc) are rq1's keys; without
results/rq1/keys.txt their cells read `skipped (rq1 not run)`.
usage: table_scale.py   (environment: SRC, RESULTS)"""
import csv, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from times import EIGHT, K, OUT, RESULTS, TWENTY  # noqa: E402

TABLES = os.path.join(RESULTS, 'tables')
NUMBER_RE = re.compile(r'^(-?)(\d+)(\.\d+)?(%?)$')


def read_keys(path):
    v = {}
    if os.path.exists(path):
        for line in open(path, encoding='utf-8'):
            if ' = ' in line:
                k, x = line.rstrip('\n').split(' = ', 1)
                v[k.strip()] = x.strip()
    return v


def print_form(value):
    """A plain number prints with thousands separators in its integer part; any other value as recorded."""
    m = NUMBER_RE.match(value.strip())
    if not m:
        return value
    sign, whole, frac, pc = m.groups()
    return f'{sign}{int(whole):,}{frac or ""}{pc}'


def tex_escape(s):
    return (s.replace('\\', r'\textbackslash{}').replace('%', r'\%').replace('&', r'\&').replace('#', r'\#')
            .replace('_', r'\_').replace('^', r'\^{}').replace('~', r'\textasciitilde{}').replace('{', r'\{')
            .replace('}', r'\}'))


def main():
    os.makedirs(TABLES, exist_ok=True)
    v = read_keys(os.path.join(OUT, 'keys.txt'))
    rq1 = os.path.join(RESULTS, 'rq1', 'keys.txt')
    size = read_keys(rq1)
    no_size = 'skipped (rq1 not run)'
    rows = []
    for p in TWENTY + ['total']:
        k = 'rq3.total' if p == 'total' else f'rq3.{K(p)}'
        sloc = size.get('setup.sloc' if p == 'total' else f'setup.{K(p)}.sloc', no_size if not size else '-')
        rows.append(['twenty', p, sloc, v[f'{k}.laertes-s'], v[f'{k}.crown-s'], '', '', v[f'{k}.total-s']])
    for q in EIGHT + ['total']:
        k = f'rq3.inator.{q}'
        rows.append(['eight', q, size.get(f'{k}.loc', no_size if not size else '-'), '', '', v[f'{k}.host-s'],
                     v[f'{k}.with-c2rust-s'], v[f'{k}.total-s']])
    with open(os.path.join(TABLES, 'scale.csv'), 'w', newline='') as f:
        w = csv.writer(f, lineterminator='\n')
        w.writerow(['half', 'program', 'lines', 'laertes_s', 'crown_s', 'inator_s', 'c2rust_plus_ours_s', 'ours_s'])
        w.writerows(rows)
    with open(os.path.join(TABLES, 'scale.tex'), 'w') as f:
        f.write("% scale: rq2's produced keys in the paper's numbers.tex form (skipped keys are absent)\n")
        for k in sorted(v):
            if not v[k].startswith('skipped'):
                f.write(f'\\@namedef{{nr@{k}}}{{\\nrMeasured{{{tex_escape(print_form(v[k]))}}}}}\n')
    print(f'rq2: Table scale -> {os.path.join(TABLES, "scale.csv")}, scale.tex')


if __name__ == '__main__':
    main()
