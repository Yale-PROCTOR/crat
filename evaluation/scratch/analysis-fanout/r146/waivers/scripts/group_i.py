#!/usr/bin/env python3
"""group_i.py <census-dir>: relay 073 item 2 (i) -- the code generator's restructurings that have no receipt table, counted in
the census's emitted trees (<census>/emitted-trees/<p>/*.rs) against the derived input (rs-crown-derived/<p>/*.rs); a count is
emitted minus input (the generator's additions), per program. Patterns:
  arg-order-hoist   `let __crat_hoist_<lo>_<index>`  (bo_rewriter/arg_order_hoist.rs:126)
  field-read-hoist  `let __crat_hoist<n>`            (bo_rewriter/field_reference_ast.rs:840)
  take              `.take()`                        (the explicit transfer out of an owning field)
  reborrow-mut      `&mut *`                         (explicit mutable reborrow)
  reborrow-shared   `&*`                             (explicit shared reborrow)
  as-deref-mut      `.as_deref_mut()`                (optional mutable view)
  as-deref          `.as_deref()`                    (optional shared view)
  drop              `drop(`                          (explicit drop at a release site)"""
import collections, glob, os, re, sys
C = sys.argv[1]; DER = 'crat/benchmarks/rs-crown-derived'
PAT = {'arg-order-hoist': r'let (?:mut )?__crat_hoist_\d+_\d+\b', 'field-read-hoist': r'let (?:mut )?__crat_hoist\d+\b',
       'take': r'\.take\(\)', 'reborrow-mut': r'&mut \*', 'reborrow-shared': r'&\*', 'as-deref-mut': r'\.as_deref_mut\(\)',
       'as-deref': r'\.as_deref\(\)', 'drop': r'(?<![\w.])drop\('}
def text(paths): return ''.join(open(p, errors='replace').read() for p in paths if not p.endswith('build.rs'))
tot = collections.Counter(); progs = collections.Counter(); rows = []
for d in sorted(glob.glob(f'{C}/emitted-trees/*')):
    p = os.path.basename(d)
    em = text(glob.glob(f'{d}/**/*.rs', recursive=True)); inp = text(glob.glob(f'{DER}/{p}/**/*.rs', recursive=True))
    row = {}
    for k, r in PAT.items():
        n = len(re.findall(r, em)) - len(re.findall(r, inp))
        row[k] = n; tot[k] += n
        if n > 0: progs[k] += 1
    rows.append((p, row))
print('program\t' + '\t'.join(PAT))
for p, row in rows: print(p + '\t' + '\t'.join(str(row[k]) for k in PAT))
print('TOTAL\t' + '\t'.join(str(tot[k]) for k in PAT))
print('PROGRAMS\t' + '\t'.join(str(progs[k]) for k in PAT))
