#!/usr/bin/env python3
"""r132 analysis step (4): quoted tool-made lines per tool and kind (and the input's three control shapes) -> quotes.md"""
import csv, os, sys
from collections import defaultdict
sys.path.insert(0, os.path.dirname(__file__))
import attribute as AT  # noqa: E402

A = AT.A


def root_of(side, p):
    d = os.path.join(AT.OUT, side, p) if side != 'laertes_before' else os.path.join(AT.BEFORE_L, p)
    return AT.tree_root(side, p, d)


def lines(root, f, line, n):
    path = os.path.join(root, f)
    ls = open(path, errors='replace').read().split('\n')
    i = int(line) - 1
    return path, '\n'.join(ls[i:i + n])


def pick(rows, k=3):
    """up to k rows, from different programs first"""
    seen, out = set(), []
    for r in rows:
        if r['program'] not in seen:
            out.append(r)
            seen.add(r['program'])
        if len(out) == k:
            return out
    for r in rows:
        if r not in out:
            out.append(r)
        if len(out) == k:
            break
    return out


def main():
    md = ['# r132 quoted lines (relay 132)', '',
          'Every quote: the absolute path:line of the emitted (or input) file, the site\'s kind / shape / destination, '
          'and the source lines from the site\'s line. Tool-made = no counterpart in the tool\'s own before tree '
          '(attribute.py). Ours = batch 58 (b52e02437).', '']
    # input control
    md += ['## The input control (benchmarks/rs-crown): c2rust\'s own references from raw places', '']
    inp = []
    for p in AT.PROGRAMS:
        d = os.path.join(AT.OUT, 'input', p)
        for g in AT.load(f'{d}/sites.tsv'):
            if AT.is_ab(g) and g['excluded'] == 'no':
                inp.append(dict(g, program=p))
    want = [('ref-binding (let ref mut freshN = <place through a raw pointer>)', lambda g: g['dest'] == 'decl', 'json.h'),
            ('autoref receiver of Option::is_some on a fn-pointer field reached through a raw pointer',
             lambda g: g['dest_detail'].endswith('is_some'), 'lodepng'),
            ('autoref receiver of a c2rust-bitfields accessor on a struct reached through a raw pointer',
             lambda g: 'set_is_metadata' in g['dest_detail'], 'brotli')]
    for title, f, prefer in want:
        cand = [g for g in inp if f(g)]
        cand.sort(key=lambda g: g['program'] != prefer)
        g = cand[0]
        path, txt = lines(root_of('input', g['program']), g['file'], g['line'], 2)
        md += [f'- **{title}** ({len(cand)} sites) — `{path}:{g["line"]}` ({g["kind"]}, dest {g["dest"]} '
               f'{g["dest_detail"]})', '', '```rust', txt, '```', '']
    for side, title in [('laertes', 'Laertes (artifact trees; before = the artifact\'s Laertes BEFORE trees)'),
                        ('crown', 'CROWN (rs-crown-transformed; before = rs-crown)'),
                        ('ours58', 'Ours, batch 58 (before = rs-crown)')]:
        f = f'{A}/toolmade-ours58-receipts.tsv' if side == 'ours58' else f'{A}/toolmade-{side}.tsv'
        rows = list(csv.DictReader(open(f), delimiter='\t'))
        md += [f'## {title}', '']
        by = defaultdict(list)
        for r in rows:
            k = r['shape'] if r['shape'].startswith('a:') else r['call_class']
            if k.startswith('a:autoref-receiver'):
                k = 'a:autoref-receiver'
            by[(k, r['counted'])].append(r)
        for (k, counted), rs in sorted(by.items(), key=lambda kv: (kv[0][1] != 'yes', -len(kv[1]))):
            md += [f'### {k}{"" if counted == "yes" else " (NOT counted: static base / round trip to raw)"} — '
                   f'{len(rs)} tool-made', '']
            for r in pick(rs):
                path, txt = lines(root_of(side, r['program']), r['file'], r['line'], 2)
                extra = f'; receipts {r["receipts"]}' if side == 'ours58' else ''
                md += [f'- `{path}:{r["line"]}` — {r["kind"]}, dest {r["dest_class"]} {r["dest_detail"]}, formal '
                       f'`{r["formal_ty"]}`, null_dom {r["null_dom"]}, from_idiom {r["from_idiom"]}{extra}', '',
                       '```rust', txt, '```', '']
    open(f'{A}/quotes.md', 'w').write('\n'.join(md) + '\n')


if __name__ == '__main__':
    main()
