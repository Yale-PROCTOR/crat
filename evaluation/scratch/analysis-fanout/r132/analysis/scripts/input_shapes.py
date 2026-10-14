#!/usr/bin/env python3
"""r132 analysis step (1): the input control's sites by shape, and the same shapes counted in every tree.

shape group = (kind, shape, dest, consumer) where shape is attribute.shape() (a:ref-binding / a:explicit-pointee /
a:explicit-subplace / a:autoref-receiver:<method> / b call) and consumer = the callee class for a call-arg:
  std:<method>        a core / std / alloc function or method (`Option::is_some`, `PartialEq::eq`, ...)
  bitfield:<method>   a c2rust-bitfields accessor (`BrotliDecoderStateStruct::set_is_metadata`, ...)
  program-fn          a function of the program
Writes input-shapes.tsv (all trees' counts per group) and prints the excluded control by reason.
"""
import csv, os, re, sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(__file__))
import attribute as AT  # noqa: E402

R = AT.R
A = AT.A
TREES = {'input': f'{R}/out/input', 'laertes_before': AT.BEFORE_L, 'laertes': f'{R}/out/laertes',
         'crown': f'{R}/out/crown', 'ours58': f'{R}/out/ours58', 'ours56': f'{R}/out/ours56'}


def consumer(g):
    if g['dest'] != 'call-arg':
        return '-'
    d = g['dest_detail']
    last2 = AT.norm_callee(d)
    if d.startswith(('std::', 'core::', 'alloc::')):
        return 'std:' + last2
    if re.search(r'::(set_)?(is_|size_nibbles|large_window|should_wrap|canny_)', d) and 'Struct::' in d:
        return 'bitfield:' + last2
    return 'program-fn'


def main():
    groups = defaultdict(Counter)
    example = {}
    progs = defaultdict(set)
    excl = defaultdict(Counter)
    for side, base in TREES.items():
        for p in AT.PROGRAMS:
            d = os.path.join(base, p)
            if AT.status(d) != 'ok':
                continue
            root = AT.tree_root(side, p, d)
            for g in AT.load(f'{d}/sites.tsv'):
                if not AT.is_ab(g):
                    continue
                if g['excluded'] == 'yes':
                    excl[side][g['excl_reason']] += 1
                    continue
                e = AT.expr_at(root, g['file'], g['line'], g['col'])
                sh = AT.shape(g, e)
                if sh.startswith('a:autoref-receiver'):
                    sh = 'a:autoref-receiver'
                k = (g['kind'], sh, g['dest'], consumer(g), 'static-base' if AT.static_base(root, e) else '-')
                groups[k][side] += 1
                if side == 'input':
                    progs[k].add(p)
                    if k not in example:
                        example[k] = f'{p}:{g["file"]}:{g["line"]}  {AT.src_line(root, g["file"], g["line"], 1)[:160]}'
    keys = sorted(groups, key=lambda k: (-groups[k]['input'], k))
    with open(f'{A}/input-shapes.tsv', 'w') as f:
        f.write('kind\tshape\tdest\tconsumer\tstatic_base\t' + '\t'.join(TREES) + '\tinput_programs\tinput_example\n')
        for k in keys:
            f.write('\t'.join(k) + '\t' + '\t'.join(str(groups[k][s]) for s in TREES) + '\t'
                    + ','.join(sorted(progs[k])) + '\t' + example.get(k, '-') + '\n')
        f.write('\n# excluded (the address idiom: the reference goes straight back to a raw pointer), by reason\n')
        reasons = sorted(set(r for c in excl.values() for r in c))
        f.write('excl_reason\t' + '\t'.join(TREES) + '\n')
        for r in reasons:
            f.write(r + '\t' + '\t'.join(str(excl[s][r]) for s in TREES) + '\n')
    tot = Counter()
    for k in keys:
        for s in TREES:
            tot[s] += groups[k][s]
    print('non-excluded a/b per tree:', dict(tot))
    for k in keys:
        if groups[k]['input']:
            print(groups[k]['input'], k, {s: groups[k][s] for s in TREES if s != 'input'})


if __name__ == '__main__':
    main()
