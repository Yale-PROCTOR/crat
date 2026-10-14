#!/usr/bin/env python3
"""r132: how much of the key-level `matched` is confirmed by the site's expression text (failure-mode check).
For each key, matched = min(after, before); text-confirmed = the multiset intersection of the normalised expression
texts (whitespace removed, `std::os::raw::` / `libc::` spelled alike). A matched pair whose texts differ is a possible
hidden swap (the tool removed one site and made another with the same key)."""
import os, re, sys
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(__file__))
import attribute as AT  # noqa: E402


def nt(e):
    e = re.sub(r'\s+', '', e)
    e = e.replace('std::os::raw::', 'libc::').replace('core::ffi::', 'libc::')
    return e


tot = defaultdict(Counter)
lines = []
for side, bdir in AT.SIDES.items():
    for p in AT.PROGRAMS:
        ad, bd = os.path.join(AT.OUT, side, p), os.path.join(bdir, p)
        if AT.status(ad) != 'ok' or AT.status(bd) != 'ok':
            continue
        ra, rb = AT.tree_root(side, p, ad), AT.tree_root(side, p, bd)
        A_ = defaultdict(Counter)
        B_ = defaultdict(Counter)
        for g in AT.load(f'{ad}/sites.tsv'):
            if AT.is_ab(g) and g['excluded'] == 'no':
                A_[AT.key(g)][nt(AT.expr_at(ra, g['file'], g['line'], g['col']))] += 1
        for g in AT.load(f'{bd}/sites.tsv'):
            if AT.is_ab(g) and g['excluded'] == 'no':
                B_[AT.key(g)][nt(AT.expr_at(rb, g['file'], g['line'], g['col']))] += 1
        m = conf = 0
        for k in set(A_) & set(B_):
            m += min(sum(A_[k].values()), sum(B_[k].values()))
            conf += sum((A_[k] & B_[k]).values())
        tot[side]['matched'] += m
        tot[side]['text_confirmed'] += conf
        if m != conf:
            lines.append(f'{side}\t{p}\tmatched={m}\ttext_confirmed={conf}')
out = ['side\tmatched\ttext_confirmed\tunconfirmed']
for s, c in tot.items():
    out.append(f'{s}\t{c["matched"]}\t{c["text_confirmed"]}\t{c["matched"] - c["text_confirmed"]}')
out += ['', '# programs with unconfirmed matches'] + lines
open(os.path.join(AT.A, 'match-check.tsv'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
