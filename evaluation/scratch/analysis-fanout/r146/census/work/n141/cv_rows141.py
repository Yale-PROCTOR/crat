#!/usr/bin/env python3
"""cv_rows141.py <base-census> <census>: r140 g088b/p7/cv_rows.py with both census dirs as arguments (r141): the raw ->
Option<&T> call-argument view adapter rows (main 212 optview.py's selection), compared on every column after the 13
frame-header columns."""
import collections, glob, os, sys
def sites(b):
    s = collections.Counter(); h = None
    for f in sorted(glob.glob(b + '/*.raw-boundary-adapters.tsv')):
        L = open(f).read().splitlines(); h = L[0].split('\t'); ix = {k: i for i, k in enumerate(h)}
        for l in L[1:]:
            x = l.split('\t')
            if x[ix['kind']] != 'placed' or x[ix['context']] != 'call-argument' or x[ix['found_form']] != 'raw': continue
            if x[ix['template']] in {'optional', 'c-raw-option-mut', 'c-raw-option-shared'} and x[ix['expected_form']].startswith('opt-ref'):
                s[tuple(x[13:])] += 1
    return s, h
A, B = sys.argv[1].rstrip('/'), sys.argv[2].rstrip('/')
a, h = sites(A); b, _ = sites(B)
print('header after frame cols:', h[13:])
print('rows base', sum(a.values()), 'census', sum(b.values()), 'identical on all non-frame columns:', a == b)
for k in sorted(a - b): print(' only-base', k[:8])
for k in sorted(b - a): print(' only-census', k[:8])
