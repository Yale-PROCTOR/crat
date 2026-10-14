#!/usr/bin/env python3
"""Relays 126/127 (S32): seed rq3.<p>.analysis-s (20, one decimal; after rq3.rest.analysis-s) and setup.<p>.c-loc (20; after
setup.<p>.sloc), new and pending. emit-s not seeded (relay 127)."""
import csv, sys
NR = sys.argv[1]
A = {r['key']: r for r in csv.DictReader(open('scratch/analysis-fanout/r126/seed/candidates.tsv'), delimiter='\t') if r['key'].endswith('.analysis-s')}
L = {r['program']: r for r in csv.DictReader(open('scratch/analysis-fanout/r127/count/loc.tsv'), delimiter='\t')}
assert len(A) == 20 and len(L) == 20
key = lambda p: p.replace('.', '')
lines = open(NR).read().split('\n')
def idx(): return {l.split(' | ')[0][2:]: i for i, l in enumerate(lines) if l.startswith('| ')}
HA = ("at the frame of record (batch 56, borrow-ownership dc5b7d53c, landed 2026-10-09; its census ran cache-only on this solve's cache, "
      "so the analysis times of record are this solve's): the L01^14u solve worktrees/era5c-l01p14u-solve on host-a (2026-10-06/07; "
      "one program at a time, max_concurrent_models=1, worker --test-threads=1, brotli last); analysis-fanout 104 (relays 126/127, S32): "
      "progress.jsonl wall_s of the program's one complete record (the definition of rq3.largest/rest.analysis-s; seed_numbers.py's reader), "
      "printed at its source precision 0.1 s; the nineteen non-brotli values sum to 40,668.6 = rq3.rest.analysis-s 40669 as printed, brotli "
      "13068.0 = rq3.largest.analysis-s; the wall spans the whole supervisor call: the solve plus writing the cache entry, the worker's two "
      "streamed re-reads and the supervisor's re-verification (opt-level-0 build; over the nineteen 16,165 s = 39.7 % is that custody, "
      "report 104 Q1); independent verifier r126/vseed: all 20 values and sums reproduced; ")
HL = ("analysis-fanout 104 (relay 127, S32): cloc 2.00 (the copy analysis-fanout 016 used: scratch/analysis-fanout/rq3/cloc-2.00.pl, "
      "sha256 2e8d7d57...) code lines with 016's command `perl cloc-2.00.pl --quiet --csv --include-ext=c,h <dir>` (SUM row, code column), "
      "the rule of rq3.inator.<p>.loc: all .c/.h files of the program's C tree, crown-artifact/c-code/<dir> (tulipindicators: the artifact "
      "has none; upstream TulipCharts/tulipindicators @ 6b3ff6d (0.8.4), TI_BUILD 1537377628 = the translation's ti_build, 111/111 modules "
      "map); frame-independent (the C input); independent verifier r127/verify: all 20 reproduced with the same cloc (sha256 checked); ")
I = idx(); at = I['rq3.rest.analysis-s']
for n, p in enumerate(sorted(L)):
    k = f"rq3.{key(p)}.analysis-s"; r = A[k]; assert k not in I
    lines.insert(at + 1 + n, f"| {k} | {r['value']} | pending | n/a | seconds | {HA}{r['source']} |")
for p, r in L.items():
    I = idx(); sib = f"setup.{key(p)}.sloc"; k = f"setup.{key(p)}.c-loc"; assert sib in I and k not in I, (sib, k)
    extra = '' if int(r['inator_rule']) == int(r['translated_set']) else f"; the files c2rust translated (+ their in-tree #includes) count {r['translated_set']}: {r['note']}"
    lines.insert(I[sib] + 1, f"| {k} | {r['inator_rule']} | pending | n/a | count | {HL}{extra} |")
open(NR, 'w').write('\n'.join(lines)); print('ok')
