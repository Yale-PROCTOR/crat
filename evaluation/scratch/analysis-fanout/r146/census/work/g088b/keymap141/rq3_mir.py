#!/usr/bin/env python3
"""rq3-inator 017's MIR reader, IMPORTED VERBATIM (parse / fn_path / NONLOCAL) from
docs agents/artifacts/2026-10-06-rq3-inator-017/scripts/ownpref-slots.py (copy in rq3-017/),
so the `slot_kind_class_rq3` column uses exactly report 017's slot kinds:
parameter-derived = caller_derived_locals (formals + Use/Cast/non-local-call fixpoint),
then named local (var_debug_info), then compiler temp (incl. `_0`)."""
import collections, glob, os, re

_src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rq3-017', 'ownpref-slots.py')).read()
import csv
_ns = {'collections': collections, 'glob': glob, 'os': os, 're': re, 'csv': csv}
# take the definitions only: NONLOCAL, parse, shape, fn_path (everything before `mir = collections.defaultdict`)
_defs = _src.split('\nmir = collections.defaultdict(dict)')[0]
_defs = _defs.split('NAMES, MIR, ROW, OUTC, OUT = sys.argv[1:6]')[1]
exec(_defs, _ns)
parse, fn_path = _ns['parse'], _ns['fn_path']


def load(mir_dir):
    mir = collections.defaultdict(dict)
    for p in sorted(os.listdir(mir_dir)):
        for f in glob.glob(f'{mir_dir}/{p}/*.ElaborateDrops.after.mir'):
            mir[p][fn_path(f, p)] = parse(f)
    return mir


def classify(info, n):
    if n in info['caller']:
        return 'parameter-derived'
    return 'named local' if n in info['named'] else 'compiler temp'
