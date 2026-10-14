#!/usr/bin/env python3
"""group_ii.py <census-dir>: relay 073 item 2 (ii) -- the re-spellings, from the census's receipt tables, with main 134f's
definitions (catalogue_check.py: distinct sites, or the terminal `applied` obligations), and the number of programs per kind."""
import collections, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import load_rejoin
D = sys.argv[1]
def load(t): return load_rejoin(D, t)  # r146: the rejoined reader (117's value fix), not 054's csv line reader
def report(kind, table, keys):
    progs = {k[0] for k in keys}
    print(f'{kind}\t{table}\t{len(keys)}\t{len(progs)}')
print('kind\treceipt table\tsites\tprograms')
ad = {(r['program'], r['site']) for r in load('raw-boundary-adapters') if r['kind'] == 'placed'}
report('call-site-adapter', 'raw-boundary-adapters (kind=placed; distinct sites)', ad)
b = load('raw-boundary-bridge-receipts')
pos = {(r['program'], r['site_key']) for r in b}
term = {(r['program'], r['site_key']): r for r in b if r['stage'] == 'terminal'}
plan = {(r['program'], r['site_key']): r for r in b if r['stage'] == 'plan'}
zero = {k for k in pos if (term.get(k) or plan.get(k) or {}).get('bridge_kind') == 'interface-call-zero-syntax'}
report('bridge', 'raw-boundary-bridge-receipts (positions)', pos)
report('bridge.with-syntax', 'raw-boundary-bridge-receipts (positions, not interface-call-zero-syntax)', pos - zero)
report('bridge.applied', 'raw-boundary-bridge-receipts (terminal applied)', {k for k, r in term.items() if r['state'] == 'applied'})
ex = {(r['program'], r['function']) for r in load('raw-boundary-exposure') if r['surface_plan'] in ('positive-seed-entry-shim', 'fnptr-web-raw-wrapper')}
report('exported-entry-wrapper', 'raw-boundary-exposure (surface_plan entry shim or fn-pointer-web wrapper; functions)', ex)
def term_applied(t):
    return {(r['program'], r['obligation_key']) for r in load(t) if r.get('stage') == 'terminal' and r.get('state') == 'applied'}
for kind, t in (('option-presentation', 'option-presentation-receipt'), ('declaration-reshape', 'declaration-shape-receipt'),
                ('slice-construction', 'slice-construction-receipt'), ('return-bridge', 'outbound-return-bridge'),
                ('unsafe-context', 'raw-boundary-unsafe-context-presentation'), ('mechanical-obligation', 'raw-boundary-mechanical-obligations')):
    report(kind, t + ' (terminal applied)', term_applied(t))
pr = {(r['program'], r['site']) for r in load('raw-boundary-pairs') if r['verdict'] == 'overlapping' and r['role'] == 'raw-view'}
report('pair-raw-view', 'raw-boundary-pairs (verdict overlapping, role raw-view; distinct argument sites)', pr)
ft = load('raw-boundary-field-transactions')
report('field-transaction', 'raw-boundary-field-transactions (status applied; fields)', {(r['program'], r['struct'], r['field']) for r in ft if r['status'] == 'applied'})
report('function-revert', 'raw-boundary-final-reverts (kind function)', {(r['program'], r.get('owner') or r.get('function') or r.get('subject') or str(i)) for i, r in enumerate(load('raw-boundary-final-reverts')) if r['kind'] == 'function'})
