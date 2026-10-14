#!/usr/bin/env python3
"""ec3_keys.py <census_dir> -- read-only: the EC3 keys of Appendix E from one raw-boundary census.

Sources (per program P, written by bo_c1::raw_boundary_wave2_corpus_census):
  P.raw-boundary-delivery-custody.json  comparison.delivered_by_ledger / delivered_by_tree / issues / observations
  P.raw-boundary-bridge-custody.json    comparison.applied_receipts / pending_receipts / files[*].rows / files[*].tree_only
  per-program.kv                        raw_boundary_realized_subjects (cross-check of the ledger set)
Identity key = (program, subject_key) for delivery; (program, receipt_key) for bridges.
Permutation counts are NOT in a census's outputs (cargo tests only) -> printed as 'not-derivable'.
"""
import glob, json, os, sys
from collections import Counter

d = sys.argv[1]
progs = sorted(os.path.basename(f)[: -len('.raw-boundary-delivery-custody.json')]
               for f in glob.glob(os.path.join(d, '*.raw-boundary-delivery-custody.json')))

L, T = set(), set()
issues = Counter()
states = Counter()
for p in progs:
    c = json.load(open(os.path.join(d, f'{p}.raw-boundary-delivery-custody.json')))['comparison']
    L |= {(p, k) for k in c['delivered_by_ledger']}
    T |= {(p, k) for k in c['delivered_by_tree']}
    for i in c['issues']:
        # own issues are 'delivery-custody:<class>:...'; 'bridge-custody:*' lines are the
        # invalidation copy of the bridge comparison's issues (bo_c1.rs:13432-13434, 625-640)
        issues[':'.join(i.split(':')[:2])] += 1
    for o in c['observations']:
        states[o['state']] += 1

# bridge custody: ledger = applied receipts (terminal+applied events of the three custody kinds);
# tree = applied receipts the parser-side matcher found rendered (matched-raw / matched-c9),
# plus tree-only witnesses (rendered bridges no receipt claims).
BL, BT, BTO, BP, BPW = set(), set(), 0, set(), set()
bstat = Counter()
for p in progs:
    c = json.load(open(os.path.join(d, f'{p}.raw-boundary-bridge-custody.json')))['comparison']
    applied = set(c['applied_receipts'])
    BL |= {(p, k) for k in applied}
    BP |= {(p, k) for k in c['pending_receipts']}
    for f in c['files'].values():
        BTO += len(f['tree_only'])
        for r in f['rows']:
            bstat[r['status']] += 1
            if r['identity'] in applied and r['status'] in ('matched-raw', 'matched-c9'):
                BT.add((p, r['identity']))
            if r['status'] == 'waived-pending':
                BPW.add((p, r['identity']))

kv_realized = kv_raw = kv_applied = 0
for line in open(os.path.join(d, 'per-program.kv')):
    row = dict(t.split('=', 1) for t in line.split()[1:] if '=' in t)
    kv_realized += int(row.get('raw_boundary_realized_subjects', 0) or 0)
    kv_raw += int(row.get('raw_boundary_realized_model_raw_family', 0) or 0)
    kv_applied += int(row.get('raw_boundary_bridge_applied_events', 0) or 0)

print(f'programs\t{len(progs)}')
print(f'ec3.ledger\t{len(L)}')
print(f'ec3.tree\t{len(T)}')
print(f'ec3.reconciled\t{len(L & T)}')
print(f'census.custody-mismatch\t{len(L ^ T)}\t(ledger-only {len(L - T)}, tree-only {len(T - L)})')
print(f'ec3.bridge-ledger\t{len(BL)}')
print(f'ec3.bridge-tree\t{len(BT)}\t(+ tree-only witnesses {BTO}; receipt-without-render {len(BL - BT)})')
print('ec3.perm-detected\tnot-derivable (cargo tests only)')
print('ec3.perm-total\tnot-derivable (cargo tests only)')
print(f'# cross-check: per-program.kv realized_subjects {kv_realized} + realized_model_raw_family {kv_raw} = {kv_realized + kv_raw} (ledger {len(L)})')
print(f'# per-program.kv bridge_applied_events (all bridge kinds) = {kv_applied}; custody covers only the 3 custody kinds')
print(f'# delivery-custody issues by class: {dict(issues)}')
print(f'# delivery-custody observation states: {dict(states)}')
print(f'# bridge rows by status: {dict(bstat)}; pending receipts {len(BP)} (waived-pending rendered {len(BPW)})')
for p, k in sorted(L ^ T):
    print(f'# mismatch\t{p}\t{k}\t{"ledger-only" if (p, k) in L else "tree-only"}')
for p, k in sorted(BL - BT):
    print(f'# bridge-unrendered\t{p}\t{k}')
