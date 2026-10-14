#!/usr/bin/env python3
"""leak141.py <census>: waiver.leak-parity under relay 139's ruling -- THE EMITTED PROGRAM'S IMPLICIT CLOSES, each counted
once by exit path (r140 vcensus's correction of 115's 18 -> 12). Per program:
  box   = <p>.raw-boundary-box-drops.tsv rows with receipt waiver-drop(<kind>) (the Box-drop observer, one row per local x site)
  rc    = <p>.return-certificate-receipts.tsv receipts naming waiver-drop(<kind>) (one per exit path of the certified return)
  ftx   = <p>.raw-boundary-field-transactions.tsv rows whose note carries waiver-drop-scope-exit=N, N summed (status applied, revert_status active)
  closes = ftx + max(box, rc): the observer rows and the return-certificate receipts name the same closes (quadtree: the 6
           observer rows are 6 locals at the closing brace; the 9 receipts are the 9 exit paths that drop them).
Each counted function must be emitted (not in <p>.raw-boundary-final-reverts.tsv). Also prints the census receipt's sum
(implicit_close_* lines) and every observer status. Read-only; fails closed via SystemExit."""
import csv, glob, os, re, sys, collections
csv.field_size_limit(10 ** 9)
C = sys.argv[1].rstrip('/')
rec = {}
for l in open(C + '/census-receipt.txt'):
    if l.startswith('implicit_close_'):
        k, v = l.strip().split('=', 1); rec[k] = v
def body(path):
    """rows of a status=/data= headed table (box-drops) or a plain tsv"""
    L = open(path).read().splitlines()
    head = {}
    while L and re.match(r'^[a-z_]+=', L[0]):
        k, v = L.pop(0).split('=', 1); head[k] = v
    rows = list(csv.DictReader(L, delimiter='\t')) if L else []
    return head, rows
tot = collections.Counter(); per = {}; statuses = {}
for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    reverted = set()
    fr = f'{C}/{p}.raw-boundary-final-reverts.tsv'
    if os.path.exists(fr):
        for r in csv.DictReader(open(fr), delimiter='\t'):
            reverted.add(r.get('function') or r.get('owner_fn') or '')
    box_fns, box = collections.Counter(), 0
    bf = f'{C}/{p}.raw-boundary-box-drops.tsv'
    if os.path.exists(bf):
        h, rows = body(bf)
        statuses[p] = h.get('status', '?') + (':' + h['detail'][:160] if 'detail' in h else '')
        for r in rows:
            if (r.get('receipt') or '').startswith('waiver-drop('):
                box += 1; box_fns[r['function']] += 1
    rc, rc_fns = 0, collections.Counter()
    rf = f'{C}/{p}.return-certificate-receipts.tsv'
    if os.path.exists(rf):
        for line in open(rf):
            n = len(re.findall(r'waiver-drop\([a-z-]+\)', line))
            if n:
                rc += n
    ftx = 0
    tf = f'{C}/{p}.raw-boundary-field-transactions.tsv'
    if os.path.exists(tf):
        for r in csv.DictReader(open(tf), delimiter='\t'):
            m = re.search(r'waiver-drop-scope-exit=(\d+)', '\t'.join(v or '' for v in r.values()))
            if m and int(m.group(1)) and r.get('status') == 'applied' and r.get('revert_status') == 'active':  # withdrawn = not in the emitted tree
                ftx += int(m.group(1))
    bad = [fn for fn in box_fns if fn in reverted]
    if bad:
        raise SystemExit(f'{p}: a counted close sits in a reverted function: {bad}')
    closes = ftx + max(box, rc)
    if closes or box or rc or ftx:
        per[p] = dict(box=box, rc=rc, ftx=ftx, closes=closes)
        tot.update(per[p])
print('census', C)
print('receipt', rec)
print('box-drop observer status', statuses)
for p, d in per.items():
    print(f'  {p:16} observer waiver rows {d["box"]:3}  return-certificate waiver receipts {d["rc"]:3}  field-transaction closes {d["ftx"]:3}  -> closes by exit path {d["closes"]}')
print(f'TOTAL closes by exit path (the ruling): {tot["closes"]}; receipt sum implicit_close_scope_exit={rec.get("implicit_close_scope_exit")} '
      f'(box-drops + return-certificate + field-transaction counted separately)')
