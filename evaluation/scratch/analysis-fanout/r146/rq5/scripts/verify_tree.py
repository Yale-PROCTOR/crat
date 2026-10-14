"""r141: verify_frame13.py <census> [--tree-custody] (with the flag, delivered = by the emitted tree; without it, the r140 copy unchanged)
verify_frame13.py <census>: relay 060 item 2 -- main 134f's verify.* definitions re-read on a census (analysis-fanout 040):
rejected-programs = programs with raw_boundary_reverted_count > 0; unit-lost-rate = reverted declarations / delivered;
wholecrate-lost-rate = delivered in those programs / all delivered. Beside them, the compiler-rejected-only variants
(programs with a compiler-diagnostics row) and the planning-time reverts (reverted in a program with no diagnostic)."""
import csv, glob, collections, re, sys, json, os
csv.field_size_limit(10 ** 9)
F = sys.argv[1]
LO = set()  # r141: --tree-custody = the count by the emitted tree (delivery-custody ledger-only rows are not delivered)
if '--tree-custody' in sys.argv[2:]:
    for f in sorted(glob.glob(F + '/*.raw-boundary-delivery-custody.json')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        c = json.load(open(f))['comparison']
        led, tree = set(c.get('delivered_by_ledger') or []), set(c.get('delivered_by_tree') or [])
        if tree - led:
            raise SystemExit('tree-only rows in ' + p)
        LO |= {(p, k) for k in led - tree}
rc = {}
for l in open(F + '/per-program.kv'):
    p = re.search(r'raw_boundary_program=(\S+)', l) or re.search(r'program=(\S+)', l)
    r = re.search(r'raw_boundary_reverted_count=(\d+)', l)
    if p and r: rc[p.group(1)] = int(r.group(1))
dl = collections.Counter(); rv = collections.Counter()
for f in glob.glob(F + '/*.raw-boundary-subject-outcomes.tsv'):
    p = f.split('/')[-1].split('.raw')[0]
    for r in csv.DictReader(open(f), delimiter='\t'):
        if r['delivery'] == 'realized-as-predicted' and (p, r['subject_key']) not in LO: dl[p] += 1
        if r['delivery'] == 'reverted': rv[p] += 1
diag = {f.split('/')[-1].split('.raw')[0] for f in glob.glob(F + '/*.raw-boundary-compiler-diagnostics.tsv')
        if any(True for _ in csv.DictReader(open(f), delimiter='\t'))}
D = sum(dl.values()); rej = [p for p in rc if rc[p] > 0]; comp = [p for p in rej if p in diag]
print('reverted_count>0:', {p: rc[p] for p in rej}, '; reverted rows:', dict(rv))
print(f'verify.rejected-programs {len(rej)}; verify.unit-lost-rate {sum(rc[p] for p in rej)}/{D} = {100*sum(rc[p] for p in rej)/D:.2f} %; '
      f'verify.wholecrate-lost-rate {sum(dl[p] for p in rej)}/{D} = {100*sum(dl[p] for p in rej)/D:.2f} %')
print(f'compiler-rejected only ({comp}): programs {len(comp)}; rows {sum(rc[p] for p in comp)} = {100*sum(rc[p] for p in comp)/D:.2f} %; '
      f'wholecrate {sum(dl[p] for p in comp)} = {100*sum(dl[p] for p in comp)/D:.2f} %; planning-time (no diagnostic) {sum(rc[p] for p in rej if p not in diag)}')
print('delivered by program:', dict(sorted(dl.items())), '; ledger-only removed:', sorted(LO))
