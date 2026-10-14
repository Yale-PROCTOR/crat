#!/usr/bin/env python3
"""write_keys.py: new-keys.tsv for the objective-order ablation (relay 146 item 2), from the run outputs in ../runs
(main's custody_count / clause57 / rate956 / box-by-form / kind_moves / census_by_identity, and ablation.py)."""
import json, re, os
R = 'scratch/analysis-fanout/r146/ablation'
RUN = R + '/runs'
HEADS = {'batch60': ('7682bb8a0', 'main 223'), 'batch60s': ('4eb66851b', 'main 224'), 'batch60sp': ('32d966b9f', 'main 225')}
def fail(m): raise SystemExit('FAIL: ' + m)
def rd(f): return open(os.path.join(RUN, f)).read()
def sp(d): return ', '.join(f'{p} {n}' for p, n in sorted(d.items(), key=lambda x: (-x[1], x[0])))
rows = []
def key(k, v, layer, unit, cause):
    for ch in '\t\n|':
        if ch in cause or ch in str(v): fail(f'bad char in {k}')
    rows.append((k, str(v), layer, unit, cause))
ph = rd('perhead.txt'); box = rd('box.txt')
for h, (hsh, rep) in HEADS.items():
    cust = rd(f'{h}-custody.txt'); rate = rd(f'{h}-rate956.txt'); c57 = rd(f'{h}-clause57.txt')
    m = re.search(r'count by the emitted tree: (\d+) \(realized (\d+) - (\d+) \+ (\d+)\)', cust) or fail('custody ' + h)
    tree, led, lo, to = map(int, m.groups())
    old = re.search(r'old: (\d+) / (\d+) = ([\d.]+) %\s+\(decided safe (\d+) less R454 (\d+)\)', rate) or fail('old ' + h)
    d6 = re.search(r'D6:\s+(\d+) / (\d+) = ([\d.]+) %\s+\(\+(\d+)', rate) or fail('d6 ' + h)
    r9 = re.search(r'R956-1 \(with D6\): (\d+) / (\d+) = ([\d.]+) %\s+\(less the first-order holds N=(\d+)\)', rate) or fail('r956 ' + h)
    if int(old.group(1)) != tree: fail('rate delivered != tree ' + h)
    hl = re.search(rf'^{h} safe (\d+) delivered (\d+) first-order (\d+) (\{{.*\}})\n  holds by program (\{{.*\}})\n  delivered by program (\{{.*\}})', ph, re.M) or fail('perhead ' + h)
    held_cls = eval(hl.group(4)); held_p = eval(hl.group(5)); dp = eval(hl.group(6))
    if int(hl.group(3)) != int(r9.group(4)) or int(hl.group(1)) != int(old.group(2)): fail('perhead mismatch ' + h)
    bx = re.search(rf'^{h} box (\d+) (\{{.*?\}}) (\{{.*\}})$', box, re.M) or fail('box ' + h)
    bfam = eval(bx.group(2)); bprog = eval(bx.group(3))
    pre = f'ablation.order.{h}.'
    tag = f'{h} census (head {hsh}, {rep}'
    key(pre + 'delivered', tree, 'delivered', 'count',
        f'{tag}): delivered by the emitted tree (custody_count.py) = {tree}; the ledger = {led} (ledger-only {lo}, tree-only {to}, so the ledger figure equals the tree); by program {sp(dp)}')
    key(pre + 'safe-decisions', int(old.group(2)), 'decided', 'count',
        f'{tag}): decided safe {old.group(4)} less R454 {old.group(5)} = {old.group(2)} (the old-definition denominator, rate956.py); D6 adds {d6.group(4)} compile-check reverts outside the safe families; the R956-1 with D6 denominator is {r9.group(2)} = {d6.group(2)} less the first-order holds {r9.group(4)}')
    key(pre + 'rate', f'{float(r9.group(3)):.2f} %', 'delivered', 'percent',
        f'{tag}): R956-1 with D6 = {tree} / {r9.group(2)} = {float(r9.group(3)):.2f} % (rate956.py over clause57.py with base batch56 and record frame11, as main runs them)')
    key(pre + 'old-rate', f'{float(old.group(3)):.2f} %', 'delivered', 'percent',
        f'{tag}): old definition = {tree} / {old.group(2)} = {float(old.group(3)):.2f} % (decided safe less R454; D6 the same, +{d6.group(4)})')
    key(pre + 'holds', int(r9.group(4)), 'decided', 'count',
        f'{tag}): first-order soundness holds N (clause57.py all first-order holds) = {r9.group(4)}; by class ' + ', '.join(f'{k} {v}' for k, v in held_cls.items()) + f'; by program {sp(held_p)}')
    key(pre + 'box', int(bx.group(1)), 'delivered', 'count',
        f'{tag}): delivered rows whose emitted form is a Box form = {bx.group(1)}; by form ' + ', '.join(f'{k} {v}' for k, v in sorted(bfam.items())) + f'; by program {sp(bprog)}')

def sentences(js, sfx, base, new, hnew):
    d = json.load(open(os.path.join(RUN, js))); c = d['counts']; s = d['split']; n = d['names']
    g = lambda k: c.get(k, 0)
    frame = f'{new} against {base} by subject key over the delivered-kinds slot tables (ablation.py; kind_moves.py reproduces the totals)'
    P = 'ablation.order.'
    key(P + 'raw-to-owning' + sfx, g('raw-to-owning'), 'decided', 'count',
        f'{frame}: model slots Raw at {base} and Owning at {new} = {g("raw-to-owning")}; by program {sp(s["raw-to-owning"])}; every one named in runs/{js}')
    for dp in ('1', '2'):
        k = 'raw-to-owning.depth' + dp
        key(P + k + sfx, g(k), 'decided', 'count', f'{frame}: of the Raw to Owning slots, pointer depth {dp} = {g(k)}; by program {sp(s.get(k, {}))}')
    bn = '; '.join(x.split(' ', 1)[1].split('::')[-2] + '::' + x.split('::')[-1].split('#')[0] for x in n.get('raw-to-owning.box', []))
    key(P + 'raw-to-owning.box' + sfx, g('raw-to-owning.box'), 'delivered', 'count',
        f'{frame}: of the Raw to Owning slots, delivered as Box (delivered kind owning) = {g("raw-to-owning.box")}; by program {sp(s.get("raw-to-owning.box", {}))}; the slots: {bn}')
    key(P + 'raw-to-owning.ref' + sfx, g('raw-to-owning.ref'), 'delivered', 'count',
        f'{frame}: of the Raw to Owning slots, delivered as references (delivered kind ref, cause certificate-departure, the W6A-A9 lend) = {g("raw-to-owning.ref")}' + (f'; by program {sp(s["raw-to-owning.ref"])}' if g('raw-to-owning.ref') else '; the A9 reference lend is withheld at this head (box-param-lend-withheld)'))
    und = g('raw-to-owning.undelivered'); deg = g('raw-to-owning.undelivered.degraded'); rev = g('raw-to-owning.undelivered.fn-reverted')
    revn = '; '.join(n.get('raw-to-owning.undelivered.fn-reverted', []))
    key(P + 'raw-to-owning.undelivered' + sfx, und, 'delivered', 'count',
        f'{frame}: of the Raw to Owning slots, not delivered = {und} (degraded raw {deg}, reverted with the function {rev}' + (f': {revn}' if rev else '') + f'); by program {sp(s.get("raw-to-owning.undelivered", {}))}')
    rn = '; '.join(x.split(' ', 1)[0] + ' ' + x.split('::')[-2] + '::' + x.split('::')[-1].split('#')[0] for x in n.get('ref-to-owning', []))
    key(P + 'ref-to-owning' + sfx, g('ref-to-owning'), 'decided', 'count',
        f'{frame}: model slots Ref at {base} and Owning at {new} = {g("ref-to-owning")} ({rn}); delivered at {new}: as references {g("ref-to-owning.delivered-ref")}, raw {g("ref-to-owning.delivered-raw")}; by program {sp(s["ref-to-owning"])}')
    key(P + 'ref-slots.before' + sfx, g('ref-slots.before'), 'decided', 'count', f'{frame}: model Ref slots at {base} = {g("ref-slots.before")}; brotli {s["ref-slots.before"]["brotli"]}, tulipindicators {s["ref-slots.before"]["tulipindicators"]}, heman {s["ref-slots.before"]["heman"]}, the other seventeen {g("ref-slots.before") - s["ref-slots.before"]["brotli"] - s["ref-slots.before"]["tulipindicators"] - s["ref-slots.before"]["heman"]}')
    key(P + 'ref-slots.after' + sfx, g('ref-slots.after'), 'decided', 'count', f'{frame}: model Ref slots at {new} = {g("ref-slots.after")}; per program equal to {base} in all twenty' if s['ref-slots.after'] == s['ref-slots.before'] else f'{frame}: model Ref slots at {new} = {g("ref-slots.after")}; by program {sp(s["ref-slots.after"])}')
    rg, rl = g('ref-moves.becomes-delivered-ref'), g('ref-moves.leaves-delivered-ref')
    key(P + 'ref-moves' + sfx, g('ref-moves'), 'decided', 'count',
        f'{frame}: slots whose model kind changes with Ref on one side = {g("ref-moves")} (Ref to Raw {g("ref-to-raw")}, Ref to Owning {g("ref-to-owning")}, Raw to Ref {g("raw-to-ref")}; kind_moves.py same-function pair re-breaks 16); by program {sp(s["ref-moves"])}; in the tree {rg + rl} of them change the delivered references: +{rg} become delivered ({sp(s.get("ref-moves.becomes-delivered-ref", {}))}), -{rl} leave ({sp(s.get("ref-moves.leaves-delivered-ref", {}))})')
    key(P + 'ref-to-raw' + sfx, g('ref-to-raw'), 'decided', 'count', f'{frame}: model Ref to Raw = {g("ref-to-raw")}; by program {sp(s["ref-to-raw"])}')
    key(P + 'raw-to-ref' + sfx, g('raw-to-ref'), 'decided', 'count', f'{frame}: model Raw to Ref = {g("raw-to-ref")}; by program {sp(s["raw-to-ref"])}')
    key(P + 'ref-moves.to-delivered' + sfx, rg, 'delivered', 'count', f'{frame}: of the Ref moves, slots not delivered as a reference at {base} and delivered as one at {new} = {rg}: ' + '; '.join(x.split(' ', 1)[0] + ' ' + x.split('::')[-2] + '::' + x.split('::')[-1].split('#')[0] for x in n.get('ref-moves.becomes-delivered-ref', [])))
    key(P + 'ref-moves.from-delivered' + sfx, rl, 'delivered', 'count', f'{frame}: of the Ref moves, slots delivered as a reference at {base} and not at {new} = {rl}: ' + '; '.join(x.split(' ', 1)[0] + ' ' + x.split('::')[-2] + '::' + x.split('::')[-1].split('#')[0].split(' ')[0] + ' (' + x.split(' -> ')[-1] + ')' for x in n.get('ref-moves.leaves-delivered-ref', [])))
    key(P + 'delivered-ref.before' + sfx, g('delivered-ref.before'), 'delivered', 'count', f'{frame}: slots delivered as references (delivered kind ref, any model kind) at {base} = {g("delivered-ref.before")}; brotli {s["delivered-ref.before"]["brotli"]}, tulipindicators {s["delivered-ref.before"]["tulipindicators"]}, heman {s["delivered-ref.before"]["heman"]}')
    diff = {p: s['delivered-ref.after'].get(p, 0) - s['delivered-ref.before'].get(p, 0) for p in s['delivered-ref.before']}
    diff = {p: v for p, v in diff.items() if v}
    key(P + 'delivered-ref.after' + sfx, g('delivered-ref.after'), 'delivered', 'count', f'{frame}: slots delivered as references at {new} = {g("delivered-ref.after")}; change by program ' + ', '.join(f'{p} {v:+d}' for p, v in sorted(diff.items())) + ', the others unchanged')
    pr = d['brotli_lost_pair_rows']; lab = d['brotli_lost_by_label']
    key(P + 'overlap-hold.brotli-lost' + sfx, len(pr), 'delivered', 'count',
        f'{new} against {base} by identity (subject key without the #N suffix, census_by_identity.py; a reverted row is labelled with its function final-reverts attribution): brotli rows delivered at {base} and not at {new} = {d["brotli_lost_total"]}; labelled with a parameter-overlap or pair hold = {len(pr)}' + (': ' + '; '.join(k.split('::')[-2] + '::' + k.split('::')[-1] + ' (' + l + ')' for k, l in pr) if pr else '') + '; all labels: ' + ', '.join(f'{l} {v}' for l, v in lab.items()) + ('; the closure:partition reverts are a cascade label, their hold not traced' if any('closure' in l for l in lab) else ''))
sentences('abl-60sp.json', '', 'batch60', 'batch60sp', '32d966b9f')
sentences('abl-60s.json', '.at-60s', 'batch60', 'batch60s', '4eb66851b')
with open(R + '/new-keys.tsv', 'w') as w:
    w.write('key\tvalue\tlayer\tunit\tcause\n')
    for r in rows: w.write('\t'.join(r) + '\n')
with open(R + '/staged.tsv', 'w') as w:
    w.write('key\tvalue_now\tvalue_60sp\tverdict\tcause\n')
# the control: 224 section 0's numbers at 60s, and 225's at 60s'
ctl = {r[0]: r[1] for r in rows}
want = {'raw-to-owning.at-60s': '222', 'raw-to-owning.depth1.at-60s': '164', 'raw-to-owning.depth2.at-60s': '58', 'raw-to-owning.box.at-60s': '8',
        'raw-to-owning.ref.at-60s': '60', 'raw-to-owning.undelivered.at-60s': '154', 'ref-to-owning.at-60s': '7', 'ref-slots.before.at-60s': '4213',
        'ref-slots.after.at-60s': '4213', 'ref-moves.at-60s': '46', 'ref-to-raw.at-60s': '16', 'raw-to-ref.at-60s': '23',
        'delivered-ref.before.at-60s': '2504', 'delivered-ref.after.at-60s': '2481', 'ref-moves.to-delivered.at-60s': '5', 'ref-moves.from-delivered.at-60s': '3',
        'raw-to-owning': '222', 'raw-to-owning.box': '8', 'raw-to-owning.ref': '0', 'raw-to-owning.undelivered': '214', 'ref-to-owning': '7',
        'ref-slots.after': '4213', 'ref-moves': '46', 'ref-moves.to-delivered': '6', 'ref-moves.from-delivered': '7', 'delivered-ref.after': '2503',
        'batch60.delivered': '2708', 'batch60.rate': '80.00 %', 'batch60.old-rate': '62.96 %', 'batch60.holds': '916', 'batch60.box': '204',
        'batch60s.delivered': '2685', 'batch60s.rate': '75.02 %', 'batch60s.old-rate': '59.27 %', 'batch60s.holds': '951', 'batch60s.box': '204',
        'batch60sp.delivered': '2715', 'batch60sp.rate': '75.17 %', 'batch60sp.old-rate': '59.93 %', 'batch60sp.holds': '918', 'batch60sp.box': '212',
        'batch60.safe-decisions': '4301', 'batch60s.safe-decisions': '4530', 'batch60sp.safe-decisions': '4530'}
bad = [(k, v, ctl.get('ablation.order.' + k)) for k, v in want.items() if ctl.get('ablation.order.' + k) != v]
print(f'keys {len(rows)}; control against main 223/224/225: {len(want) - len(bad)} / {len(want)} equal')
if bad: raise SystemExit(f'CONTROL FAILED: {bad}')
