#!/usr/bin/env python3
"""clause_holds_d6.py (analysis-fanout 112, relay 138: copy of r133 clause_holds.py; ONLY change: D6 universe rule)
clause_holds.py <census-dir> <record-count> <record-den> <hold-price.tsv> <raw-view-peers.tsv> [<era-5c hold dir>] [out.tsv]
Relay 290 item 2 (relay 284 item 5): the clause's record line under the same holds, by identity, on one census:
  (1) the pending hold: the pending sites' reference-side subjects (pending_hold_price.py's table);
  (2) the peer rule: the delivered callee formals standing as a raw-view peer (raw_view_peers.py's table);
  (3) the retained-access check at era-5c's line: the slots its scan holds (`hold.<program>` rows, status `held`),
      joined to the census subjects by (owner function, MIR local).
Withdrawn N = the decided-safe subjects a hold names (the union, by identity); d = the delivered among them.
Printed, for each hold alone and for the unions: the old definition (count - d) / denominator, and the withdrawn
rows out of the denominator (count - d) / (denominator - N)."""
import csv, glob, os, re, sys
csv.field_size_limit(10**9)
SAFE = {'ref', 'slice', 'box', 'optional', 'cursor'}
D = 'realized-as-predicted'
R454 = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'


def main(cen, count, den, hold_price, peers, era5c=None, out=None):
    count, den = int(count), int(den)
    excl = {(r['program'], r['owner'], r['binding'])
            for r in csv.DictReader(open(R454), delimiter='\t') if r['counts_toward_N'] == 'true'}
    # the census's decided-safe subjects (as clause_line.py counts them), and the delivered among them
    safe, delivered, by_slot = set(), set(), {}
    for f in sorted(glob.glob(f'{cen}/*.raw-boundary-subject-outcomes.tsv')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        subjects = {r['subject_key']: r for r in csv.DictReader(open(f.replace('subject-outcomes', 'subjects')), delimiter='\t')}
        for so in csv.DictReader(open(f), delimiter='\t'):
            real = so['delivery'] == D
            if not (so['family'] in SAFE or real or subjects[so['subject_key']]['decision'] in SAFE):  # D6
                continue
            binding = re.sub(r'#\d+$', '', so['subject_key'].rsplit('::', 1)[-1])
            if so['family'] in SAFE and not real and (p, so['owner_fn'], binding) in excl:
                continue  # R454, outside the denominator already
            k = (p, so['subject_key'])
            safe.add(k)
            if real:
                delivered.add(k)
            s = subjects.get(so['subject_key'])
            if s:
                by_slot[(p, s['owner_fn'], s['mir_local'])] = k
    holds = {}
    holds['pending'] = {(r['program'], r['subject']) for r in csv.DictReader(open(hold_price), delimiter='\t')}
    holds['peers'] = {(r['program'], r['peer_subject']) for r in csv.DictReader(open(peers), delimiter='\t')}
    if era5c:
        held, unjoined = set(), 0
        for f in sorted(glob.glob(f'{era5c}/hold.*')):
            p = os.path.basename(f)[len('hold.'):]
            for line in open(f):
                c = line.rstrip('\n').split('\t')
                if len(c) < 5 or c[4] != 'held':
                    continue
                k = by_slot.get((p, c[0], c[1]))
                if k:
                    held.add(k)
                else:
                    unjoined += 1
        holds['retained-access'] = held
        print(f'era-5c held slots not joined to a decided-safe census subject (temporaries, non-safe, R454): {unjoined}')
    rows = []

    def line(name, ks):
        ks = ks & safe
        n, d = len(ks), len(ks & delivered)
        old = (count - d) / den
        out_ = (count - d) / (den - n)
        rows.append((name, n, d, count - d, den, den - n, old, out_))
        print(f'{name:38} N={n:5} d={d:5}  old {count - d:,}/{den:,} = {100 * old:.2f} %   '
              f'out {count - d:,}/{den - n:,} = {100 * out_:.2f} %')

    print(f'record: {count:,} / {den:,} = {100 * count / den:.2f} %  (census tables: {len(delivered):,} delivered of {len(safe):,} decided safe)')
    for name, ks in holds.items():
        line(name, ks)
    names = list(holds)
    if len(names) >= 2:
        line('pending + peers', holds['pending'] | holds['peers'])
    if 'retained-access' in holds:
        line('retained-access + pending', holds['retained-access'] | holds['pending'])
        line('all three', holds['retained-access'] | holds['pending'] | holds['peers'])
    if out:
        with open(out, 'w') as w:
            w.write('holds\tN\td\tnumerator\tdenominator_old\tdenominator_out\trate_old\trate_out\n')
            for r in rows:
                w.write('\t'.join(map(str, r[:6])) + f'\t{r[6]:.6f}\t{r[7]:.6f}\n')


if __name__ == '__main__':
    main(*sys.argv[1:8])
