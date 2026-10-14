#!/usr/bin/env python3
"""r141 (relay analysis-fanout 141, group rq5): audit_batch58pp_rowlevel.py parametrized (base, census, cols, map, tag) plus P9 (--tree-custody: delivery-custody ledger-only rows read by receipt). With the r140 arguments it reproduces r140/rq5/out byte for byte (the control)."""
"""r140 (relay analysis-fanout 139, group rq5): RQ5 row by row at 58pp (main/batch58pp, cf9719575). Base = 58's D6 row file of record (r138/d6/out/rq5-rows-58-d6.tsv = r133c + 7 verifier corrections + D6's 12). Rules P0-P8 unchanged from r133c (docstring below); P0 now reads the 58 cause."""
"""r133c (relay analysis-fanout 133 item 3, first bullet): RQ5's six causes at batch 58, ROW BY ROW (R770-1 / R772-3 /
R775 / R777-2). Base: batch 56's row-level file of record (r122 g088b rows-final-b56.tsv). Census: main/batch58
(b52e02437, frame14u's cache, cache-only).

Standard (the same as r110 audit_frame14u.py / r122 audit_batch56.py): a batch-58 undelivered row whose (program,
subject_key, label, family) equals batch 56's keeps batch 56's row-level cause. Every other row (new at 58, relabelled,
family-changed) is classified HERE by its own receipt (subjects.tsv reason / reason_detail / exclusion; the
into-held-formal chain followed to its root; the final-reverts root for reverted rows):

  P0  a relabelled / family-changed row whose batch-56 row-level cause is unavoidable (held / no-safe-form / undefined /
      type-system: a fact of the input, R770-1) keeps it -- the 58 hold sits on top of it;
  P1  held:pair-not-shown-disjoint
        raw-boundary-site (the pending pair hold, R829-1 / R855-1)            -> side-condition
        ref-beside-raw / ref-beside-ref ; unresolved (R934-1 (i))              -> side-condition
        ... ; contained (one argument derives from the other's object)        -> side-condition, unless the call is
                                                                                 read as UB (none of the 6 is: see notes)
        ... ; same-static (one static at both positions, a written partner)   -> undefined (035's "identical argument
                                                                                 twice"; R864-1's zsqr class)
  P2  held:retained-alias (R826-1 (E) / R864-3 retained-access hold; R796-1 map) -> side-condition (R786-1 (i))
  P3  held:into-held-formal / into-held-binding: the cause of the root hold the chain ends at (a cascade inherits its
      root's cause, R770-1); roots: the P1/P2 holds -> side-condition; held:released-through-indirect-call -> undefined
  P4  pair-not-shown-disjoint (the pair pass's own; wave-5d's line), its blocked-subject cascades -> side-condition
  P5  pair-proven-overlap and its blocked-subject cascades -> undefined (R810-3; the record's label default)
  P6  contract-allocation (blocked-subject:contract-allocation:use) and the dependency-class-held rows rooted there
      -> side-condition (035: contract-allocation:use = the callee is not proven a lend)
  P7  a5-site-proof-t2-fallback: the receipt names fallback-yields-contained-edit (a rendering shape) -> generator
  P8  every other changed row: the label-level map (035 rq5_cause_map.py, map58/rows.tsv), which is the record's
      default (pair-raw-view / escapes-via-* / aliased-storage-withdrawn / pending-sibling-overlap -> side-condition;
      verify-reverted / slice-* / null-init / opt-local-construction -> generator; slice-neg-or-unknown-offset per the
      035 override).
Writes rq5-rows-58pp.tsv (1,627 rows, every reading side by side), rows-final-b58pp.tsv, totals-b58pp.tsv, label-map-58pp.tsv,
changed-58.tsv, left-b58pp.tsv."""
import csv, collections, re
csv.field_size_limit(10**9)
import argparse, json, os
ap = argparse.ArgumentParser()
ap.add_argument('--base', required=True); ap.add_argument('--census', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--cols', required=True); ap.add_argument('--map', required=True); ap.add_argument('--tag', required=True)
ap.add_argument('--n-base', type=int, required=True); ap.add_argument('--n-rows', type=int, required=True)
ap.add_argument('--prev', default='58'); ap.add_argument('--cur', default='58pp')
ap.add_argument('--tree-custody', action='store_true', help='r141: rows the ledger counts delivered but the emitted tree keeps raw (delivery-custody ledger-only) join the undelivered set and are read by their receipts (P9)')
A = ap.parse_args()
BASE, C, D, T = A.base, A.census, A.out, A.tag
rd = lambda f: list(csv.DictReader(open(f), delimiter='\t'))
key = lambda r: (r['program'], r['subject_key'])
old = {key(r): r for r in rd(BASE)}
oldm = old  # the base row file carries the previous frame's census family
if not (len(old) == A.n_base):
    raise SystemExit(len(old))
newm = {key(r): r for r in rd(A.cols)}
rows = rd(f'{A.map}/rows.tsv')
LEDGER_ONLY = []
if A.tree_custody:
    import glob
    for f in sorted(glob.glob(C + '/*.raw-boundary-delivery-custody.json')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        c = json.load(open(f))['comparison']
        led, tree = set(c.get('delivered_by_ledger') or []), set(c.get('delivered_by_tree') or [])
        if tree - led:
            raise SystemExit(f'tree-only rows in {p}: the tree delivers what the ledger does not; read them first')
        LEDGER_ONLY += [(p, k) for k in sorted(led - tree)]
if not (len(rows) + len(LEDGER_ONLY) == A.n_rows):
    raise SystemExit((len(rows), len(LEDGER_ONLY)))
SJ = {}
def subj(p):
    if p not in SJ:
        SJ[p] = {r['subject_key']: r for r in rd(f'{C}/{p}.raw-boundary-subjects.tsv')}
    return SJ[p]
BYARG, BYNAME = {}, {}
def formal(p, fn, n):
    if p not in BYARG:
        a, b = collections.defaultdict(list), collections.defaultdict(list)
        for s in subj(p).values():
            a[(s['owner_fn'], s['arg_index'])].append(s)
            b[s['subject_key'].split('#')[0]].append(s)
        BYARG[p], BYNAME[p] = a, b
    return [s for s in BYARG[p].get((fn, str(n)), []) if s['reason'].startswith('held:')]
def binding(p, path):
    formal(p, '', 0)
    return [s for s in BYNAME[p].get(path, []) if s['reason'].startswith('held:')]

UNAVOID = {'held', 'no-safe-form', 'undefined', 'type-system'}
SC, UD, GEN = 'side-condition', 'undefined', 'generator'

def own_hold(p, s):
    """cause, sub, evidence for a subject whose own receipt is a first-order hold (P1, P2, released)."""
    r, d = s['reason'], s['reason_detail']
    if r == 'held:pair-not-shown-disjoint':
        m = re.match(r'pair-not-shown-disjoint:([a-z-]+):', d)
        kind = m.group(1)
        if kind == 'raw-boundary-site':
            sib = re.search(r'risky-siblings=([^;]*)', d)
            return SC, 'pending pair hold (raw-boundary-site; R829-1 / R855-1)', f'a caller\'s reference handed to a raw formal beside a sibling not shown disjoint ({sib.group(0) if sib else "risky siblings"}): argument overlap not established'
        why = d.split(';', 1)[1] if ';' in d else ''
        if why.startswith('same-static'):
            return UD, f'{kind}; same-static (identical argument twice, written partner)', 'one static at both positions of the call (zmodpow: zmodsqr(libzahl_tmp_pow_b, libzahl_tmp_pow_b, _)); zmodsqr hands both to zsqr(a, b), which writes a while b is live: R864-1 / 081\'s zsqr class (TB/SB UB), 035 "identical argument twice" -> undefined'
        if why.startswith('contained'):
            return SC, f'{kind}; contained (R934-1 (i) / R866-1)', 'one argument derives from the other\'s object; no write into the reference\'s range through the raw peer is established at the call (read in the emitted tree, notes §1.4): argument overlap not shown harmless -> side-condition'
        return SC, f'{kind}; unresolved (R934-1 (i))', f'reference formal beside a {"raw" if kind.endswith("raw") else "reference"} written formal, roots unresolved, {why.split(";")[1] if ";" in why else why}: argument overlap not established'
    if r == 'held:retained-alias':
        return SC, 'retained-access hold (' + d.split(' |')[0].split(':')[0] + ':' + d.split(':')[1].split(' ')[0] + ')', 'R826-1 (E) / R864-3: the referent is reached through a stored / self-referential / cyclic raw pointer the program may access while the reference is live; not shown harmless (R786-1 (i): side-condition)'
    if r == 'held:released-through-indirect-call':
        return UD, 'released through an indirect call', 'R857-2: the reference would be deallocated through a function pointer while protected (TB/SB UB; fan-out 074) -> undefined (56 row-level reading)'
    return None

def chain_root(p, s, seen=()):
    d = s['reason_detail']
    m = re.match(r'into-held-formal:(.*)#(\d+)$', d)
    n = re.match(r'into-held-binding:(.*)$', d)
    nxt = formal(p, m.group(1), m.group(2)) if m else (binding(p, n.group(1)) if n else None)
    if nxt is None:
        return s, seen
    if not (nxt):
        raise SystemExit((p, s['subject_key'], d))
    f = nxt[0]
    if not (f['subject_key'] not in seen):
        raise SystemExit('check failed: line 116')
    return chain_root(p, f, seen + (f['subject_key'],))

def classify(r, o):
    p, sk, lab = r['program'], r['subject_key'], r['label']
    s = subj(p)[sk]
    if o and o['cause'] in UNAVOID:
        return o['cause'], f'{A.prev} cause kept ({o["sub"][:60]}); {A.prev} adds {lab}', f'P0: unavoidable at {A.prev} (a fact of the input); the {A.cur} hold sits on top: ' + o['evidence'][:200]
    if lab in ('held:pair-not-shown-disjoint', 'held:retained-alias', 'held:released-through-indirect-call'):
        c, sub, ev = own_hold(p, s)
        return c, sub, f'P1/P2: {s["reason_detail"][:160]} :: {ev}'
    if lab == 'held:into-held-formal':
        root, path = chain_root(p, s)
        c, sub, ev = own_hold(p, root)
        return c, f'cascade -> {root["subject_key"]} ({sub})', f'P3: {s["reason_detail"][:120]} -> chain of {len(path)} to {root["subject_key"]} [{root["reason"]}] :: {ev}'
    excl = s['exclusion']
    if lab == 'pair-not-shown-disjoint':
        return SC, 'pair pass: pair not shown disjoint' + (' (blocked-subject cascade)' if 'blocked-subject' in excl else ''), f'P4: reason={s["reason"]} detail={s["reason_detail"][:60]} excl={excl[:90]}: argument overlap not established'
    if lab == 'pair-proven-overlap':
        return UD, 'pair proven to overlap' + (' (blocked-subject cascade)' if 'blocked-subject' in excl else ''), f'P5: R810-3 (two live references over one object, a written side); excl={excl[:80]}'
    if lab == 'contract-allocation' or (lab == 'dependency-class-held' and 'contract-allocation:use' in newm[(p, sk)]['root_reason']):
        return SC, 'contract-allocation:use (blocked-subject cascade)', f'P6: excl={excl[:90]} root={newm[(p, sk)]["root"][:90]}: the callee is not proven a lend (035)'
    if lab == 'a5-site-proof-t2-fallback':
        return GEN, 'T2 fallback yields a contained edit', f'P7: excl={excl[:120]}: a rendering shape, no absent fact named'
    return r['cause'], r['sub'], 'P8 label-level (035 map): ' + r['evidence'][:200]

def p9(p, sk):
    """P9 (r141): a row the ledger counts delivered and the emitted tree keeps raw (delivery-custody ledger-only). The
    count of record is by the tree, so it is undelivered; it carries no hold label of its own (reason '-'), and the tree
    keeps it raw because the compile check reverted a function it depends on: the cause is the revert's (verify-reverted,
    a compiler diagnostic = the generator's own output did not type-check) -> generator."""
    fr = [r for r in rd(f'{C}/{p}.raw-boundary-final-reverts.tsv') if r['kind'] == 'function']
    dg = [r for r in rd(f'{C}/{p}.raw-boundary-compiler-diagnostics.tsv')]
    fns = ', '.join(f"{r['identity']} ({r['attribution']})" for r in fr)
    codes = ', '.join(sorted({f"{r['error_code']} in {r['function']}" for r in dg}))
    return GEN, 'custody ledger-only: raw in the emitted tree beside a compile-check revert', f'P9: delivery-custody ledger-only (the ledger reads realized-as-predicted, the emitted tree keeps the subject raw; count of record by the tree); the program\'s function reverts: {fns}; compiler diagnostics: {codes}; no hold label (reason -): the generator\'s output did not type-check -> generator'

rows = rows + [dict(program=p, subject_key=k, group='T', label='custody:ledger-only', cause='', sub='', evidence='') for p, k in LEDGER_ONLY]
out, changed, n_kind = [], [], collections.Counter()
for r in rows:
    k = key(r); o = old.get(k)
    if r['label'] == 'custody:ledger-only':
        so = {x['subject_key']: x for x in rd(f'{C}/{k[0]}.raw-boundary-subject-outcomes.tsv')}[k[1]]
        m = dict(family=so['family'], delivery='custody-ledger-only', cause='generator')
        kind = 'custody-ledger-only' if not o else 'custody-ledger-only-in-base'
        c, sub, ev = p9(*k)
        changed.append(k)
        n_kind[kind] += 1
        s = subj(k[0])[k[1]]
        out.append(dict(program=k[0], subject_key=k[1], family=m['family'], delivery=m['delivery'], kind=kind, label=r['label'],
                        reason_detail=s['reason_detail'][:200], exclusion=s['exclusion'][:120],
                        b58_label=o['label'] if o else '-', b58_family=o['family'] if o else '-', b58_cause=o['cause'] if o else '-',
                        cause=c, sub=sub, evidence=ev, readingA=c, main_map='-'))
        continue
    m = newm[k]
    if o and o['label'] == r['label'] and oldm[k]['family'] == m['family']:
        kind, c, sub, ev = 'unchanged', o['cause'], o['sub'], o['evidence']
    else:
        kind = 'new' if not o else ('relabelled' if o['label'] != r['label'] else 'family-changed')
        c, sub, ev = classify(r, o)
        changed.append(k)
    n_kind[kind] += 1
    s = subj(k[0])[k[1]]
    out.append(dict(program=k[0], subject_key=k[1], family=m['family'], delivery=m['delivery'], kind=kind, label=r['label'],
                    reason_detail=s['reason_detail'][:200], exclusion=s['exclusion'][:120],
                    b58_label=o['label'] if o else '-', b58_family=o['family'] if o else '-', b58_cause=o['cause'] if o else '-',
                    cause=c, sub=sub, evidence=ev,
                    readingA=r['cause'] if kind != 'unchanged' else o['readingA'], main_map=m['cause']))
CAUSES = ['held', 'no-safe-form', 'undefined', 'type-system', 'side-condition', 'form-fact', 'generator']
F = list(out[0].keys())
with open(f'{D}/rq5-rows-{T}.tsv', 'w') as f:
    w = csv.DictWriter(f, F, delimiter='\t', lineterminator='\n'); w.writeheader(); w.writerows(out)
with open(f'{D}/rows-final-b{T}.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n'); w.writerow(['program', 'subject_key', 'group', 'label', 'cause', 'sub', 'evidence'])
    grp = {key(r): r['group'] for r in rows}
    w.writerows([[x['program'], x['subject_key'], grp[(x['program'], x['subject_key'])], x['label'], x['cause'], x['sub'], x['evidence']] for x in out])
per = collections.defaultdict(collections.Counter); tot = collections.Counter()
for x in out: per[x['program']][x['cause']] += 1; tot[x['cause']] += 1
with open(f'{D}/totals-b{T}.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n'); w.writerow(['program'] + CAUSES + ['total'])
    for p in sorted(per): w.writerow([p] + [per[p][c] for c in CAUSES] + [sum(per[p].values())])
    w.writerow(['total'] + [tot[c] for c in CAUSES] + [sum(tot.values())])
lab = collections.defaultdict(collections.Counter)
for x in out: lab[(x['label'], x['kind'] if x['kind'] == 'unchanged' else 'changed')][x['cause']] += 1
with open(f'{D}/label-map-{T}.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n'); w.writerow(['label', 'rows', 'unchanged_or_changed'] + CAUSES)
    for (l, kd) in sorted(lab, key=lambda t: (-sum(lab[t].values()), t)):
        w.writerow([l, sum(lab[(l, kd)].values()), kd] + [lab[(l, kd)][c] for c in CAUSES])
here = {key(r) for r in rows}
with open(f'{D}/left-b{T}.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n'); w.writerow(['program', 'subject_key', 'b58_label', 'b58_cause', 'b58_kind'])
    for k in sorted(set(old) - here): w.writerow([k[0], k[1], old[k]['label'], old[k]['cause'], old[k]['kind']])
o56 = collections.Counter(r['cause'] for r in old.values())
rc = {n: collections.Counter(x[n] for x in out) for n in ('readingA', 'main_map')}
print('kinds', dict(n_kind), 'changed', len(changed), 'left', len(set(old) - here))
print('cause\tb58(D6)\trow-level58pp\tA\tmain')
for c in CAUSES: print(f'{c}\t{o56[c]}\t{tot[c]}\t' + '\t'.join(str(rc[n][c]) for n in rc))
print('total', sum(o56.values()), sum(tot.values()))
