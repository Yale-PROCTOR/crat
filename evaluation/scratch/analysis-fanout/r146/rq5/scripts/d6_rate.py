#!/usr/bin/env python3
"""r141: d6_rate.py <census-dir> <out-dir> <U> <D> [--tree-custody] (the 58pp copy with the pins as arguments and the count by the emitted tree)
d6_rate.py <census-dir> <out-dir>   (analysis-fanout 112, relay 138: copy of r136 r956_rate.py; ONLY changes: D6 universe rule
(also a subject whose census decision is a safe form, whatever the outcome) and the asserted totals 4,272 / 2,633)
r956_rate.py <census-dir> <out-dir>
Relay 136 (R956-1, the USER): the rate of record at a census = delivered by identity over the same census's in-scope
safe decisions (R709-1, p1_count.py's rule: family in SAFE or delivered, less the R454 36) with every FIRST-ORDER
soundness hold of the code generator out of the denominator. Cascades (into-held-formal, class holds, closures,
verify reverts) stay IN.

A subject is withheld by a first-order hold when EITHER
  (L) its label (raw-boundary-subjects.tsv `reason`, the first reason) is the hold, OR
  (R) a receipt in raw-boundary-settled-holds.tsv names it under the hold's predicate.
Hold kinds (main 213 §4 / clause57.py's `kind`):
  pending      held:pair-not-shown-disjoint whose detail is not ref-beside-* (raw-boundary-site; R829-1 / R855-1)
  ref-beside   held:pair-not-shown-disjoint whose detail has ref-beside-raw / ref-beside-ref (R864-1 / R934-1 (i))
  retained     held:retained-alias (R864-3)
  backstop     held:released-through-indirect-call (R857-2)
  cascade      held:into-held-formal (NOT first order; reported only)
Read-only on the census; writes only into <out-dir>.
"""
import collections, csv, glob, json, os, re, statistics, sys
csv.field_size_limit(10 ** 9)
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
DELIV = 'realized-as-predicted'
R454F = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'
R454 = {(r['program'], r['owner'], r['binding']) for r in csv.DictReader(open(R454F), delimiter='\t')
        if r['counts_toward_N'] == 'true'}
if not (len(R454) == 36):
    raise SystemExit('check failed: line 29')
FIRST = ('pending', 'ref-beside', 'retained', 'backstop')
ALL = FIRST + ('cascade',)


def kind(pred, detail):
    if pred == 'held:pair-not-shown-disjoint':
        return 'ref-beside' if 'ref-beside-' in detail else 'pending'
    return {'held:retained-alias': 'retained', 'held:released-through-indirect-call': 'backstop',
            'held:into-held-formal': 'cascade'}.get(pred)


def sub_kind(pred, detail):
    """finer label: pending / ref-beside-raw / ref-beside-ref / retained:<evident> / backstop / cascade"""
    k = kind(pred, detail)
    if k == 'ref-beside':
        return 'ref-beside-ref' if 'ref-beside-ref' in detail else 'ref-beside-raw'
    if k == 'retained':
        return 'retained:' + ':'.join(detail.split(';')[0].split(' | ')[0].split(':')[:2])
    return k


def load(C):
    rows = []  # one per subject-outcome row
    for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        subj = {r['subject_key']: r for r in csv.DictReader(open(f.replace('subject-outcomes', 'subjects')), delimiter='\t')}
        settled = collections.defaultdict(list)
        for r in csv.DictReader(open(f.replace('subject-outcomes', 'settled-holds')), delimiter='\t'):
            settled[r['subject']].append((r['predicate'], r['detail']))
        for so in csv.DictReader(open(f), delimiter='\t'):
            k = so['subject_key']
            d = so['delivery'] == DELIV and (p, so['subject_key']) not in LEDGER_ONLY  # r141: by the emitted tree
            sb0 = subj[k]
            s = so['family'] in SAFE or d or sb0['decision'] in SAFE  # D6 (relay 138)
            key = re.sub(r'#\d+$', '', k)
            owner, _, b = key.rpartition('::')
            r454 = (p, owner, b) in R454
            if r454:
                if not (s and not d):
                    raise SystemExit('check failed: line 68')
            sb = subj[k]
            lab = kind(sb['reason'], sb['reason_detail'])
            rec = settled.get(k, [])
            rows.append(dict(program=p, subject_key=k, family=so['family'], delivery=so['delivery'],
                             emitted_form=so['emitted_form'], delivered=d, in_scope=s and not r454, r454=r454,
                             reason=sb['reason'], reason_detail=sb['reason_detail'], label_kind=lab,
                             label_sub=sub_kind(sb['reason'], sb['reason_detail']) if lab else None,
                             receipts=rec))
    return rows


def main(C, out):
    os.makedirs(out, exist_ok=True)
    rows = load(C)
    U = [r for r in rows if r['in_scope']]
    D = [r for r in U if r['delivered']]
    if not (len(U) == EXP_U and len(D) == EXP_D):
        raise SystemExit((len(U), len(D)))
    log = []
    P = lambda *a: log.append(' '.join(str(x) for x in a))
    P(f'census {C}')
    P(f'rows {len(rows)}; in scope (p1_count rule) {len(U)}; delivered {len(D)}; old rate {100*len(D)/len(U):.2f} %')

    # per-subject hold sets, label and receipts
    out_scope_hold = collections.Counter()
    for r in rows:
        r['by_label'] = {r['label_kind']} if r['label_kind'] else set()
        r['by_receipt'] = {kind(p_, d_) for p_, d_ in r['receipts']} - {None}
        r['subs'] = ({r['label_sub']} if r['label_sub'] else set()) | {sub_kind(p_, d_) for p_, d_ in r['receipts']}
        r['holds'] = r['by_label'] | r['by_receipt']
        r['first'] = r['holds'] & set(FIRST)
        if r['holds'] and not r['in_scope']:
            for h in r['holds']:
                out_scope_hold[(h, 'r454' if r['r454'] else ('family=' + r['family']))] += 1
    P('\n(1) hold sets over ALL 7,011 rows that are OUTSIDE the 4,260 (a held subject outside scope does not move the denominator):')
    for (h, why), n in sorted(out_scope_hold.items()):
        P(f'    {h:11} {why:22} {n}')

    # label vs receipts agreement
    P('\n(1a) label (first reason) vs settled-holds receipts, in scope, per hold:')
    P(f'    {"hold":11} {"label":>6} {"receipt":>8} {"both":>6} {"label-only":>10} {"receipt-only":>12} {"union":>6}')
    for h in ALL:
        L = {r['subject_key'] + '@' + r['program'] for r in U if h in r['by_label']}
        R = {r['subject_key'] + '@' + r['program'] for r in U if h in r['by_receipt']}
        P(f'    {h:11} {len(L):6} {len(R):8} {len(L & R):6} {len(L - R):10} {len(R - L):12} {len(L | R):6}')
    lab_first = [r for r in U if r['label_kind'] in FIRST]
    W = [r for r in U if r['first']]
    P(f'    first-order by label alone: {len(lab_first)} (main 213 §4: 906)')
    P(f'    first-order by label OR receipt (the withheld set): {len(W)}')
    extra = [r for r in W if r['label_kind'] not in FIRST]
    P(f'    withheld by a receipt only (label is not a first-order hold): {len(extra)}; their labels: '
      + str(dict(collections.Counter(r['reason'] for r in extra).most_common())))

    # overlap matrix
    P('\n(1b) overlap matrix over the withheld set (subjects named by both holds, label or receipt):')
    P('    ' + ' '.join(f'{h:>11}' for h in ALL))
    for a in ALL:
        P(f'    {a:11}' + ' '.join(f'{sum(1 for r in U if a in r["holds"] and b in r["holds"]):11}' for b in ALL))
    combos = collections.Counter('+'.join(sorted(r['first'])) for r in W)
    P('    first-order combinations: ' + ', '.join(f'{k} {v}' for k, v in combos.most_common()))
    subc = collections.Counter('+'.join(sorted(s for s in r['subs'] if s != 'cascade')) for r in W)
    P('    finer combinations: ' + ', '.join(f'{k} {v}' for k, v in subc.most_common()))
    casc_also = sum(1 for r in W if 'cascade' in r['holds'])
    P(f'    withheld subjects ALSO named by into-held-formal (counted once, as first order): {casc_also}')

    wd = [r for r in W if r['delivered']]
    P(f'\n(1c) every withheld subject in scope: {all(r["in_scope"] for r in W)} (by construction W is drawn from the 4,260); '
      f'withheld AND delivered: {len(wd)}')
    allheld_rows = [r for r in rows if r['first']]
    P(f'    first-order-held rows over all 7,011: {len(allheld_rows)}; outside the 4,260: {sum(1 for r in allheld_rows if not r["in_scope"])}; '
      f'delivered among all: {sum(1 for r in allheld_rows if r["delivered"])}')

    # attribution: one hold per subject (label first, else a fixed order) for the "withdrawn by hold" column
    order = ('pending', 'ref-beside', 'retained', 'backstop')
    def attr(r):
        return r['label_kind'] if r['label_kind'] in FIRST else next(h for h in order if h in r['first'])
    by_attr = collections.Counter(attr(r) for r in W)
    wn = len(W)
    rate = 100 * len(D) / (len(U) - wn)
    P(f'\n(2) R956-1 rate: {len(D):,} / ({len(U):,} - {wn}) = {len(D):,} / {len(U) - wn:,} = {rate:.2f} %')
    P('    withdrawn by hold (attributed once: the label; a receipt-only subject to the first of pending, ref-beside, retained, backstop):')
    for h in FIRST:
        anyn = sum(1 for r in W if h in r['first'])
        P(f'      {h:11} attributed {by_attr[h]:4}   named (label or receipt) {anyn:4}')
    P(f'      total {wn}')

    # per program
    progs = sorted({r['program'] for r in rows})
    per = []
    for p in progs:
        u = [r for r in U if r['program'] == p]
        d = sum(r['delivered'] for r in u)
        w = sum(1 for r in u if r['first'])
        wh = collections.Counter(attr(r) for r in u if r['first'])
        casc = sum(1 for r in u if r['label_kind'] == 'cascade' and not r['first'])
        den = len(u) - w
        per.append(dict(program=p, delivered=d, in_scope=len(u), withheld=w,
                        withheld_pending=wh['pending'], withheld_ref_beside=wh['ref-beside'],
                        withheld_retained=wh['retained'], withheld_backstop=wh['backstop'],
                        denominator=den, rate_r956=(f'{100*d/den:.2f}' if den else 'n/a'),
                        rate_old=(f'{100*d/len(u):.2f}' if u else 'n/a'),
                        cascade_label=casc))
    rates = [100 * x['delivered'] / x['denominator'] for x in per if x['denominator']]
    med = statistics.median(rates)
    rates_old = [100 * x['delivered'] / x['in_scope'] for x in per if x['in_scope']]
    P(f'    per-program median (programs with a non-empty denominator, n={len(rates)}): {med:.2f} %  '
      f'(old definition median {statistics.median(rates_old):.2f} %)')
    with open(f'{out}/rate.tsv', 'w') as w:
        cols = list(per[0])
        w.write('\t'.join(cols) + '\n')
        for x in per:
            w.write('\t'.join(str(x[c]) for c in cols) + '\n')
        w.write('\t'.join(['TOTAL', str(len(D)), str(len(U)), str(wn), str(by_attr['pending']), str(by_attr['ref-beside']),
                           str(by_attr['retained']), str(by_attr['backstop']), str(len(U) - wn), f'{rate:.2f}',
                           f'{100*len(D)/len(U):.2f}', str(sum(x['cascade_label'] for x in per))]) + '\n')
        w.write('\t'.join(['MEDIAN', '', '', '', '', '', '', '', '', f'{med:.2f}', f'{statistics.median(rates_old):.2f}', '']) + '\n')

    # holds.tsv per subject (every in-scope subject named by any hold, first order or cascade)
    with open(f'{out}/holds.tsv', 'w') as w:
        cols = ['program', 'subject_key', 'family', 'delivery', 'in_scope', 'withheld_r956', 'attributed_hold',
                'first_order_holds', 'label_reason', 'label_hold', 'receipt_holds', 'finer', 'cascade_named', 'reason_detail']
        w.write('\t'.join(cols) + '\n')
        for r in rows:
            if not r['holds']:
                continue
            w.write('\t'.join(map(str, [r['program'], r['subject_key'], r['family'], r['delivery'], int(r['in_scope']),
                                        int(bool(r['first']) and r['in_scope']), attr(r) if r['first'] else '-',
                                        '+'.join(sorted(r['first'])) or '-', r['reason'], r['label_kind'] or '-',
                                        '+'.join(sorted(r['by_receipt'])) or '-',
                                        '+'.join(sorted(r['subs'])) or '-', int('cascade' in r['holds']),
                                        r['reason_detail'].replace('\t', ' ')])) + '\n')

    # (3) provenance variants
    ret = [r for r in U if 'retained' in r['first']]
    ret_lab = [r for r in U if r['label_kind'] == 'retained']
    P('\n(3) provenance:')
    P(f'    old definition (R709-1): {len(D):,} / {len(U):,} = {100*len(D)/len(U):.2f} %')
    P(f'    R812-1 / R858-2 (retained-access only, by label as main): {len(D):,} / {len(U)-len(ret_lab):,} = '
      f'{100*len(D)/(len(U)-len(ret_lab)):.2f} %  (withdrawn {len(ret_lab)})')
    P(f'    R812-1, label or receipt: {len(D):,} / {len(U)-len(ret):,} = {100*len(D)/(len(U)-len(ret)):.2f} %  (withdrawn {len(ret)})')
    return dict(U=U, D=D, W=W, rows=rows, log=log, out=out)


LEDGER_ONLY = set()


def ledger_only(C):
    out = set()
    for f in sorted(glob.glob(C + '/*.raw-boundary-delivery-custody.json')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        c = json.load(open(f))['comparison']
        led, tree = set(c.get('delivered_by_ledger') or []), set(c.get('delivered_by_tree') or [])
        if tree - led:
            raise SystemExit(f'tree-only rows in {p}')
        out |= {(p, k) for k in led - tree}
    return out


if __name__ == '__main__':
    # r141: d6_rate.py <census> <out> <expected universe> <expected delivered> [--tree-custody]
    EXP_U, EXP_D = int(sys.argv[3]), int(sys.argv[4])
    if '--tree-custody' in sys.argv[5:]:
        LEDGER_ONLY = ledger_only(sys.argv[1])
    res = main(sys.argv[1], sys.argv[2])
    print('\n'.join(res['log']))
