#!/usr/bin/env python3
"""r132 analysis step (5): join ours58's TOOL-MADE sites (toolmade-ours58.tsv) to batch 58's receipts.

Receipts read (main/batch58/<p>.*.tsv, read-only):
  P5   raw-boundary-premise-bridge-dereferenceable  (premise=bridge-dereferenceable)
  §77  the emitted text: a slice construction (or Box of one) whose arguments hold `FALLBACK_SLICE_EXTENT`
       (cross-checked against slice-construction-receipt / bridge receipts with extent `fallback(...)`)
  P6   raw-boundary-allocator-contract-receipt, kind=admitted   (the relay's "allocator contract (P6)")
  R534 raw-boundary-box-param-receipt detail `exported-consumer-waiver`, and every exposure-wrapper site
       (a call-arg into crat's twin `__crat_safe_f`)
  BR   raw-boundary-bridge-receipts, stage=terminal state=applied, found_form=raw and expected_form not raw (a raw value
       bridged into a safe form): the adapter (bridge_kind), its retention tier (T1 certificate / T2 waiver / none)
The receipts' coordinates are on the DERIVED substrate (benchmarks/rs-crown-derived/<p>, the census input), not on the
emitted tree, so the join is textual: same function (last path segment, `__crat_safe_` removed), the same callee for a
call-arg (when the receipt names one), and the receipt's operand text (derived source at its span, whitespace removed)
contained in the site's expression text (whitespace removed). Receipts are assigned one-to-one per site in source order.
"""
import csv, glob, os, re
from collections import Counter, defaultdict

csv.field_size_limit(10**9)
R = 'scratch/analysis-fanout/r132'
A = f'{R}/analysis'
B58 = 'scratch/main/batch58'
DERIVED = 'crat/benchmarks/rs-crown-derived'


def last(f):
    s = f.rsplit('::', 1)[-1]
    s = re.sub(r'::<.*', '', s)
    return s[len('__crat_safe_'):] if s.startswith('__crat_safe_') else s


def ns(t):
    return re.sub(r'\s+', '', t or '')


def load(p, kind):
    f = f'{B58}/{p}.{kind}.tsv'
    return list(csv.DictReader(open(f), delimiter='\t')) if os.path.exists(f) else []


class Derived:
    def __init__(self, p):
        d = f'{DERIVED}/{p}'
        root = next(f for f in ('lib.rs', 'c2rust-lib.rs') if os.path.exists(f'{d}/{f}'))
        self.b = open(f'{d}/{root}', 'rb').read()
        self.lines = self.b.decode('utf-8', 'replace').split('\n')
        self.fns = [(m.start(), m.group(1).decode()) for m in re.finditer(rb'\bfn\s+([A-Za-z_]\w*)', self.b)]
        self.starts = [m[0] for m in self.fns]

    def text(self, lo, hi):
        return self.b[lo:hi].decode('utf-8', 'replace')

    def fn_at(self, lo):
        import bisect
        i = bisect.bisect_right(self.starts, lo) - 1
        return self.fns[i][1] if i >= 0 else None

    def text_lc(self, l1, c1, l2, c2):
        if l1 == l2:
            return self.lines[l1 - 1][c1 - 1:c2 - 1]
        return self.lines[l1 - 1][c1 - 1:] + ' ' + ' '.join(self.lines[l1:l2 - 1]) + ' ' + self.lines[l2 - 1][:c2 - 1]


def defindex_map(p):
    m = {}
    for f in glob.glob(f'{B58}/{p}.*.tsv'):
        for mm in re.finditer(r'DefId\(0:(\d+) ~ [^\]]*\]::([^)]*)\)', open(f, errors='replace').read()):
            m[mm.group(1)] = mm.group(2)
    return m


SAFE_FORMS_RAW = {'raw'}


def main():
    sites = list(csv.DictReader(open(f'{A}/toolmade-ours58.tsv'), delimiter='\t'))
    out = []
    per = defaultdict(Counter)
    for p in sorted(set(s['program'] for s in sites)):
        ps = [s for s in sites if s['program'] == p]
        der = Derived(p)
        dmap = defindex_map(p)
        # ---- P5
        p5 = []
        for r in load(p, 'raw-boundary-premise-bridge-dereferenceable'):
            if r['site_kind'] == 'call-bridge':
                m = re.match(r'(.*)@<program>/[^:]+:(\d+):(\d+): (\d+):(\d+)', r['site'])
                caller, op = (last(m.group(1)), der.text_lc(*map(int, m.groups()[1:]))) if m else (None, '')
                p5.append(dict(kind='call', fn=caller, callee=last(r['function']), op=ns(op), binding=r['binding'],
                               label=f'P5:{r["site_kind"]}', used=False))
            else:
                p5.append(dict(kind='bind', fn=last(r['function']), callee=None, op=ns(r['pointer']),
                               binding=r['binding'], label=f'P5:{r["site_kind"]}', used=False))
        # ---- P6
        p6 = defaultdict(set)
        for r in load(p, 'raw-boundary-allocator-contract-receipt'):
            if r.get('kind') == 'admitted' and r.get('subject') and '::' in r['subject']:
                fn, loc = r['subject'].rsplit('::', 1)
                p6[last(fn)].add(loc)
        # ---- R534
        r534 = set()
        for r in load(p, 'raw-boundary-box-param-receipt'):
            if r['kind'] == 'admitted' and 'exported-consumer-waiver' in r['detail']:
                m = re.search(r'callee=(\S+)', r['detail'])
                if m:
                    r534.add(last(m.group(1)))
        # ---- bridge receipts
        br = []
        for r in load(p, 'raw-boundary-bridge-receipts'):
            if r['stage'] != 'terminal' or r['state'] != 'applied' or r['lo'] in ('0', '-', ''):
                continue
            zero = r['argument_kind'] in ('addr-of', 'addr-of-mut') and r['expected_form'] != 'raw'
            if not zero and (r['found_form'] != 'raw' or r['expected_form'] == 'raw'):
                continue
            lo, hi = int(r['lo']), int(r['hi'])
            m = re.match(r'local:(\d+)$', r['callee'])
            callee = last(dmap[m.group(1)]) if m and m.group(1) in dmap else None
            if r['callee'].startswith('foreign:'):
                callee = last(r['callee'][len('foreign:'):])
            is_arg = bool(re.match(r'arg\d+', r['position']))
            br.append(dict(fn=der.fn_at(lo), callee=callee, op=ns(der.text(lo, hi)), lo=lo, used=False, is_arg=is_arg,
                           label=f'BR{"0" if zero else ""}:{r["bridge_kind"]}|tier={r["retention_tier"]}|waiver={r["waiver_id"]}'
                                 f'|extent={r["extent_kind"].split("(")[0]}'))
        br.sort(key=lambda x: x['lo'])
        ps.sort(key=lambda s: (s['file'], int(s['line']), int(s['col'])))
        for s in ps:
            labels = []
            e = ns(s['expr'])
            fn = last(s['fn'])
            callee = last(s['dest_detail']) if s['dest'] == 'call-arg' else None
            cc = s['call_class']
            if (cc.startswith('from_raw_parts') or cc == 'Box::from_raw') and 'FALLBACK_SLICE_EXTENT' in e:
                labels.append('S77:fabricated-extent')
            for r in p5:
                if r['used'] or r['fn'] != fn:
                    continue
                if r['kind'] == 'call':
                    ok = s['dest'] == 'call-arg' and callee == r['callee'] and r['op'] and r['op'] in e
                else:
                    ok = (s['dest'] in ('decl', 'assign') and s['dest_detail'] == r['binding']) or \
                         (r['op'] and len(r['op']) > 3 and r['op'] in e)
                if ok:
                    r['used'] = True
                    labels.append(r['label'])
                    break
            if fn in p6 and (s['dest_detail'] in p6[fn] or 'BrotliAllocate' in e) and cc in (
                    'Box::from_raw', 'from_raw_parts', 'from_raw_parts_mut'):
                labels.append('P6:allocator-contract')
            if s['boundary'] == 'yes':
                labels.append('R534:exported-consumer-waiver' if cc == 'Box::from_raw' and callee in r534
                              else 'exposure-wrapper')
            for r in br:
                if r['used'] or r['fn'] != fn or not r['op'] or r['op'] not in e:
                    continue
                if r['is_arg'] and (s['dest'] != 'call-arg' or (r['callee'] is not None and callee != r['callee'])):
                    continue                    # a call-argument bridge joins only a call-arg site of the same callee
                r['used'] = True
                labels.append(r['label'])
                break
            prim = primary(labels)
            if prim == 'unreceipted':
                if s['helper_module'] == 'yes':
                    prim = 'unreceipted:helper-module'
                elif cc.startswith('from_raw_parts'):
                    prim = 'unreceipted:evidence-extent-construction'
                elif s['from_idiom'] == 'yes':
                    prim = 'unreceipted:from-c2rust-reference'
                else:
                    prim = 'unreceipted:other'
            per[p][prim] += 1
            per['TOTAL'][prim] += 1
            if s['counted'] == 'yes':
                per[p]['counted.' + prim] += 1
                per['TOTAL']['counted.' + prim] += 1
            out.append(dict(s, receipts=';'.join(labels) or '-', primary=prim))
        per[p]['p5_rows'] = len(p5)
        per[p]['p5_matched'] = sum(r['used'] for r in p5)
        per[p]['br_rows'] = len(br)
        per[p]['br_matched'] = sum(r['used'] for r in br)
        for k in ('p5_rows', 'p5_matched', 'br_rows', 'br_matched'):
            per['TOTAL'][k] += per[p][k]
    cols = list(sites[0].keys()) + ['receipts', 'primary']
    with open(f'{A}/toolmade-ours58-receipts.tsv', 'w') as f:
        w = csv.DictWriter(f, cols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        for r in out:
            w.writerow(r)
    keys = sorted(set(k for c in per.values() for k in c))
    with open(f'{A}/ours58-receipt-join.tsv', 'w') as f:
        f.write('program\t' + '\t'.join(keys) + '\n')
        for p in sorted(per, key=lambda x: (x == 'TOTAL', x)):
            f.write(p + '\t' + '\t'.join(str(per[p][k]) for k in keys) + '\n')
    for k in keys:
        print(k, per['TOTAL'][k])


ORDER = ['S77', 'P5', 'P6', 'R534', 'exposure-wrapper', 'BR-T2', 'BR-T1', 'BR-none', 'BR-zero-syntax']


def primary(labels):
    """the one label a site is tabulated under (all labels are kept in `receipts`)"""
    tags = set()
    for l in labels:
        if l.startswith('BR0:'):
            tags.add('BR-zero-syntax')
        elif l.startswith('BR:'):
            t = re.search(r'tier=(\w+)', l).group(1)
            tags.add('BR-T2' if t == 'T2' else 'BR-T1' if t == 'T1' else 'BR-none')
        else:
            tags.add(l.split(':')[0])
    for o in ORDER:
        if o in tags:
            return o
    return 'unreceipted'


if __name__ == '__main__':
    main()
