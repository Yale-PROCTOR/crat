#!/usr/bin/env python3
"""r141 rq5_forms_tree.py: rq5_forms_d6.py with an optional 6th argument --tree-custody (the count by the emitted tree); without it the r140 copy unchanged
rq5_forms_d6.py (analysis-fanout 112, relay 138: copy of r133 g088b/rq5/rq5_forms_ef.py; ONLY change: D6 -- the universe also admits a
subject whose census decision is a safe form whatever its outcome; an UNDELIVERED raw-family subject so admitted takes its census
decision as its family (box -> the box / boxslice split below), a delivered one keeps the emitted-form reading)
rq5_forms.py (r095 copy: POS may be `--emitted-form`, reading step (1) from the census's subject-outcomes emitted_form)
rq5_forms.py <census> <rows.tsv> <positions-dir> <main-155 rq5-rows.tsv (its R454 group)> <fatfacts.tsv>: relay 055 item 2 / R775-1 -- the manuscript's Table
`tab:rq5` per form on the licensed reading (analysis-fanout 036).

Universe: the census's decided-safe subjects (a safe family, or delivered), less R454's `let ref mut` bindings
(= rq1.frame-safe-decisions). Form of a subject:
  ref / cursor / slice : the census family (`ref`, `cursor`, `slice`);
  optional             : `optref` or `slice` (an optional slice is in the slice row);
  box                  : `box` or `boxslice`;
  raw family delivered : by its emitted form (box -> box, ref -> ref).
The split of `optional` / `box` is read, in order, from (1) the emitted type of a delivered subject (the typed
counter's positions on the frame's tree, twin reading), (2) the census's own candidate form for the subject
(mechanical-obligations `expected_form`, additive-family-fallbacks candidates, the allocator-contract shape), and
(3) the model's own fatness fact for the slot (L01^13 cache QualifierFacts: array-like -> slice), and otherwise
(4) left `unresolved` and counted. Columns:
  withheld  = rows whose cause (rows.tsv) is side-condition
  licensed  = decided - withheld
  delivered = realized-as-predicted
  reverted  = delivery `reverted`, not withheld
  held      = cause `held` (the I/O pass's stream identities), not reverted
  notplaced = the rest (degraded for a typed reason)"""
import collections, csv, glob, json, os, re, sys
csv.field_size_limit(10 ** 9)
C, ROWS, POS, R454, FAT = sys.argv[1:6]
LO = set()  # r141: '--tree-custody' as 6th argument = the count by the emitted tree (delivery-custody ledger-only rows are not delivered)
if '--tree-custody' in sys.argv[6:]:
    for cf in sorted(glob.glob(C + '/*.raw-boundary-delivery-custody.json')):
        cp = os.path.basename(cf).split('.raw-boundary')[0]
        cc = json.load(open(cf))['comparison']
        led, tree = set(cc.get('delivered_by_ledger') or []), set(cc.get('delivered_by_tree') or [])
        if tree - led:
            raise SystemExit('tree-only rows in ' + cp)
        LO |= {(cp, k) for k in led - tree}
EMITTED_FORM = POS == '--emitted-form'
FATUSED = []
fat = {}
for l in open(FAT):
    pp, slot, v = l.rstrip('\n').split('\t'); fat[(pp, slot)] = v
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
cause = {r['subject_key']: r['cause'] for r in csv.DictReader(open(ROWS), delimiter='\t')}
excl = {(r['program'], r['subject_key']) for r in csv.DictReader(open(R454), delimiter='\t') if r['group'] == 'R454'}

def slice_like(form):
    return form is not None and ('slice' in form)

def short(owner):
    return owner.rsplit('::', 1)[-1].replace('__crat_safe_', '')

out = collections.defaultdict(collections.Counter)
how = collections.Counter(); unresolved = []
for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    subj = {r['subject_key']: r for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-subjects.tsv'), delimiter='\t')}
    # (1) emitted types (twin reading: __crat_safe_<f> read as <f>)
    pos = {}
    pf = f'{POS}/{p}/positions.tsv'
    if os.path.exists(pf):
        for r in csv.DictReader(open(pf), delimiter='\t'):
            if r['depth'] == '0' and r['layer'] == '0' and r['kind'] in ('param', 'local', 'return'):
                pos.setdefault((short(r['owner']), r['name']), r['form'])
    # (2) candidate forms the census records
    cand = collections.defaultdict(set)
    mo = f'{C}/{p}.raw-boundary-mechanical-obligations.tsv'
    if os.path.exists(mo):
        for r in csv.DictReader(open(mo), delimiter='\t'):
            m = re.match(r'local:\d+:(\d+):depth=0', r['subject_key'] or '')
            if m:
                cand[(short(r['owner_path']), m.group(1))].add(r['expected_form'])
    af = f'{C}/{p}.raw-boundary-additive-family-fallbacks.json'
    if os.path.exists(af):
        def walk(x):
            if isinstance(x, list):
                if len(x) == 3 and all(isinstance(y, str) for y in x) and '#' in x[0]:
                    k = x[0]; m = re.match(r'(.*)::([^:#]+)#(\d+)$', k)
                    if m: cand[(short(m.group(1)), m.group(3))].add(x[2])
                for y in x: walk(y)
            elif isinstance(x, dict):
                for y in x.values(): walk(y)
        walk(json.load(open(af)))
    ac = f'{C}/{p}.raw-boundary-allocator-contract-receipt.tsv'
    if os.path.exists(ac):
        for r in csv.DictReader(open(ac), delimiter='\t'):
            if r['kind'] == 'admitted' and (r['detail'] or '').startswith('shape=slice'):
                fn, name = r['subject'].split('::')[-2:]
                cand[('NAME', fn, name)].add('box-slice')
    for o in csv.DictReader(open(f), delimiter='\t'):
        k = o['subject_key']; s = subj.get(k, {}); fam = s.get('family', o['family'])
        dlv = o['delivery'] == 'realized-as-predicted' and (p, o['subject_key']) not in LO
        if fam == 'raw' and not dlv and s.get('decision') in SAFE:  # D6 (relay 138)
            fam = s['decision']; how['D6: undelivered raw family, by census decision'] += 1
        if not (fam in SAFE or dlv) or (p, k) in excl or o.get('exclusion', '').startswith('universe-exclusion'):
            continue
        m = re.match(r'(.*)::([^:#]+)#(\d+)$', k); fn, name, loc = short(m.group(1)), m.group(2), m.group(3)
        if fam == 'raw':
            form = 'box' if o['emitted_form'] == 'box' else 'ref'; how['raw family, by emitted form'] += 1
        elif fam in ('ref', 'cursor', 'slice'):
            form = fam
        else:
            e = pos.get((fn, name)) if dlv else None
            if dlv and EMITTED_FORM:  # r095: the census's own emitted_form column (the typed counter's reading, without running it)
                e = {'optional': 'opt-ref', 'opt-slice': 'opt-slice-ref', 'box': 'box', 'box-slice': 'box-slice',
                     'opt-box-slice': 'opt-box-slice'}.get(o['emitted_form'], e)
            cs = cand.get((fn, loc), set()) | cand.get(('NAME', fn, name), set())
            if e is not None and e not in ('raw', 'raw-mut', 'raw-const', 'unmatched'):
                sl = slice_like(e); how[f'{fam} split by emitted type'] += 1
            elif cs and not any(x in ('raw', '-', '') for x in cs) or any(slice_like(x) or 'ref' in x or 'box' in x for x in cs):
                sl = any(slice_like(x) for x in cs); how[f'{fam} split by census candidate form'] += 1
            elif (p, f"{m.group(1)}::_{loc}@d0") in fat:
                sl = fat[(p, f"{m.group(1)}::_{loc}@d0")].endswith('array-like'); how[f'{fam} split by the model fatness fact'] += 1; FATUSED.append((p, f"{m.group(1)}::_{loc}@d0", fat[(p, f"{m.group(1)}::_{loc}@d0")], fam, o['delivery']))
            else:
                sl = None; how[f'{fam} unresolved'] += 1; unresolved.append((p, k, fam, o['delivery']))
            if fam == 'optional':
                form = 'slice' if sl else 'optref'
            else:
                form = 'boxslice' if sl else 'box'
        c = cause.get(k)
        out[form]['decided'] += 1
        if c == 'side-condition':
            out[form]['withheld'] += 1
        elif dlv:
            out[form]['delivered'] += 1
        elif o['delivery'] == 'reverted':
            out[form]['reverted'] += 1
        elif c == 'held':
            out[form]['held'] += 1
        else:
            out[form]['notplaced'] += 1
FORMS = ['ref', 'optref', 'slice', 'cursor', 'box', 'boxslice']
print('form\tdecided\twithheld\tlicensed\tdelivered\treverted\tnotplaced\theld')
tot = collections.Counter()
for fm in FORMS:
    x = out[fm]; x['licensed'] = x['decided'] - x['withheld']
    for k in ('decided', 'withheld', 'licensed', 'delivered', 'reverted', 'notplaced', 'held'): tot[k] += x[k]
    if not (x['licensed'] == x['delivered'] + x['reverted'] + x['notplaced'] + x['held']):
        raise SystemExit(fm)
    print(fm, *(x[k] for k in ('decided', 'withheld', 'licensed', 'delivered', 'reverted', 'notplaced', 'held')), sep='\t')
print('total', *(tot[k] for k in ('decided', 'withheld', 'licensed', 'delivered', 'reverted', 'notplaced', 'held')), sep='\t')
print('# how the optional / box split was read:', dict(how))
print('# unresolved (left in optref / box):', len(unresolved))
for u in unresolved: print('#  ', *u)
print('# fatness facts used:', len(FATUSED))
for u in FATUSED: print('#F ', *u)
