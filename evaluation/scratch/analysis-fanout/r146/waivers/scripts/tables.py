#!/usr/bin/env python3
"""tables.py <census-dir>: the r141 waiver-group keys measured from a census's receipt tables, with the methods of
analysis-fanout 060 (br3.py, tabs.py, certs.py), 061 (lenclass.py, q7q8.py, per-program.kv) and 055 (fallback_uses.py).
Prints `key<TAB>value<TAB>detail` lines. Pure Python over the tables; no binary."""
import collections, glob, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import load, PROGS
B = sys.argv[1]
out = []
def emit(k, v, d=''): out.append((k, v, d))
def per(c): return ', '.join(f'{p} {n}' for p, n in sorted(c.items(), key=lambda x: (-x[1], x[0])) if n)
# ---- bridge receipts (060 br3.py) ----
br, bad = load(B, 'raw-boundary-bridge-receipts', strict=True)
def sites(pred, stage='terminal', state='applied'):
    return {(r['prog'], r['site_key']) for r in br if pred(r) and r['stage'] == stage and (state is None or r['state'] == state)}
def planned(pred): return {(r['prog'], r['site_key']) for r in br if pred(r) and r['stage'] == 'plan'}
def progs(s): return collections.Counter(p for p, _ in s)
t1 = sites(lambda r: r['retention_tier'] == 'T1'); t1p = planned(lambda r: r['retention_tier'] == 'T1')
emit('bridge.certified', len(t1), f'records {len(br)}; T1 planned {len(t1p)} applied {len(t1)} dropped {len(t1p) - len(t1)}; {per(progs(t1))}')
emit('bridge.certified.programs', len(progs(t1)), '')
t2 = sites(lambda r: r['retention_tier'] == 'T2'); t2p = planned(lambda r: r['retention_tier'] == 'T2')
ca = sites(lambda r: r['waiver_id'].startswith('c-aliasing')); ti = sites(lambda r: r['waiver_id'].startswith('retention-waiver'))
emit('waiver.waived-bridges', len(t2), f'T2 planned {len(t2p)} applied {len(t2)} dropped {len(t2p) - len(t2)}; c-aliasing v1 {len(ca)} ({len(progs(ca))} programs) + tier-2 {len(ti)}; {per(progs(t2))}')
emit('waiver.waived-bridges.programs', len(progs(t2)), '')
emit('waiver.waived-bridges.tier-2', len(ti), f'{len(progs(ti))} programs: {per(progs(ti))}')
fb = sites(lambda r: r['extent_kind'].startswith('fallback(FALLBACK_SLICE_EXTENT')); fbp = planned(lambda r: r['extent_kind'].startswith('fallback(FALLBACK_SLICE_EXTENT'))
fbk = collections.Counter(r['extent_kind'] for r in br if r['extent_kind'].startswith('fallback(FALLBACK'))
emit('waiver.fallback-extent.bridge-receipts', len(fb), f'planned {len(fbp)} applied {len(fb)} dropped {len(fbp) - len(fb)}; {len(progs(fb))} programs: {per(progs(fb))}; extent_kind values {sorted(fbk)}')
# ---- length classes (061 lenclass.py) ----
def klass(e):
    v = e[len('evidence('):-1]
    if v.startswith('runtime-binding-length') and 'extent-fallback-receipted' in v: return 'slice-length:table-row-under-fallback'
    if v.startswith(('runtime-binding-length', 'delivered-parameter-slice', 'derived-cursor-base', 'sealed-contract:array-field-reborrow', 'sealed-contract:computed-suffix-copy')): return 'slice-length'
    if v.startswith('fallback-base'): return 'fallback-base'
    if re.fullmatch(r'\d+', v) or v.startswith(('nested-descriptor-array', 'literal-bytes')) or re.fullmatch(r'[\d\s()+*a-z_:<>]*as\s+(libc::)?[a-z_]+(\s+as\s+(libc::)?[a-z_]+)*\)?', v) or re.fullmatch(r'core::mem::size_of::<[^>]+>\(\)', v): return 'constant'
    if 'CStr::from_ptr' in v: return 'c-string'
    if v.startswith('associated-argument'): return 'count-argument'
    if v.startswith('sealed-contract:counted-void'): return 'counted-void'
    return 'expression'
ev = {}
for r in br:
    if r['stage'] == 'terminal' and r['state'] == 'applied' and r['extent_kind'].startswith('evidence'):
        ev[(r['prog'], r['site_key'])] = (klass(r['extent_kind']), r['arm'])
def key_of(c, a):
    if c in ('constant', 'expression') and a == 'c': return 'libc-contract-count'
    if c in ('constant', 'expression'): return 'array-or-constant'
    if c == 'slice-length': return 'slice-length'
    if c in ('count-argument', 'counted-void'): return 'count-argument'
    if c == 'c-string': return 'c-string'
    if c in ('slice-length:table-row-under-fallback', 'fallback-base'): return 'fallback-inherited'
    raise SystemExit(f'unmapped length class {c} {a}')
lk = collections.defaultdict(collections.Counter); sub = collections.Counter()
for (p, s), (c, a) in ev.items(): lk[key_of(c, a)][p] += 1; sub[(c, a)] += 1
for k in ('slice-length', 'array-or-constant', 'count-argument', 'libc-contract-count', 'c-string'):
    emit(f'codegen.length.evidence.{k}', sum(lk[k].values()), per(lk[k]))
emit('codegen.length.evidence', sum(sum(lk[k].values()) for k in lk if k != 'fallback-inherited'), f'evidence-labelled distinct sites {len(ev)}')
emit('codegen.length.fallback-inherited', sum(lk['fallback-inherited'].values()),
     f"table rows under fallback {sub[('slice-length:table-row-under-fallback', 'surface')]} + fallback-base {sum(v for (c, a), v in sub.items() if c == 'fallback-base')}; {per(lk['fallback-inherited'])}")
# ---- slice-construction receipts with a fallback extent (060's overlapping receipt line) ----
sc, _ = load(B, 'slice-construction-receipt')
scf = {(r['prog'], r.get('obligation_key', '')) for r in sc if r.get('stage') == 'terminal' and r.get('state') == 'applied' and 'fallback' in r.get('extent_kind', r.get('extent', ''))}
emit('(info) slice-construction-fallback-applied', len(scf), per(progs(scf)))
# ---- licensed lifts, retention, exported waivers, pairs (060 tabs.py) ----
ll, _ = load(B, 'raw-boundary-licensed-lifts')
lf = [r for r in ll if r['extent_class'] == 'fallback']
emit('waiver.extent-lift', len(lf), f"rows {len(ll)}; {len({r['prog'] for r in lf})} programs: {per(collections.Counter(r['prog'] for r in lf))}")
rt, _ = load(B, 'raw-boundary-retention')
rv = collections.Counter(r['verdict'] for r in rt)
for v, k in (('no-retain', 'no-retain'), ('retains', 'retains'), ('unknown', 'unknown')):
    emit(f'codegen.retention.{k}', rv[v], f"rows {len(rt)} in {len({(r['prog'], r.get('function', r.get('callee', '')) ) for r in rt})} functions, {len({r['prog'] for r in rt})} programs, attested {collections.Counter(r.get('attested') for r in rt)}; verdicts {dict(rv)}")
ep, _ = load(B, 'raw-boundary-exported-entry-pairs')
emit('waiver.entry-pairs', len(ep), f"rows of raw-boundary-exported-entry-pairs; receipts {dict(collections.Counter(r['receipt'] for r in ep))}; {len({r['prog'] for r in ep})} programs: {per(collections.Counter(r['prog'] for r in ep))}")
rc, _ = load(B, 'return-certificate-receipts')
xp = [r for r in rc if r['detail'].startswith('exported-producer-waiver')]
emit('waiver.exported-producer', len(xp), f"rows with detail exported-producer-waiver (kind {dict(collections.Counter(r['kind'] for r in xp))}), {len({r['prog'] for r in xp})} programs: " + '; '.join(f"{r['prog']} {r['callee'].split('::')[-1]}" for r in xp))
bp, _ = load(B, 'raw-boundary-box-param-receipt')
xc = [r for r in bp if r['detail'].startswith('exported-consumer-waiver')]
emit('waiver.exported-consumer', len(xc), f"rows with detail exported-consumer-waiver (kind {dict(collections.Counter(r['kind'] for r in xc))}): " + '; '.join(f"{r['prog']} {r['detail'].split('callee=')[-1].split('::')[-1]}" for r in xc))
pr, _ = load(B, 'raw-boundary-pairs')
pv = collections.Counter(r['verdict'] for r in pr); prr = collections.Counter((r['verdict'], r['reason']) for r in pr)
pdet = f"rows {len(pr)}, {len({r['prog'] for r in pr})} programs: {per(collections.Counter(r['prog'] for r in pr))}"
emit('codegen.pairs.clear', pv['clear'], f"the {pv['clear']} clear rows: {per(collections.Counter(r['prog'] for r in pr if r['verdict'] == 'clear'))} (of " + pdet + f"); clear reasons {dict(collections.Counter(r['reason'] for r in pr if r['verdict'] == 'clear'))}")
emit('codegen.pairs.overlapping', pv['overlapping'], f"overlapping reasons {dict(collections.Counter(r['reason'] for r in pr if r['verdict'] == 'overlapping'))}; roles {dict(collections.Counter(r['role'] for r in pr if r['verdict'] == 'overlapping'))}")
emit('codegen.pairs.overlapping.raw-view', prr[('overlapping', 'a5-fallback-raw-view-role')], '')
emit('codegen.pairs.overlapping.proof-accepted', prr[('overlapping', 'pair-proof-accepted')], '')
emit('codegen.pairs.overlapping.same-object', prr[('overlapping', 'pair-t2-same-object')], '')
emit('codegen.pairs.overlapping.held', sum(v for (vv, rr), v in prr.items() if vv == 'overlapping' and rr.startswith('held-no-proof')),
     str({rr: v for (vv, rr), v in prr.items() if vv == 'overlapping' and rr.startswith('held')}))
# ---- sibling-predicate audit (060 certs.py) ----
pairs = {}; conflict = 0
for f in sorted(glob.glob(B + '/*.raw-boundary-sibling-predicate-audit.json')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    for r in json.load(open(f))['audit']['rows']:
        for s in r.get('siblings', []):
            pf = s.get('proof') or {}
            L, R = pf.get('left_site'), pf.get('right_site')
            if not L or not R: continue
            k = (p, L['caller'], L['block'], L['statement_index'], L['callee_definition'], tuple(sorted((L['argument_index'], R['argument_index']))), L.get('slot_depth'), R.get('slot_depth'))
            v = (pf.get('outcome'), pf.get('family'), pf.get('reason'))
            if k in pairs and pairs[k] != v: conflict += 1
            pairs[k] = v
emit('codegen.pair-audit.pairs', len(pairs), f'conflicting duplicates {conflict}')
nr = [k for k, v in pairs.items() if v[2] == 'a5-not-proven-disjoint']
emit('codegen.pair-audit.not-proven', len(nr), per(collections.Counter(k[0] for k in nr)))
ap = [k for k, v in pairs.items() if v[2] == 'a5-proven-disjoint']
emit('codegen.pair-audit.analysis-proven', len(ap), f"families {dict(collections.Counter(pairs[k][1] for k in ap))}; {len({k[0] for k in ap})} programs")
cert = [k for k, v in pairs.items() if v[2] and v[2].startswith('pair-disjoint')]
emit('codegen.pair-cert.total', len(cert), f"reasons outside the named kinds: {sorted({pairs[k][2] for k in cert} - {'pair-disjoint:' + x for x in ['type-rule','distinct-roots','distinct-roots:allocator-contract','allocation-identity:allocator-contract','disjoint-fields','null-operand','fresh-stack-address','parameter-pair','read-read-shared','exported-entry-waiver','static-vs-entry:exported-entry-static-waiver']})}; other proof reasons {sorted({v[2] for v in pairs.values()} - {pairs[k][2] for k in cert} - {'a5-not-proven-disjoint','a5-proven-disjoint'})}")
for kind, reason in [('type-rule', 'type-rule'), ('distinct-roots', 'distinct-roots'), ('distinct-roots.allocator-contract', 'distinct-roots:allocator-contract'),
                     ('allocation-identity.allocator-contract', 'allocation-identity:allocator-contract'), ('disjoint-fields', 'disjoint-fields'),
                     ('null-operand', 'null-operand'), ('fresh-stack-address', 'fresh-stack-address'), ('parameter-pair', 'parameter-pair'),
                     ('read-read-shared', 'read-read-shared'), ('exported-entry-waiver', 'exported-entry-waiver'), ('static-vs-entry-waived', 'static-vs-entry:exported-entry-static-waiver')]:
    ks = [k for k in cert if pairs[k][2] == 'pair-disjoint:' + reason]
    c = collections.Counter(k[0] for k in ks)
    emit(f'codegen.pair-cert.{kind}', len(ks), f'{len(c)} programs: {per(c)}')
    if kind == 'static-vs-entry-waived': emit('waiver.entry-static', len(ks), f'{len(c)} programs: {per(c)}')
# ---- emitted trees: global allocator, panic strategy, fallback uses (055) ----
ga = []; fu = collections.Counter(); fdef = collections.Counter()
for d in sorted(glob.glob(f'{B}/emitted-trees/*')):
    p = os.path.basename(d)
    t = ''.join(open(f, errors='replace').read() for f in glob.glob(f'{d}/**/*.rs', recursive=True) if not f.endswith('build.rs'))
    if re.search(r'#\[global_allocator\]\s*static\s+__CRAT_GLOBAL_ALLOCATOR\s*:\s*std::alloc::System\s*=\s*std::alloc::System\s*;', t): ga.append(p)
    fu[p] = len(re.findall(r'\bFALLBACK_SLICE_EXTENT\b', t)) - len(re.findall(r'\bconst\s+FALLBACK_SLICE_EXTENT\b', t))
    fdef[p] = len(re.findall(r'\bconst\s+FALLBACK_SLICE_EXTENT\b', t))
rec = open(f'{B}/census-receipt.txt').read()
emit('output.global-allocator.programs', len(ga), f"trees declaring it {len(ga)} of {len(glob.glob(B + '/emitted-trees/*'))}; receipt global_allocator=declared {len(re.findall(r'global_allocator=declared', rec))}")
ps = collections.Counter(re.findall(r'panic_strategy=(\S+)', rec))
emit('output.panic-strategy', '/'.join(sorted(ps)) if ps else 'n/a', f'receipt panic_strategy counts {dict(ps)}')
emit('waiver.fallback-extent', sum(fu.values()), f"{sum(1 for v in fu.values() if v)} programs: {per(fu)}; const definitions {sum(fdef.values())}")
emit('waiver.fallback-extent.programs', sum(1 for v in fu.values() if v), '')
for p in PROGS: emit(f'(tree) fallback-uses.{p}', fu.get(p, 0), '')
fx = re.findall(r'fallback_slice_extent=(\S+)', rec); emit('(info) receipt fallback_slice_extent', '/'.join(sorted(set(fx))), '')
# ---- verification (061 q7q8.py, per-program.kv) ----
fr, _ = load(B, 'raw-boundary-final-reverts'); so, _ = load(B, 'raw-boundary-subject-outcomes')
held = [r for r in fr if r['attribution'].startswith('held:')]
hc = collections.Counter(r['prog'] for r in held)
emit('verify.held-units', len(held), f"distinct (program, identity) {len({(r['prog'], r['identity']) for r in held})}; {per(hc)}")
emit('verify.held-units.programs', len(hc), '')
tna = [r for r in so if r['exclusion'].startswith('terminal-not-applied')]
unit_of = {(r['prog'], r['identity']): r for r in held}
inheld = [r for r in tna if (r['prog'], r['owner_fn']) in unit_of]
emit('verify.held-units.declarations', len(inheld), f"terminal-not-applied {len(tna)}, in held units {len(inheld)}; {per(collections.Counter(r['prog'] for r in inheld))}; held units with none {sum(1 for k in unit_of if not any((r['prog'], r['owner_fn']) == k for r in inheld))}")
for head in ('dropped-site', 'blocked-subject', 'dependency-class-held', 'a5-fallback-unrenderable', 'intra-class-interval-overlap'):
    us = [r for r in held if r['attribution'].split(':')[1] == head]
    ks = {(r['prog'], r['identity']) for r in us}
    emit(f'verify.held-units.{head}', len(us), per(collections.Counter(r['prog'] for r in us)))
    emit(f'verify.held-units.{head}.declarations', sum(1 for r in inheld if (r['prog'], r['owner_fn']) in ks), '')
heads = collections.Counter(r['attribution'].split(':')[1] for r in held)
emit('(info) held heads', len(heads), str(dict(heads)))
cr = [r for r in held if 'seam-positive-retention' in r['attribution']]
ck = {(r['prog'], r['identity']) for r in cr}
crd = [r for r in inheld if (r['prog'], r['owner_fn']) in ck]
emit('verify.held-units.callee-retains', len(cr), f"{dict(collections.Counter(r['attribution'] for r in cr))}; {per(collections.Counter(r['prog'] for r in cr))}")
emit('verify.held-units.callee-retains.declarations', len(crd), '; '.join(f'{v} rows, exclusion {x}' for x, v in collections.Counter(r['exclusion'] for r in crd).items()))  # r146: the full exclusion string (117's text fix)
gh = [r for r in fr if r['attribution'].startswith('graft-held')]
emit('verify.planning-reverted.graft-held', sum(len(r['named_subject'].split()) for r in gh), '; '.join(f"{r['prog']} {r['identity'].split('::')[-1]} ({r['attribution']}: {len(r['named_subject'].split())})" for r in gh))
cl = [r for r in fr if r['attribution'].startswith('closure:')]
emit('verify.planning-reverted.closure', sum(len(r['named_subject'].split()) for r in cl), '; '.join(f"{r['prog']} {r['identity'].split('::')[-1]} ({r['attribution']}: {len(r['named_subject'].split())})" for r in cl))
dch = [r for r in held if r['attribution'].split(':')[1] == 'dependency-class-held']
emit('verify.dependency-only.units', len(dch) + len(cl), f"held:dependency-class-held {len(dch)} ({'; '.join(r['prog'] + ' ' + r['identity'].split('::')[-1] for r in dch)}) + closure units {len(cl)} ({'; '.join(r['prog'] + ' ' + r['identity'].split('::')[-1] for r in cl)})")
emit('(info) final-reverts attribution heads', len(fr), str(dict(collections.Counter(r['attribution'].split(':')[0] for r in fr))))
kv = {}
for l in open(f'{B}/per-program.kv'):
    d = dict(x.split('=', 1) for x in l.split() if '=' in x); kv[d['program']] = d
vr = {p: int(d['raw_boundary_verify_rounds']) for p, d in kv.items()}
emit('verify.first-check-passed.programs', sum(1 for v in vr.values() if v == 1), f"rounds {', '.join(f'{p} {v}' for p, v in sorted(vr.items()) if v != 1)}")
emit('verify.rounds.max', max(vr.values()), '')
emit('verify.search.programs', sum(1 for d in kv.values() if int(d.get('raw_boundary_bisect_probes', 0)) > 0 or int(d.get('raw_boundary_class_bisect_probes', 0)) > 0), '')
emit('verify.unchanged-output.programs', sum(1 for d in kv.values() if d.get('raw_boundary_outcome_kind') != 'emitted'), str(dict(collections.Counter(d.get('raw_boundary_outcome_kind') for d in kv.values()))))
emit('verify.atom-takeback.declarations', sum(int(d.get('raw_boundary_atom_successes', 0)) for d in kv.values()),
     f"atom_ambiguous {', '.join(p + ' ' + d['raw_boundary_atom_ambiguous'] for p, d in sorted(kv.items()) if d.get('raw_boundary_atom_ambiguous', '0') != '0')}; no atom counters: {[p for p, d in sorted(kv.items()) if 'raw_boundary_atom_successes' not in d]}")
for k, v, d in out: print(f'{k}\t{v}\t{d}')
