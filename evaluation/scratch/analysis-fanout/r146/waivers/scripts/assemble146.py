#!/usr/bin/env python3
"""assemble146.py (relay 146): stage the waiver-group keys (the key set of r141/waivers/staged.tsv) at 60s' (main/batch60sp,
head 32d966b9f) from the re-pointed producers' outputs in ../out146: tables.py, group_i.py / group_ii.py (054; group (ii)
on the rejoined reader, 117's value fix), deref_keys.py (062), the release-tool aggregate (061), lend_waiver_sites.py (038,
streamed), rq4_pair_sites.py (wave-6o 097's instrument step), contracts.py. CONTROL: the same producers on main/batch58pps39
(and the S39 cache, code 3eaf5228d) must reproduce r141/waivers/staged.tsv's value_58ppp exactly (with 117's 202 -> 203), and
that value must be the record's current value; the .before keys' control is 055's method on main/b54p. Fails closed."""
import collections, re
S = 'scratch/analysis-fanout/r146/waivers'; O = S + '/out146'; M = 'scratch/main'
R141 = 'scratch/analysis-fanout/r141/waivers/staged.tsv'; REC = 'scratch/analysis-fanout/r146/record-current.md'
HEAD = '32d966b9fc2ef56fcd40e95ee762f73b0e0be70a'; CTRL_REV = '3eaf5228d'
CS = ['b54p', 'batch58pps39', 'batch60sp']; NOW = 'batch60sp'; CT = 'batch58pps39'
# ---- the key set, the 58''' expected values, the record ----
r141 = [l.rstrip('\n').split('\t') for l in open(R141).read().splitlines()[1:]]
KEYS = [r[0] for r in r141]
if len(KEYS) != 163 or len(set(KEYS)) != 163: raise SystemExit('key set is not 163 distinct keys')
EXP = {r[0]: (r[2], r[3]) for r in r141}
EXP['codegen.rewrite.slice-construction.sites'] = ('203', 'differs')  # 117's value fix (the rejoined reader)
ROWRE = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) \| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")
RECV = {}
for l in open(REC, encoding='utf-8'):
    m = ROWRE.match(l.rstrip('\n'))
    if m and m['key'] in EXP:
        if m['key'] in RECV: raise SystemExit('duplicate record row ' + m['key'])
        RECV[m['key']] = m['value']
if set(RECV) != set(KEYS): raise SystemExit(f'record lacks {sorted(set(KEYS) - set(RECV))}')
V = {c: {} for c in CS}; DET = {c: {} for c in CS}; SRC = {}
def put(c, k, v, d='', src=''):
    V[c][k] = str(v); DET[c][k] = d
    if src: SRC[k] = src
def T(s): return s.replace('{C}', f'{M}/batch60sp')
for c in CS:
    for l in open(f'{O}/tables-{c}.tsv'):
        k, v, d = (l.rstrip('\n').split('\t') + [''])[:3]
        put(c, k, v, d, T(f'{S}/scripts/tables.py over {{C}}/*.tsv (and emitted-trees, census-receipt.txt, per-program.kv)'))
    rows = [l.rstrip('\n').split('\t') for l in open(f'{O}/group-i-{c}.tsv')]
    hdr = rows[0]
    for j, kind in enumerate(hdr[1:], 1):
        per = ', '.join(f'{r[0]} {r[j]}' for r in rows[1:-2] if r[j] != '0')
        put(c, f'codegen.rewrite.{kind}.sites', rows[-2][j], per, T(f'{S}/scripts/group_i.py {{C}} (analysis-fanout 054 verbatim; emitted-trees minus crat/benchmarks/rs-crown-derived)'))
        put(c, f'codegen.rewrite.{kind}.programs', rows[-1][j], '', SRC[f'codegen.rewrite.{kind}.sites'])
    for l in open(f'{O}/group-ii-{c}.tsv').read().splitlines()[1:]:
        kind, table, n, p = l.split('\t')
        put(c, f'codegen.rewrite.{kind}.sites', n, table, T(f'{S}/scripts/group_ii.py {{C}} (analysis-fanout 054, main 134f definitions, read with the rejoined reader common.load_rejoin = 117 value fix)'))
        put(c, f'codegen.rewrite.{kind}.programs', p, table, SRC[f'codegen.rewrite.{kind}.sites'])
    if c == 'b54p': continue
    for l in open(f'{O}/deref-keys-{c}.tsv'):
        k, v, d = l.rstrip('\n').split('\t')
        put(c, f'codegen.rewrite.{k}.sites', v, d, f'{S}/scripts/deref_keys.py over {O}/tools-batch60sp/rows.tsv (062 deref-tool binary scratch/analysis-fanout/r083/taskB/deref-tool/target/release/deref-tool, classes = 062 classify.py; owner-lend per-program split box / option-box)')
    ag = open(f'{O}/tools-{c}/aggregate.out').read()
    def cnt(name): m = re.search(rf'^output {re.escape(name)} (\d+) (.*)$', ag, re.M); return (int(m.group(1)), m.group(2)) if m else (0, '')
    ir, irv, fr_, frv = cnt('into_raw.call'), cnt('into_raw.valpath'), cnt('from_raw.call'), cnt('from_raw.valpath')
    fg = sum(cnt(n)[0] for n in ('forget.call', 'forget.valpath', 'ManuallyDrop.call', 'ManuallyDrop.valpath', 'ManuallyDrop.type', 'leak.call', 'leak.valpath'))
    sec5 = ag.split('## (5)')[1].split('## (6)')[0]
    mm = re.findall(r"MISMATCH \('([^']+)', '([^']+)'\) (\S+) (\d+) (\d+)", sec5)
    real = [m for m in mm if m[2] != m[1].split('::')[-1]]
    tot = re.search(r'^TOTAL\t(\d+)\t(\d+)\t(\d+)', ag, re.M).groups()
    RT = f'release-tool binary scratch/analysis-fanout/r080/release-tool/target/release/release-tool (061, syn 2) + {S}/scripts/release_aggregate.py over {O}/tools-batch60sp/out.tsv'
    put(c, 'codegen.rewrite.box-into-raw.sites', ir[0] + irv[0], f'{ir[0]} calls {ir[1]} + {irv[0]} value paths {irv[1]}', RT)
    put(c, 'codegen.rewrite.box-from-raw.sites', fr_[0] + frv[0], f'{fr_[0]} calls {fr_[1]} + {frv[0]} value paths', RT)
    put(c, 'codegen.rewrite.forget.sites', fg, 'mem::forget / ManuallyDrop / Box::leak in the outputs', RT)
    put(c, 'waiver.recursive-leak', fg, 'forget(replace(..)) / ManuallyDrop / Box::leak in the outputs', RT)
    put(c, 'codegen.release.functions-differ', len(real), f'input free {tot[0]} = output free {tot[1]} + drop {tot[2]}; folded mismatches {len(mm)} = the exposure wrapper forward call only ({"; ".join(m[0] + " " + m[1].split("::")[-1] for m in mm)}) when real = 0; real mismatches {[m[:3] for m in real]}', RT)
    put(c, '(info) free-drop', f'{tot[0]} {tot[1]} {tot[2]}')
    lw = open(f'{O}/lend-{c}.out').read(); m = re.search(r'total receipts (\d+)', lw)
    per = ', '.join(f'{a} {b}' for a, b in re.findall(r'^(\S+)\t(\d+)\t', lw, re.M))
    put(c, 'waiver.lend-indirect-call.sites', m.group(1), per, f'{S}/scripts/lend_waiver_sites.py (038 parameterized, tail fixed; streamed, MemAvailable >= 30 GiB) over worktrees/era5c-r215-kindorder/cache/era5b-model-cache-v1/*.json (twenty entries = {M}/batch60sp-manifest.tsv)')
    put(c, '(info) lend-sites', '\n'.join(sorted(l for l in lw.splitlines() if l.startswith('    '))))
    rq = re.search(r"TOTAL \{'sites': (\d+), '(\w+)': (\d+), '(\w+)': (\d+)\}", open(f'{O}/rq4-{c}.out').read()).groups()
    put(c, 'rq4.pair.sites', rq[0], f'mapping only: {rq[1]} {rq[2]}, {rq[3]} {rq[4]}', f'{S}/scripts/rq4_pair_sites.py {M}/batch60sp (wave-6o 097 docs agents/tools/runtime/pair_sites.py instrument step: raw-boundary-pairs rows role raw-view/primary, mapped onto emitted calls; no type-check round, no run)')
ct = open(f'{O}/contracts.out').read()
def cline(rev):
    l = [x for x in ct.splitlines() if x.startswith(rev)][0]
    g = lambda pat: re.search(pat, l).group(1)
    return dict(callees=g(r'callees (\d+)'), positions=g(r'positions (\d+)'), release=len(eval(g(r'release (\[[^\]]*\])'))), noret=g(r'no-retain (\d+)'), stream=g(r'stream-family symbols (\[[^\]]*\])'))
for c, rev in ((CT, CTRL_REV), (NOW, HEAD)):
    d = cline(rev); CTS = f'{S}/scripts/contracts.py {HEAD[:9]} (git show of crates/pointer_replacer/src/bo_rewriter/decision/raw_boundary_contracts.rs: TABLE rows + is_stdio_stream_position)'
    put(c, 'design.libc-contract-callees', d['callees'], f"TABLE {d['positions']} positions + stream family {d['stream']}", CTS)
    put(c, 'design.libc-contract-callees.no-retain', d['noret'], '', CTS); put(c, 'design.libc-contract-callees.release', d['release'], 'free, fclose (Consume), realloc (AtomicSourceSink)', CTS)
    put(c, 'design.libc-contract-positions', d['positions'], '', CTS)
cb = {c: open(f'{O}/calleebound-{c}.txt').read().splitlines()[-1] for c in (CT, NOW)}
# ---- stage ----
def clean(s): return re.sub(r'\s+', ' ', s.replace('|', '/').replace('\t', ' ')).strip()
NOTE = {}
exec(open(S + '/scripts/notes146.py').read())
ROW = []; CMP = []; CTRL = collections.Counter()
for k in KEYS:
    now = RECV[k]; exp, vd141 = EXP[k]; vct, v60 = V[CT].get(k), V[NOW].get(k)
    if k.startswith('waiver.fallback-extent.before'):
        p = k.split('.')[-1]; tk = 'waiver.fallback-extent' if p == 'before' else '(tree) fallback-uses.' + p.replace('jsonh', 'json.h')
        ctrl = V['b54p'].get(tk)
        if ctrl != now: raise SystemExit(f'CONTROL MISS {k}: record {now} vs b54p {ctrl}')
        CTRL['before-b54p'] += 1; CMP.append((k, now, exp, ctrl, vct, V[NOW].get(tk)))
        ROW.append((k, now, now, 'carried', f"a fixed baseline, not frame-dependent: the 54' uses of FALLBACK_SLICE_EXTENT kept as the BEFORE of the callee-bound analysis (relay 082 item 1; waiver.fallback-extent is the AFTER). Control: 055's method on {M}/b54p/emitted-trees gives {ctrl} = the record. For reference the same count on {M}/batch60sp/emitted-trees is {V[NOW].get(tk)} (on {M}/batch58pps39: {V[CT].get(tk)}); method {S}/scripts/tables.py (055's fallback_uses.py regex)"))
        continue
    if k in ('waiver.sibling-parameters', 'waiver.sibling-unknown'):
        if vd141 != 'carried': raise SystemExit(k)
        CMP.append((k, now, exp, '', '', ''))
        ROW.append((k, now, now, 'carried', "EMPTY ON PURPOSE (analysis-fanout 060; disposition (d) drop, analysis-fanout 086): the quantity is undefined (the census has no column for a reference parameter beside a pending row, nor an unknown envelope) and R833 removed the pair waiver; nothing to measure at any frame")); continue
    if k == 'codegen.length.constant-bound.record':
        CMP.append((k, now, exp, '', '', ''))
        ROW.append((k, now, '', 'not-at-60sp', f"the 67 came from wave-4 080's logging variant (exc-small-0575b61b4, the eighteen at 54'), a build that logs the R677-6 arm's call-argument sites; the census tables do not label these sites apart: on {M}/batch60sp the receipts carry only callee-bound / callee-bound:may:size labels ({cb[NOW].replace('TOTAL ', '')}; across the bridge, mechanical-obligation and slice-construction receipts; no R677-6 or must label; the same reading on {M}/batch58pps39), so no value can be read from the census; a value needs that logging variant rebuilt on {HEAD[:9]} and run (a build: not done here)")); continue
    if vct is None or v60 is None: raise SystemExit(f'no measurement for {k}')
    if exp != now: raise SystemExit(f'record {now} is not 58ppp {exp} for {k}')
    if vct != exp: raise SystemExit(f'CONTROL MISS {k}: 58ppp {exp} vs re-pointed producer on batch58pps39 {vct}')
    CTRL['batch58pps39'] += 1; CMP.append((k, now, exp, '', vct, v60))
    verdict = 'equal' if v60 == now else 'differs'
    cause = f"method: {SRC.get(k, '')}; per-program/detail: {clean(DET[NOW].get(k, '')) or '-'}"
    if k in NOTE: cause += '; ' + NOTE[k]
    cause += f"; control: the same producer on {M}/batch58pps39" + (f" (S39 cache, code {CTRL_REV})" if k.startswith(('waiver.lend', 'design.')) else '') + f" = {vct} = the record"
    if verdict == 'differs': cause += f"; previously at 58''': {now}"
    ROW.append((k, now, v60, verdict, clean(cause)))
with open(S + '/staged.tsv', 'w') as f:
    f.write('key\tvalue_now\tvalue_60sp\tverdict\tcause\n')
    for k, now, v, vd, cause in ROW:
        c = clean(cause)
        if vd == 'differs' and not re.search(r"previously at 58''': \S+$", c): raise SystemExit(f'differs without the tail: {k}')
        if vd == 'carried' and len(c) < 20: raise SystemExit(f'carried without a reason: {k}')
        if any(x in c for x in '\t\n|'): raise SystemExit(f'bad char in {k}')
        f.write(f'{k}\t{now}\t{v}\t{vd}\t{c}\n')
with open(O + '/compare.tsv', 'w') as f:
    f.write('key\trecord\tvalue_58ppp(r141+117)\tb54p(before ctrl)\tbatch58pps39\tbatch60sp\n')
    for r in CMP: f.write('\t'.join(str(x) for x in r) + '\n')
if len(ROW) != 163: raise SystemExit('row count')
print(collections.Counter(r[3] for r in ROW), dict(CTRL))
