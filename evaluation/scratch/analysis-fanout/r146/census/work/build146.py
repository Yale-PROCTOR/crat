#!/usr/bin/env python3
"""build146.py FRAME -- analysis-fanout r146 / census (relay 146, the FINAL re-seed): STAGE the census group's keys at 60s'.

FRAME=60sp -> scratch/analysis-fanout/r146/census/staged.tsv  (key, value_now, value_60sp, verdict, cause)
FRAME=s39  -> work/ctl/staged-ctl.tsv, the CONTROL: the same build over the same re-pointed producers run on main/batch58pps39
              (read by the emitted tree, cen-s39-tree) and the S39 cache era5c-r211-s39pp; its value column is compared with
              r141/census/staged.tsv value_58ppp (ctl/ctl-compare.txt).
Key set: r141/census/staged.tsv's 345 keys + the RQ3 twenty-program times (rq3.<p>.analysis-s and rq3.total.analysis-s, relay 146).
value_now = the record (r146/record-current.md = docs origin/main paper/numbers-of-record.md, md5 8371d530, 117's write).
Inputs: work/out146/<FRAME>/ (run146.sh), work/out146/layers-<FRAME>.tsv (layers141.py, solve side), cache/* (streamed /
bounded-head cache products; era-5c's 60-KINDORDER cache era5c-r215-kindorder for 60sp, the S39 cache for the control).
60s' is read BY THE EMITTED TREE, which at 60s' equals the ledger (custody data=true, ledger-only 0, tree-only 0).
Every check is fail-closed through raise SystemExit (never assert)."""
import collections, csv, json, os, re, sys
csv.field_size_limit(10 ** 9)

F = sys.argv[1] if len(sys.argv) > 1 else ''
if F not in ('s39', '60sp'):
    raise SystemExit('usage: build146.py s39|60sp')
R141 = 'scratch/analysis-fanout/r141'
R146 = 'scratch/analysis-fanout/r146'
H = R146 + '/census'
W = H + '/work'
O = f'{W}/out146/{F}'
CA = H + '/cache'
M = 'scratch/main'
REC = R146 + '/record-current.md'
TREE = H + '/cen-s39-tree'
CEN = {'s39': TREE, '60sp': M + '/batch60sp'}[F]
RAW = {'s39': M + '/batch58pps39', '60sp': M + '/batch60sp'}[F]
FT = {'s39': "58'''", '60sp': "60s'"}[F]          # the frame staged
PREV = {'s39': "58''", '60sp': "58'''"}[F]        # the frame before it (60sp: the frame the record holds now)
PO = {'s39': W + '/out141/58pp', '60sp': W + '/out146/s39'}[F]   # the previous frame's producer outputs (cause text only)
S60 = F == '60sp'


def need(c, m):
    if not c:
        raise SystemExit('build146 FAIL: ' + str(m))


# ---------------------------------------------------------------- the record and the key set
rec = {}
for l in open(REC):
    if l.startswith('| ') and not l.startswith('| key ') and not l.startswith('|---'):
        c = l.rstrip('\n').split(' | ')
        rec[c[0][2:].strip()] = c[1].strip()
r141 = {}
for r in csv.DictReader(open(R141 + '/census/staged.tsv'), delimiter='\t', quoting=csv.QUOTE_NONE):
    r141[r['key']] = (r['value_now'], r['value_58ppp'], r['verdict'])
PROGS20 = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree', 'libzahl', 'lil',
           'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
RQ3P = [f'rq3.{p.replace(".", "")}.analysis-s' for p in PROGS20] + ['rq3.total.analysis-s']
keys = list(r141) + RQ3P
need(len(r141) == 345 and len(keys) == 366 and len(set(keys)) == 366, (len(r141), len(keys)))
need(all(k in rec for k in keys), 'a key is missing from the record')
groups = json.load(open(W + '/groups.json'))


def kv(path, skip=('#', 'key\t')):
    d = {}
    for l in open(path):
        if l.startswith(skip) or not l.strip():
            continue
        c = l.rstrip('\n').split('\t')
        if len(c) >= 2:
            d[c[0]] = c[1]
    return d


V = {}


def put(k, v, src, verdict=None, cause=''):
    need(k in keys, 'not in the key set: ' + k)
    need(k not in V, 'twice: ' + k)
    V[k] = (str(v), verdict, cause, src)


# ---------------------------------------------------------------- inputs
rate = {r['program']: r for r in csv.DictReader(open(O + '/rate/rate.tsv'), delimiter='\t')}
holds = list(csv.DictReader(open(O + '/rate/holds.tsv'), delimiter='\t'))
p1 = open(O + '/p1_count-d6.out').read().splitlines()
p1o = open(O + '/p1_count-old.out').read().splitlines()
lay = kv(O + '/layers-d6.tsv')
layprov = {l.split('\t')[0]: l.rstrip('\n').split('\t')[2] for l in open(O + '/layers-d6.tsv') if l.count('\t') >= 2}
lays = kv(f'{W}/out146/layers-{F}.tsv')
strata = kv(O + '/strata-d6.tsv')
cand = kv(O + '/cand.out')
g5 = kv(O + '/seed-g5.tsv')
sn = kv(O + '/seed_numbers.out')
FORMS = {}
for l in open(O + '/forms-d6.out'):
    if l.startswith(('#', 'form')):
        continue
    c = l.rstrip('\n').split('\t')
    FORMS[c[0]] = dict(zip(['decided', 'withheld', 'licensed', 'delivered', 'reverted', 'notplaced', 'held'], c[1:]))
pt = open(O + '/pair-table.out').read()
sites = eval(re.search(r'pair sites \(unordered, deduplicated\) \d+ (\{.*\})', pt).group(1))
e3 = kv(O + '/ec3.txt')
crown = open(O + '/crown-name-join.txt').read()
crown61 = [l.rstrip('\n').split('\t') for l in open(O + '/crown61.out') if not l.startswith('#')]
ch = open(O + '/clause-holds-d6.txt').read()
leak = open(O + '/leak.out').read()
ownp = open(O + '/ownpref.out').read()
idn = open(O + '/ident-vs-batch58.out').read().splitlines()[0]
idn_pp = open(O + '/ident-vs-prev.out').read().splitlines()[0]

def idpp(path):
    t = open(path).read()
    g = eval(re.search(r'^gained \d+ (\{.*\})$', t, re.M).group(1))
    l = eval(re.search(r'^lost \d+ (\{.*\})$', t, re.M).group(1))
    return ', '.join(f'{p} ' + ' / '.join(x for x in ((f'+{g[p]}' if g.get(p) else ''), (f'-{l[p]}' if l.get(p) else '')) if x) for p in sorted(set(g) | set(l)))


IDPP = idpp(O + '/ident-vs-prev.out')
DELIV, UNIV = int(rate['TOTAL']['delivered']), int(rate['TOTAL']['in_scope'])
WH, DEN = int(rate['TOTAL']['withheld']), int(rate['TOTAL']['denominator'])
HP, HR, HT, HB = (rate['TOTAL'][x] for x in ('withheld_pending', 'withheld_ref_beside', 'withheld_retained', 'withheld_backstop'))
EXP = {'s39': (2678, 4301, 915, 3386, ('248', '263', '403', '1')), '60sp': (2715, 4530, 918, 3612, ('251', '262', '404', '1'))}[F]  # 60sp = main 225 / batch60sp-holds.tsv
need((DELIV, UNIV, WH, DEN, (HP, HR, HT, HB)) == EXP, ('totals', DELIV, UNIV, WH, DEN, (HP, HR, HT, HB)))
m1 = re.match(r'n (\d+) delivered (\d+) safe_raw (\d+) r454 36 safe (\d+) unmod (\d+)$', p1[0])
need(m1 and int(m1.group(2)) == DELIV and int(m1.group(4)) == UNIV, p1[0])
NSUBJ, UNMOD = int(m1.group(1)), int(m1.group(5))
need(F == '60sp' or (NSUBJ, UNMOD) == (7011, 996), p1[0])
need(p1o[0] == p1[0], 'D6 adds something: p1_count old != D6 line 1')
R956 = 100 * DELIV / DEN
OLD = 100 * DELIV / UNIV
LEDGER = int(e3['ec3.ledger'])
CUST = e3['census.custody-mismatch']

TREEC = ("BY THE EMITTED TREE (relay 141): main/batch58pps39 read with the four tulipindicators ledger-only custody rows "
         "(fuzzer::main_0::argv#2, info_0#20, smoke::test_ind_name::info#4, s#49: the ledger counts them delivered, the emitted tree keeps "
         "them raw; they sit in ti_find_indicator's two callers, whose callee the compile check reverts) set to delivery degraded "
         "(r141/census/cen-s39-tree, cp -rL of the census, 4 rows of tulipindicators.raw-boundary-subject-outcomes.tsv changed); ledger "
         f"{LEDGER:,}") if F == 's39' else (f"BY THE EMITTED TREE (relay 141's rule): at 60s' the tree equals the ledger (main/batch60sp custody: "
                                           f"data=true, ledger-only 0, tree-only 0; ec3 ledger {LEDGER:,}, tree {e3['ec3.tree']}), so the census tables are read as written")
IDS = (f"by identity by the tree (n141/ident141.py): {idn_pp.split(': ')[1]} against 58'' (brotli +32 / -12, heman +17 / -2, libtree +1, "
       f"libzahl +1 / -1, tulipindicators -7), {idn.split(': ')[1]} against 58") if F == 's39' else (
       f"by identity by the tree (n141/ident141.py): {idn_pp.split(': ')[1]} against 58''' (cen-s39-tree) ({IDPP}), {idn.split(': ')[1]} against 58; "
       f"main 225: +15 / -8 against 60 (7682bb8a0, 2,708), +99 / -69 against 60s (4eb66851b, 2,685)")
SRC_RATE = (f'{O}/rate/rate.tsv + holds.tsv (r138 d6_rate.py, the asserted totals taken from the frame: p141/d6_rate.py) on {CEN}')
RATEC = (f"R956-1 with D6: {DELIV:,} / ({UNIV:,} - {WH}) = {DELIV:,} / {DEN:,} = {R956:.4f} %; withheld (label = receipt union, each "
         f"counted once): pending {HP}, ref-beside {HR}, retained-access {HT}, backstop {HB}; the cascade into-held-formal "
         f"({rate['TOTAL']['cascade_label']} by label) stays IN the denominator; 0 withheld subjects delivered; old definition (R709-1) "
         f"{DELIV:,} / {UNIV:,} = {OLD:.2f} %; per-program median {rate['MEDIAN']['rate_r956']} % (old {rate['MEDIAN']['rate_old']} %); "
         f"D6 adds 0 (p1_count.py and p1_count_d6.py both {UNIV:,} / {DELIV:,}); {TREEC}; {IDS}")


def mk_cause(*parts):
    return '; '.join(p for p in parts if p)


# ---------------------------------------------------------------- r146: 60s'-only cause builders (read the previous frame's products)
def owning_moves(path):
    t = open(path).read()
    blk = t.split('model_kind moves', 1)[1].split('decision moves', 1)[0].splitlines()[1:]
    return {re.match(r'\s+(\(.*?\))', l).group(1): l.split(')')[-1].split() for l in blk if 'owning' in l}


def owners_created_60sp(fd, mk55, own55):
    """At 60s' the model-kind diff against b55 carries the Ref > Owning > Raw order's owners; the copy-lend arm's own share is read
    through batch 60 (the 59m frame: mutable copy-lend on, no order). The staged value is the copy-lend arm's: 0 when b55 -> 60 moves
    no subject to or from Owning and every owning move b55 -> 60s' is a move 60 -> 60s' (the order's)."""
    m55 = owning_moves(O + '/famdiff-vs-b55.out')
    m60 = owning_moves(O + '/famdiff-b55-vs-batch60.out')
    mo = owning_moves(O + '/famdiff-batch60-vs-60sp.out')
    need(len(m60) == 0 and set(m55) == set(mo), ('owners-created attribution', len(m60), len(m55), len(mo)))
    kinds = collections.Counter(tuple(v) for v in m55.values())
    src = (f'{O}/famdiff-vs-b55.out (n141/famdiff141.py main/b55 -> {CEN}): model_kind moves {mk55.group(1)} over {NSUBJ:,} subjects, {own55} to or '
           f'from owning ({", ".join(f"{a} -> {b} {n}" for (a, b), n in sorted(kinds.items()))}); famdiff-b55-vs-batch60.out: b55 -> batch 60 (the 59m '
           f'frame, mutable copy-lend on, no order) moves 0 to or from owning; famdiff-batch60-vs-60sp.out: the {len(mo)} owning moves 60 -> 60s\' are '
           f'the same {len(m55)} subjects')
    cause = (f"METHOD NOTE (60s'): the literal reading of the producer (model-kind moves to or from owning, b55 -> the frame) is {own55}, every one "
             "the Ref > Owning > Raw order's (main 225 s0: 222 Raw -> Owning + 7 Ref -> Owning, the same set by identity); the copy-lend arm "
             "itself (read through batch 60, the same copy-lend with no order) creates 0 owners, which is what this key states; see notes Q")
    return 0, src, cause


OPC60 = ROUNDSC = S9C60 = S16C60 = ''
if S60:
    _op = open(O + '/ownpref.out').read()
    _ms = re.search(r'against the S39 set \((\d+)\): same slots (\d+), only S39 (\d+), only 60sp (\d+)', _op)
    _mk = re.search(r'of the union, kind moved S39 -> 60sp: (\{.*\})', _op)
    _mo = re.search(r'Owning slots S39 (\d+), 60sp (\d+), S39 subset of 60sp: (\w+)', _op)
    need(_ms and _mk and _mo, 'ownpref 60sp lines')
    OPC60 = (f"60s' has no terms-on solve either: the ablation pair is read as L01^14 (terms on) against era-5c's 60-KINDORDER cache (terms off, "
             f"the frame, the Ref > Owning > Raw order); against 58''''s set ({_ms.group(1)}): same slots {_ms.group(2)}, only 58''' {_ms.group(3)}, "
             f"only 60s' {_ms.group(4)} (the 581 are Owning again at 60s' under the order); kind moves S39 -> 60s' within the union {_mk.group(1)}; the frame's Owning slots {_mo.group(1)} -> {_mo.group(2)} "
             f"(58''''s a subset: {_mo.group(3)})")
    _r0 = {r['program']: r for r in csv.DictReader(open(CA + '/reader/s39/records.tsv'), delimiter='\t')}
    _r1 = {r['program']: r for r in csv.DictReader(open(CA + '/reader/60sp/records.tsv'), delimiter='\t')}
    _rd = lambda r: max(int(x) for x in r['epochs_per_construction'].split(','))
    _mv = [f'{p} {_rd(_r0[p])} -> {_rd(_r1[p])}' for p in sorted(_r1) if _rd(_r0[p]) != _rd(_r1[p])]
    _cp = [f"{p} {_r0[p]['planner_cap_10K+1']} -> {_r1[p]['planner_cap_10K+1']}" for p in sorted(_r1) if _r0[p]['planner_cap_10K+1'] != _r1[p]['planner_cap_10K+1']]
    ROUNDSC = f"against 58''' (the S39 cache): rounds {', '.join(_mv) or 'none moves'}; planner caps {', '.join(_cp) or 'none move'}"
    _c0, _c1 = open(CA + '/s9/s39/candidates.tsv').read(), open(CA + '/s9/60sp/candidates.tsv').read()
    _p0, _p1 = open(CA + '/s9/replay-s39.out').read(), open(CA + '/s9/replay-60sp.out').read()
    S9C60 = ("CONTROL: the same script on the S39 cache reproduces r141's s9/s39/candidates.tsv and replay output; at 60s' candidates.tsv is "
             + ("identical to 58'''s" if _c0 == _c1 else "NOT identical to 58'''s") + ', the replay output ' + ('identical' if _p0 == _p1 else 'differs'))

    def _adm(d):
        a = collections.defaultdict(lambda: collections.defaultdict(set))
        for l in open(d + '/admitted-rows.tsv'):
            p, off, k, kind = l.rstrip('\n').split('\t')
            a[p][off].add((k, kind))
        return {p: v[sorted(v, key=int)[-1]] for p, v in a.items()}
    _a0, _a1 = _adm(CA + '/s16/work-s39'), _adm(CA + '/s16/work-60sp')
    _dk = [f'{p}: {sorted(_a0.get(p, set()) ^ _a1.get(p, set()))}' for p in sorted(set(_a0) | set(_a1)) if _a0.get(p) != _a1.get(p)]
    S16C60 = ("CONTROL: the same driver on the S39 cache reproduces r141's admitted-rows.tsv (sorted); against 58''': "
              + ('the admitted rows and their kinds are identical program by program' if not _dk else 'moved ' + '; '.join(_dk)))


# ---------------------------------------------------------------- rate (R956-1)
put('rq1.frame-realization-rate', f'{R956:.1f}%', SRC_RATE, cause=RATEC)
put('rq1.frame-realization-rate.amended', f'{R956:.1f}%', SRC_RATE, cause=RATEC)
put('rq1.frame14u.realization-rate', f'{R956:.2f}%', SRC_RATE, cause=RATEC)
put('rq1.frame-realization-rate.old-definition', f'{OLD:.1f}%', SRC_RATE + ' (3) old definition',
    cause=f'R709-1: {DELIV:,} / {UNIV:,} = {OLD:.4f} % (decided safe {m1.group(3)} less R454 36); {TREEC}')
for k in ('rq1.frame-safe-decisions', 'rq1.frame-safe-decisions.amended', 'rq1.frame14u.safe-decisions'):
    put(k, DEN, SRC_RATE, cause=RATEC)
for k in ('rq1.frame-delivered', 'rq1.frame14u.delivered'):
    put(k, DELIV, SRC_RATE + f'; = {O}/p1_count-d6.out line 1; ec3 tree {e3["ec3.tree"]}, ledger {LEDGER}', cause=mk_cause(TREEC, IDS))
ret = [r for r in holds if r['withheld_r956'] == '1' and r['attributed_hold'] == 'retained']
fin = collections.Counter(r['finer'] for r in ret)
sc = fin['retained:evident:self-reference'] + fin['retained:evident:cycle']
ds = sum(v for k, v in fin.items() if 'derived-store' in k)
RW = f'{SRC_RATE}: label held:retained-alias (R864-3), = label or settled receipt; finer {dict(sorted(fin.items()))}'
need(len(ret) == int(HT), 'retained')
RETC = ''
if True:  # r146: against the previous frame (control: 58''; 60s': 58''')
    r58 = {(r['program'], r['subject_key']) for r in csv.DictReader(open(f'{PO}/rate/holds.tsv'), delimiter='\t') if r['withheld_r956'] == '1' and r['attributed_hold'] == 'retained'}
    rnew = sorted((r['program'], r['subject_key'], r['finer']) for r in ret if (r['program'], r['subject_key']) not in r58)
    rgone = sorted(k for k in r58 if k not in {(r['program'], r['subject_key']) for r in ret})
    RETC = f"against {PREV}: newly held {len(rnew)} " + ', '.join(f'{a} {b} ({c})' for a, b, c in rnew) + f'; no longer held {len(rgone)} {rgone}'
put('rq1.frame-withdrawn.retained-access', len(ret), RW,
    cause=mk_cause(f'self-container {sc} + derived-store {ds} + {len(ret) - sc - ds} stop-gap rows (observed / fixture, no settled receipt)', RETC))
put('rq1.frame-withdrawn.retained-access.delivered', sum(1 for r in ret if r['delivery'] == 'realized-as-predicted'), RW + '; a held subject is never delivered')
put('rq1.frame-withdrawn.retained-access.self-container', sc, RW + f': evident:self-reference {fin["retained:evident:self-reference"]} + evident:cycle {fin["retained:evident:cycle"]}', cause=RETC)
put('rq1.frame-withdrawn.retained-access.self-container.delivered', 0, RW)
put('rq1.frame-withdrawn.retained-access.derived-store', ds, RW + ': evident:derived-store')
put('rq1.frame-withdrawn.retained-access.derived-store.delivered', 0, RW)
PK = {'jsonh': 'json.h'}
for k in groups['rate']:
    m = re.match(r'rq1\.frame-withdrawn\.retained-access\.([a-z0-9]+)(\.delivered)?$', k)
    if m and m.group(1) not in ('delivered', 'self-container', 'derived-store'):
        p = PK.get(m.group(1), m.group(1))
        vv = 0 if m.group(2) else int(rate[p]['withheld_retained'])
        put(k, vv, SRC_RATE + f' row {p} (withheld_retained)', cause=(RETC if str(vv) != rec[k] else ''))

# ---------------------------------------------------------------- count / Box / modeled fraction
P1 = f'{O}/p1_count-d6.out (r138 p1_count_d6.py on {CEN}; the old p1_count.py gives the same line 1: D6 adds 0)'
mb = re.match(r'box (\d+) (\{.*\})$', p1[2]); bp = p1[3]
need(mb, p1[2])
BOXBF = ', '.join(f'{a} {b}' for a, b in sorted(eval(mb.group(2)).items(), key=lambda x: -x[1]))
BOXC = ''
if True:  # r146: against the previous frame
    bpp = eval(open(f'{PO}/p1_count-d6.out').read().splitlines()[3].split('box by program ', 1)[1])
    bss = eval(bp.split('box by program ', 1)[1])
    fpp = eval(open(f'{PO}/p1_count-d6.out').read().splitlines()[2].split(' ', 2)[2])
    fss = eval(mb.group(2))
    BOXC = (f"against {PREV}: by program " + ', '.join(f'{q} {bpp.get(q, 0)} -> {bss.get(q, 0)}' for q in sorted(set(bpp) | set(bss)) if bpp.get(q, 0) != bss.get(q, 0))
            + '; by form ' + ', '.join(f'{q} {fpp.get(q, 0)} -> {fss.get(q, 0)}' for q in sorted(set(fpp) | set(fss)) if fpp.get(q, 0) != fss.get(q, 0))
            + (" (brotli ClusterBlocksDistance delivered whole at 58''': its class#1498 E0599 no longer occurs, main 219 s3)" if F == 's39' else
               f"; Box {BOXBF} by family (main 225: Box 212 = opt-box-slice 99, box 92, box-slice 21; +8 against 60 = heman's box-param-reseat formals)"))
put('rq1.frame14u.delivered-box', int(mb.group(1)), P1 + f' line 3: {mb.group(2)}; {bp}',
    cause=BOXC)
mf = re.match(r'modeled-fraction ([\d.]+%) (\d+)/(\d+)$', p1[4])
need(mf, p1[4])
put('rq1.modeled-fraction', mf.group(1), P1 + f' line 5 ({mf.group(2)}/{mf.group(3)}; unmodeled {UNMOD}, R454 36; subjects {NSUBJ:,})', cause=TREEC)
for k in keys:
    if k.startswith('rq1.frame14.'):
        put(k, rec[k], f"carried: superseded row describing main/frame14 (L01^14); {FT} does not touch it", verdict='carried')

# ---------------------------------------------------------------- pair-hold price (D2)
lines = {m.group(1).strip(): m for m in re.finditer(r'^(pending|peers|pending \+ peers)\s+N=\s*(\d+) d=\s*(\d+)\s+old ([\d,]+)/([\d,]+) = ([\d.]+) %\s+out ([\d,]+)/([\d,]+) = ([\d.]+) %', ch, re.M)}
need({'pending', 'peers'} <= set(lines), 'clause-holds lines')
pv = open(O + '/raw-view-peers.txt').read().splitlines()
PH = (f'{O}/clause-holds-d6.txt (r138 clause_holds_d6.py with {DELIV:,} / {UNIV:,} over hold-price.tsv (pending_hold_price.py) and '
      f'raw-view-peers.tsv (raw_view_peers.py: {pv[1]}))')
PHC = (f"DEFINITION (D2): at the hold census the pending pair hold is APPLIED, so the not-yet-applied hold's price is 0 by construction; "
       f"the peers rule's delivered peers: {lines['peers'].group(2)} ({pv[0].split(': ', 1)[1]}); R956-1 information values: pending "
       f"{DELIV:,} / ({UNIV:,} - {HP}) = {100 * DELIV / (UNIV - int(HP)):.2f} %, peers {DELIV:,} / ({UNIV:,} - {HR}) = {100 * DELIV / (UNIV - int(HR)):.2f} %")
put('rq1.frame14u.pair-hold.pending.withdrawn', lines['pending'].group(2), PH + ' line pending', cause=PHC)
put('rq1.frame14u.pair-hold.pending.rate', lines['pending'].group(6) + '%', PH + ' line pending (old)', cause=PHC)
put('rq1.frame14u.pair-hold.pending.rate.out-of-denominator', lines['pending'].group(9) + '%', PH + ' line pending (out)', cause=PHC)
put('rq1.frame14u.pair-hold.peers.withdrawn', lines['peers'].group(2), PH + ' line peers', cause=PHC)
put('rq1.frame14u.pair-hold.peers.rate', lines['peers'].group(6) + '%', PH + ' line peers (old)', cause=PHC)
put('rq1.frame14u.pair-hold.peers.rate.out-of-denominator', lines['peers'].group(9) + '%', PH + ' line peers (out)', cause=PHC)

# ---------------------------------------------------------------- CROWN
CRC60 = ''
if S60:
    same61 = open(O + '/crown61.out').read() == open(PO + '/crown61.out').read()
    mvd = [p for p in PROGS20 if os.popen(f'diff -rq {M}/batch58pps39/emitted-trees/{p} {RAW}/emitted-trees/{p}').read() != '']
    CRC60 = (("crown61.out byte-identical to 58'''s: no unit moves" if same61 else "crown61.out DIFFERS from 58'''s") +
             f"; the trees that differ 58''' -> 60s': {', '.join(mvd)}; = main 225 (CROWN 55 / 61 by the name join, unchanged)")
mc = re.search(r'CROWN by the name join of record: (\d+) / 61 \(crown61 (\d+) \+ (\d+) of the three', crown)
need(mc, crown)
not_ok = [r for r in crown61 if r[-1] == 'False']
field_norow = [r for r in not_ok if r[2].startswith('field') and r[3] == 'no row']
subj_bad = [r for r in not_ok if r[2] == 'subject' and r[3] != 'no row']
need(len(crown61) == 61, 'crown61 rows')
sj = {}
for r in csv.DictReader(open(CEN + '/quadtree.raw-boundary-subjects.tsv'), delimiter='\t'):
    sj[r['subject_key']] = r
dec_only = [r for r in subj_bad if sj.get(r[1] + '#1', {}).get('model_kind') == 'owning']
op = [r for r in subj_bad if r not in dec_only]
heads = {}
for r in csv.DictReader(open(CA + '/heads/models.tsv'), delimiter='\t'):
    if r['program'] == 'quadtree' and r['slot'] in ('src::src::quadtree::quadtree::field0@d0', 'src::src::bounds::quadtree_bounds::field0@d0', 'src::src::bounds::quadtree_bounds::field1@d0'):
        heads[r['slot']] = r[{'s39': 'kinds39', '60sp': 'kind60sp'}[F]]
root = [r for r in field_norow if r[1] == 'src::src::quadtree::quadtree::field0@d0']
need(len(root) == 1 and heads.get('src::src::quadtree::quadtree::field0@d0') == 'raw', 'quadtree.root')
justified = 1
unjoin = 0
delivered = int(mc.group(1))
openn = len(field_norow) - justified + len(op)
CR = (f'{O}/crown61.out (crown61.py on {CEN}: {mc.group(2)} = crown61 subjects + fields) + {O}/crown-name-join.txt (main\'s '
      f'crown_name_join.py, the record\'s join: the three pattern-matched box units bst deleteNode::temp, temp_0, buffer '
      f'test_buffer_slice__range_error::a) = {crown.strip()[:60]}...')
CRC = ("crown61.out byte-identical to 58''s (n141 diff): no unit moves; the five trees that differ 58'' -> 58''' are brotli, heman, libtree, "
       "libzahl, tulipindicators, none holding a CROWN unit" if F == 's39' else CRC60)
put('rq2.crown.units', len(crown61), 'constant: CROWN\'s 61 owning units (crown61 table)')
put('rq2.crown.units.delivered', delivered, CR, cause=CRC)
put('rq2.crown.units.unjoinable', unjoin, CR)
put('rq2.crown.units.justified', justified, f'quadtree quadtree.root: no field-transaction row at {FT} (no src::src::quadtree::quadtree row); model slot '
    f'src::src::quadtree::quadtree::field0@d0 = {heads["src::src::quadtree::quadtree::field0@d0"]} in the frame\'s cache entry ({CA}/heads/models.tsv, bounded head read)')
put('rq2.crown.units.ceiling', 61 - justified - unjoin, '61 - justified 1 - unjoinable 0')
put('rq2.crown.units.gap', 61 - justified - unjoin - delivered, f'ceiling {61 - justified - unjoin} - delivered {delivered} = decided-only {len(dec_only)} + open {openn}', cause=CRC)
put('rq2.crown.units.decided-only', len(dec_only), f'{CR}: ' + ', '.join(f'{r[1]} (census {r[3]}; model_kind owning, family {sj[r[1] + "#1"]["family"]}, reason {sj[r[1] + "#1"]["reason"]})' for r in dec_only), cause=CRC)
put('rq2.crown.units.open', openn, f'{CR}: quadtree_bounds.nw / .se (no field row; model slots ' + ', '.join(f'{k.split("::")[-1]}={v}' for k, v in sorted(heads.items()) if 'bounds' in k)
    + ') + ' + ', '.join(f'{r[1]} ({sj[r[1] + "#1"]["reason"]})' for r in op) + f'; check {delivered} + {len(dec_only)} + {justified} + {unjoin} + {openn} = 61', cause=CRC)
need(delivered + len(dec_only) + justified + unjoin + openn == 61, 'crown check')
same_avl_bst = all(os.popen(f'diff -rq {M}/batch58pp/emitted-trees/{p} {RAW}/emitted-trees/{p}').read() == '' for p in ('avl', 'bst'))  # 60s': checked, still identical
need(same_avl_bst, 'avl/bst trees moved')
put('rq2.crown.units.borrow-on-raw', 4, f"avl and bst emitted trees byte-identical between batch58pp and {os.path.basename(RAW)} (diff -rq), so the four X rows (avl height/getBalance/preOrder, bst inorder) hold")

# ---------------------------------------------------------------- copy-lend / owners by preference
pb = open(O + '/pairs-b55.txt').read()
mm = re.search(r'listed locals moving as listed: (\d+) / (\d+)', pb)
moff = re.search(r'model-kind moves OFF the list: (\d+) (\{.*\})', pb)
need(mm and moff, 'pairs_read')
fd = open(O + '/famdiff-vs-b55.out').read() if os.path.exists(O + '/famdiff-vs-b55.out') else ''
mk55 = re.search(r'^model_kind moves b55->\S+: (\d+)', fd, re.M)
own55 = sum(1 for l in fd.split('model_kind moves', 1)[1].split('decision moves', 1)[0].splitlines()[1:] if 'owning' in l) if fd else -1
need(mk55 and (own55 == 0 or S60), 'famdiff b55')
CL = f'{O}/pairs-b55.txt (pairs_read.py main/b55 -> {CEN} on era-5c 144\'s 24 pairs)'
MV_PP = re.search(r'listed locals moving as listed: (\d+)', open(O + '/pairs-prev.txt').read()).group(1)
MK_PP = re.search(r'^model_kind moves \S+: (\d+)', open(O + '/famdiff-vs-prev.out').read(), re.M).group(1)
put('analysis.copy-lend.locals.listed', int(mm.group(2)), CL + f': {mm.group(2)} listed; constant')
CLM = ''
if S60:
    def _pl(path):
        d = {}
        for l in open(path):
            m_ = re.match(r'^(OK|\?\?) (\S+)\s+(\S+)\s+#\s*(\d+) ', l)
            if m_:
                d[(m_.group(2), m_.group(3), m_.group(4))] = m_.group(1)
        return d
    _q0, _q1 = _pl(PO + '/pairs-b55.txt'), _pl(O + '/pairs-b55.txt')
    _on = sorted(f'{p} {f.split("::")[-1]} _{n}' for (p, f, n), v in _q1.items() if v == 'OK' and _q0.get((p, f, n)) != 'OK')
    _off = sorted(f'{p} {f.split("::")[-1]} _{n}' for (p, f, n), v in _q1.items() if v != 'OK' and _q0.get((p, f, n)) == 'OK')
    CLM = (f"against 58''' (pairs-b55.txt of both frames): {len(_on)} listed locals newly move as listed ({', '.join(_on)}), {len(_off)} no longer do "
           f"({', '.join(_off)}): the 24 pairs are same-function swaps whose tie the order re-breaks (main 225 s0: 16 of the 46 slots that change identity "
           f"are same-function pair re-breaks)")
put('analysis.copy-lend.locals.moved-at-census', int(mm.group(1)), CL + f' "listed locals moving as listed: {mm.group(1)} / {mm.group(2)}"; off the list {moff.group(1)} {moff.group(2)}' +
    (f"; against 58'' (pairs-batch58pp.txt): {MV_PP} / 48 move (the S39 relaxation re-breaks some listed swaps)" if F == 's39' else
     f"; against 58''' (pairs-prev.txt, cen-s39-tree -> batch60sp): {MV_PP} / 48 move"), cause=(CLM if S60 and str(mm.group(1)) != rec['analysis.copy-lend.locals.moved-at-census'] else ''))
if not S60:
    put('analysis.copy-lend.owners-created', 0, f'{O}/famdiff-vs-b55.out (n141/famdiff141.py main/b55 -> {CEN}): model_kind moves {mk55.group(1)} over 7,011 subjects, '
        f'{own55} to or from owning' + (f"; against 58'' {MK_PP} moves, 0 to or from owning" if F == 's39' else ''))
else:
    OWNC_V, OWNC_SRC, OWNC_C = owners_created_60sp(fd, mk55, own55)
    put('analysis.copy-lend.owners-created', OWNC_V, OWNC_SRC, cause=OWNC_C)
mo = re.search(r'owners by preference \(owning at L01\^14, not at the frame\): (\d+); gained \(owning only at the frame\): (\d+)', ownp)
mcls = re.search(r'by \(frame kind, slot class\): (\{.*\})', ownp)
mbeh = re.search(r'behind a delivered declaration at the frame\'s census \(.*\): (\d+)', ownp)
need(mo and mcls and mbeh, 'ownpref')
cls = eval(mcls.group(1))
fieldterm = sum(v for (k, c), v in cls.items() if c == 'field')
localterm = sum(v for (k, c), v in cls.items() if c != 'field')
OPS = (f'{O}/ownpref.out (n141/ownpref141.py: per-slot kind diff of the terms-on cache L01^14 (era5c-l01p14-restored-solve) against '
       f'the frame\'s cache ({"the S39 row era5c-r211-s39pp" if F == "s39" else "era-5c 60-KINDORDER era5c-r215-kindorder"}), heads read by r100\'s bounded model_head.read_head '
       f'({CA}/heads/models.tsv: dump_heads146.py over the four caches); classes from keymap141/{F}): by (frame kind, class) {dict(sorted(cls.items()))}')
OPC = ("the S39 row has no terms-on solve: the ablation pair is read as L01^14 (terms on, old analyses tree) against the S39 cache (terms off, "
       "the frame); the set is the L01^14u set slot for slot (603 / 603), the frame's Owning slots equal L01^14u's (400 = 400), and one "
       "slot of the set moves raw -> ref under the relaxation (brotli BrotliZopfliComputeShortestPath::_100@d0)") if F == 's39' else OPC60
put('analysis.owners-by-preference', int(mo.group(1)), OPS, cause=OPC)
put('analysis.owners-by-preference.by-field-term', fieldterm, OPS + ': fields', cause=OPC)
put('analysis.owners-by-preference.by-local-term', localterm, OPS + ': locals (compiler temporaries)', cause=OPC)
put('analysis.owners-by-preference.delivered-overlap', int(mbeh.group(1)), OPS + f': behind a delivered declaration in keymap141/{F}/reverse-index.tsv (built at {os.path.basename(CEN)}, delivered by the tree)', cause=OPC)

# ---------------------------------------------------------------- analysis.* from the cache (067 reader, S9, S16)
RD = {'s39': CA + '/reader/s39/records.tsv', '60sp': CA + '/reader/60sp/records.tsv'}[F]
recs = list(csv.DictReader(open(RD), delimiter='\t'))
need(len(recs) == 20, 'reader rows')
byp = {r['program']: r for r in recs}
ORDER = [x.split(' ')[0] for x in rec['analysis.guarded.cap.per-program'].split(', ')]
need(sorted(ORDER) == sorted(byp), 'cap order')
caps = {p: int(byp[p]['planner_cap_10K+1']) for p in byp}
rounds = {p: max(int(x) for x in byp[p]['epochs_per_construction'].split(',')) for p in byp}
pins = [p for p in byp if int(byp[p]['pin_rounds']) > 0]
unk = [p for p in byp if byp[p]['unknown_reasons'] != '-' or byp[p]['ledger_probe_unknown_or_unprobed'] not in ('0', '-') or byp[p]['worker_log_flags'] != '-'
       or 'unknown' in byp[p]['demand_query_outcomes'] or 'unknown' in byp[p]['demand_final_selection_outcomes']]
fb = sum(int(byp[p]['guarded_fallbacks']) for p in byp)
need(all(byp[p]['repair'] == 'guarded' for p in byp), 'repair')
RS = (f'{RD} (067\'s reader r110/p1-rq1/reader/read_records.py re-pointed: SOLVE from READER_SOLVE, completion and key from each '
      f'workers/<p>.json receipt (the S39 row\'s progress.jsonl names only its ten host-a solves), worker logs from workers/ or '
      f'staging-A2/workers/ (A2\'s ten, host-b); each entry streamed with ijson yajl2_c, one at a time, stopping at the origin key)')
RSC = (f"S39 cache (era5c-r211-s39pp: ten entries solved on host-a 07:06Z-08:46Z 10-11, A2's ten solved on host-b and copied in; "
       f"analysis 746aad53, configuration beff8254); CONTROL: the same reader on era5c-l01p14u-solve reproduces r110's records.tsv on every "
       f"column but parse_s (cache/reader/ctl)") if F == 's39' else (
       "era-5c's 60-KINDORDER cache (era5c-r215-kindorder: the twenty solved on host-b 03:01Z-11:24Z 10-13, era-5c 172b; analysis 1d8dcd40, "
       "configuration d9a474da, launch 2e94d9a5; = main 225's keycheck); CONTROL: the same reader on the S39 cache reproduces r141's records.tsv "
       "on every column but parse_s")
put('analysis.guarded.cap', min(caps.values()), RS + f': min planner cap 10K+1 over the twenty ({min(caps, key=caps.get)}, K = {byp[min(caps, key=caps.get)]["K"]})', cause=RSC)
put('analysis.guarded.cap.per-program', ', '.join(f'{p} {caps[p]}' for p in ORDER), RS + ': planner_cap_10K+1 per program (the record\'s order)', cause=RSC)
put('analysis.guarded.fallbacks', fb, RS + ': guarded_fallbacks summed; every receipt repair=guarded, guarded_verifications=2', cause=RSC)
put('analysis.pins.programs', len(pins), RS + ': programs with pin_rounds > 0: ' + ', '.join(f'{p} {byp[p]["pin_slots"]}' for p in pins) + ' (pinned slots)', cause=RSC)
put('analysis.rounds.max', max(rounds.values()), RS + f': max epochs per construction over the 40 verifications ({max(rounds, key=rounds.get)})', cause=RSC)
put('analysis.rounds.per-program', ', '.join(f'{p} {rounds[p]}' for p in ORDER), RS + ': max epochs per construction per program (the record\'s order)',
    cause=mk_cause(RSC, 'against L01^14u: libtree 10 -> 11, binn 7 -> 8, tulipindicators 8 -> 9' if F == 's39' else ROUNDSC))
put('analysis.unknown-solves', len(unk), RS + ': no unknown reason, no unknown / unprobed ledger cell, no worker-log flag, demand outcomes sat / unsat only', cause=RSC)
S9 = f'{CA}/s9/{F}/candidates.tsv + readers-{F}.out (082 S9 readers.py re-pointed: S and keymap141/{F}; bounded 64 MiB chunks)'
s9t = open(f'{CA}/s9/readers-{F}.out').read()
mt = re.search(r"TOTAL (\{.*\})", s9t)
need(mt, 's9')
t9 = eval(mt.group(1))
S9C = ("CONTROL: the same script on the L01^14u solve reproduces r110's s9u/candidates.tsv byte for byte; at S39 candidates.tsv and "
       "replay.py's reader_replay are identical to the control's") if F == 's39' else S9C60
put('analysis.lend.field-read.candidates', t9['candidates'], S9 + f': TOTAL {t9}', cause=S9C)
put('analysis.lend.field-read.taken', t9['guard_true'], S9 + ': guard r = ref(view) and own(field) true in the frame\'s model (bst / avl minValueNode)', cause=S9C)
S16 = {'s39': CA + '/s16/work-s39', '60sp': CA + '/s16/work-60sp'}[F]
adm = collections.defaultdict(lambda: collections.defaultdict(set))
for l in open(S16 + '/admitted-rows.tsv'):
    p, off, k, kind = l.rstrip('\n').split('\t')
    adm[p][off].add((k, kind))
last = {p: d[sorted(d, key=int)[-1]] for p, d in adm.items()}
nadm = sum(len(v) for v in last.values())
nkept = sum(1 for v in last.values() for _, kind in v if kind == 'owning')
S16S = (f'{S16}/admitted-rows.tsv + run_frame.log (082 S16 return-port port re-pointed: licensing sections located afresh per entry '
        f'(offsets141.py), run_frame.py / markers.py + run_big.py for the three large entries; kinds from the frame\'s model head)')
S16C = ("CONTROL: the same driver on the L01^14u solve reproduces r110 s16u/work-u/admitted-rows.tsv (sorted, byte-identical); at S39 the "
        "admitted rows, their kinds and the holds equal the control's program by program") if F == 's39' else S16C60
put('analysis.return-port.admitted', nadm, S16S + ': slots admitted (last snapshot)', cause=S16C)
put('analysis.return-port.kept', nkept, S16S + ': admitted and Owning in the frame\'s model', cause=S16C)

# ---------------------------------------------------------------- leak parity (relay 139's ruling)
ml = re.search(r'TOTAL closes by exit path \(the ruling\): (\d+); receipt sum implicit_close_scope_exit=(\d+)', leak)
mrec = re.search(r"receipt (\{.*\})", leak)
mobs = re.search(r"box-drop observer status (\{.*\})", leak)
need(ml and mrec and mobs, 'leak')
recd = eval(mrec.group(1)); obs = eval(mobs.group(1))
LP = (f'{O}/leak.out (n141/leak141.py on {CEN}: per program field-transaction closes (applied, active) + max(Box-drop observer '
      f'waiver-drop rows, return-certificate waiver-drop receipts); every counted function emitted); census-receipt '
      f'implicit_close_scope_exit={recd["implicit_close_scope_exit"]} overwrite={recd["implicit_close_overwrite"]} unwind={recd["implicit_close_unwind"]} '
      f'sources {recd["implicit_close_sources"]} by program {recd["implicit_close_by_program"]} box_share_unpublished={recd["implicit_close_box_share_unpublished"]}')
per_leak = re.findall(r'^\s+(\S+)\s+observer waiver rows\s+(\d+)\s+return-certificate waiver receipts\s+(\d+)\s+field-transaction closes\s+(\d+)\s+-> closes by exit path (\d+)', leak, re.M)
LPC = ("THE EMITTED PROGRAM'S IMPLICIT CLOSES, each counted once by exit path (relay 139's ruling; r140 vcensus's correction): "
       + ', '.join(f'{p} {c}' for p, b, r, t, c in per_leak)
       + f" = {ml.group(1)}; the census receipt's {ml.group(2)} counts quadtree's 6 Box-drop observer rows and its 9 return-certificate "
       f"receipts separately, though they name the same closes; A LOWER BOUND: brotli's Box-drop observer {obs.get('brotli', '?')}")
if F == 's39':
    LPC += ("; FLAG: relay 141's text says '18 implicit closes (buffer 1, quadtree 15, lodepng 2)': that is the receipt sum, not the ruling's "
            "number; at 58''' the quadtree / buffer / lodepng Box-drop tables (modulo the verify tmp path), return-certificate receipts and field "
            "transactions are identical to 58''s; tulipindicators' new field transaction smoke::test_ind_name.answers (waiver-drop-scope-exit=1) is "
            "revert_status withdrawn, so it is not a close of the emitted program; brotli's observer error changed reason (58'': emitted crate failed "
            "before the observer; 58''': unreceipted Box MIR drop population, BrotliCreateHqZopfliBackwardReferences::matches#60 expected_normal=1 got_normal=2)")
if S60:
    LPC += ("; FLAG: main 225's 'implicit closes 23 (heman scope-exit 4, beside the Box formals)' is the receipt sum, not the ruling's number "
            "(quadtree's 6 observer rows and 9 return-certificate receipts name the same 9 closes; heman's 2 observer rows and 2 return-certificate "
            "receipts are the same two closes, kmAABB2Initialize::pBox and kmAABB3Initialize::pBox, one per function exit); against 58''' (12): "
            "+2 heman (the box-param-reseat formals' scope-exit closes) and +1 tulipindicators (field transaction smoke::test_ind_name.answers "
            "waiver-drop-scope-exit=1, revert_status withdrawn at 58''' and active at 60s', its function emitted); brotli's observer error reason "
            "unchanged from 58''' (unreceipted Box MIR drop population, BrotliCreateHqZopfliBackwardReferences::matches#60)")
put('waiver.leak-parity', ml.group(1), LP, cause=LPC)
put('waiver.leak-parity-scope', ml.group(1), LP, cause=LPC)
put('waiver.leak-parity-overwrite', recd['implicit_close_overwrite'], LP)
put('waiver.leak-parity-unwind', recd['implicit_close_unwind'], LP)

# ---------------------------------------------------------------- six shipped suites
SIXF = {'s39': (M + '/batch58pps39-six-suites.tsv', M + '/batch58pp-six-suites.tsv'), '60sp': (M + '/batch60sp-six-suites.tsv', M + '/batch58pps39-six-suites.tsv')}[F]
same6 = open(SIXF[0]).read() == open(SIXF[1]).read() and open(SIXF[0][:-4] + '.txt').read() == open(SIXF[1][:-4] + '.txt').read()
need(same6, 'six suites moved')
SS = (f"{SIXF[0]} and .txt byte-identical to {os.path.basename(SIXF[1])} / .txt (6/6 emitted pass; urlparser C test=-6 abort, url.h's own "
      f"heap overflow under _FORTIFY_SOURCE=3); run on the frame's emitted trees" + ("; among the six only libtree's tree differs from 58'' (utoa::str slice)" if F == 's39' else
     "; the six emitted trees are byte-identical to 58''''s (diff -rq main/batch58pps39 vs main/batch60sp)"))
for k in keys:
    if k.startswith('rq1.tests.'):
        put(k, rec[k], SS)

# ---------------------------------------------------------------- layers
LY = f'{O}/layers-d6.tsv (layers141.py = r138 layers_d6.py + the tree reading + the typed-failure receipt fallback, census side, on {RAW})'
LYS = f'{W}/out146/layers-{F}.tsv (layers141.py with the frame\'s solve: workers/<p>.json receipts, heads by model_head.read_head, demand-evidence by a chunked prefix scan)'
ALIAS = {'delivery.programs-degraded': 'layer2.programs-degraded', 'delivery.not-placed': 'layer2.not-placed', 'hold.io-domain': 'layer2.held-stream'}
SOLVE_LAYER = ['layer1.programs-accepted', 'layer1.slots', 'layer1.ref', 'layer1.raw', 'layer1.owning', 'layer1.site-assumptions', 'layer1.site-retracted', 'layer1.site-active']
LSCTL, HMV = '', ''
if S60:
    _lc = kv(f'{W}/out146/layers-s39.tsv')
    LSCTL = ' / '.join(f'{int(_lc[k]):,}' for k in SOLVE_LAYER)
    _hm = collections.Counter((r['kinds39'], r['kind60sp']) for r in csv.DictReader(open(CA + '/heads/models.tsv'), delimiter='\t') if r['kinds39'] != r['kind60sp'])
    HMV = ', '.join(f'{a} -> {b} {n}' for (a, b), n in sorted(_hm.items(), key=lambda x: -x[1]))
LSC = ("re-derived from the S39 cache (115 carried them as the L01^14u solve's cache; the cache changed); CONTROL: the same run on "
       "era5c-l01p14u-solve gives the record's 58'' values (20 / 59,603 / 44,730 / 14,473 / 400 / 332 / 249 / 83)") if F == 's39' else (
       "re-derived from era-5c's 60-KINDORDER cache (era5c-r215-kindorder, the twenty on host-b); CONTROL: the same run on the S39 cache "
       "reproduces 58''''s values (" + LSCTL + ")")
for k in SOLVE_LAYER:
    c = LSC
    if S60 and lays[k] != rec[k] and k in ('layer1.ref', 'layer1.raw', 'layer1.owning'):
        c = mk_cause(LSC, f"the Ref > Owning > Raw order (60s): model slots S39 -> 60s' {HMV} (cache/heads/models.tsv, bounded head reads); "
                     "main 225: 229 slots newly Owning at depth 0 (222 Raw -> Owning, 7 Ref -> Owning)")
    if F == 's39' and k in ('layer1.ref', 'layer1.raw'):
        c = mk_cause(LSC, 'the relaxation moves 15 model slots ref -> raw on net (heads: 14u -> S39 per program in cache/heads/summary.txt)')
    put(k, lays[k], LYS + f' row {k}', cause=c)
for k in ['census.data-flag', 'census.delivery-flag', 'layer1.declarations', 'layer1.decided-raw', 'layer1.excluded-items', 'delivery.programs-degraded',
          'delivery.not-placed', 'hold.io-domain', 'hold.void-pointee', 'hold.thin-extent']:
    c = ''
    if k == 'census.data-flag' and S60:
        c = 'census-receipt status=complete data=true (custody 20 / 20; ledger-only 0, tree-only 0)'
    if k == 'census.data-flag' and F == 's39':
        c = 'census-receipt status=complete-with-typed-failure data=false: the typed failure is tulipindicators\' delivery custody (identity-mismatch, 4 ledger-only rows)'
    if k == 'census.delivery-flag':
        c = {             's39': 'census-receipt delivery=degraded (a complete-with-typed-failure receipt; no hold-census gate lines are written)',
             '60sp': 'census-receipt delivery=regressed (regressed_programs=14): the standing comparator reading since 58 (main 225 s1)'}[F]
    if k == 'layer1.decided-raw':
        c = f'raw family undelivered and not decided safe (D6); {TREEC}'
    if k == 'delivery.not-placed':
        c = f'in-scope neither delivered nor reverted: {UNIV} - {DELIV} - {lay["layer2.reverted"]} = {lay["layer2.not-placed"]}' + (' (the four tree-raw custody rows are not placed)' if F == 's39' else
            " (the 229 newly Owning slots enter the decided-safe universe undelivered; rq5 group: all 212 new undelivered rows read generator)")
    if k == 'delivery.programs-degraded' and F == 's39':
        c = 'the typed-failure receipt carries no programs_degraded line: read from per-program.kv raw_boundary_outcome_kind (20 emitted)'
    pv_ = layprov.get(ALIAS.get(k, k), '')
    mbp = re.search(r'(by program [^;]*|raw family [^;]*)$', pv_)
    if mbp and lay[ALIAS.get(k, k)] != rec[k]:
        c = mk_cause(c, mbp.group(1))
    put(k, lay[ALIAS.get(k, k)], LY + f' row {ALIAS.get(k, k)}', cause=c)

# ---------------------------------------------------------------- strata / forms / cand
ST = f'{O}/strata-d6.tsv (r138 strata_d6.py on {CEN} + the frame\'s cache heads)'
STRC = {}
if S60:
    def _srows(path):
        c = collections.Counter()
        for r in csv.DictReader(open(path), delimiter='\t'):
            c[(r['stratum'], r['program'])] += 1
        return c
    _s0, _s1 = _srows(PO + '/strata-rows-d6.tsv'), _srows(O + '/strata-rows-d6.tsv')
    _sd = lambda st: ', '.join(f'{p} {_s0[(x, p)]} -> {_s1[(x, p)]}' for (x, p) in sorted(set(_s0) | set(_s1)) if x == st and _s0[(x, p)] != _s1[(x, p)])
    ORD = (f"the Ref > Owning > Raw order (60s): model slots S39 -> 60s' {HMV} (cache/heads/models.tsv); at depth 0, 229 subjects newly model "
           f"Owning (main 225 s0: 222 Raw -> Owning, 7 Ref -> Owning)")
    STRC = {'owning': ORD + "; owning.decided counts model Owning (d0) or decided box, whatever the outcome",
            'depth': ORD + '; depth rows by program against 58\'\'\': ' + (_sd('depth') or 'unchanged') + '; depth-field rows: ' + (_sd('depth-field') or 'unchanged'),
            'outparam': ORD + '; outparam.decided = pointer formals of ptr_depth >= 2 whose inner slot (d1..) the model now decides Owning',
            'fields': ORD}
for k in keys:
    if k.startswith('rq1.strata.') and k in strata:
        c_ = BOXC if k == 'rq1.strata.owning.delivered' else STRC.get(k.split('.')[2], '')
        put(k, strata[k], ST, cause=(c_ if strata[k] != rec[k] else ''))
FO = (f'{O}/forms-d6.out (r138 rq5_forms_d6.py on {CEN}, rows = the rq5 group\'s row-level rows '
      + {'s39': 'r141/rq5/out/rows-final-b58ppp.tsv (read-only copy work/in141/, md5 a18f1980, 13:30Z)',
         '60sp': 'r146/rq5/out60sp/rows-final-b60sp.tsv (read-only copy work/in146/, md5 1f2ea1c4, 21:38Z)'}[F]
      + ', --emitted-form, the R454 group of the rq5 group\'s rows-*-main.tsv, the frame\'s d0 fatness facts'
      + ('; byte-identical to the rq5 group\'s forms-58ppp-rowlevel.out (their tree reading)' if F == 's39' else
         '; byte-identical to the rq5 group\'s forms-60sp-rowlevel.out') + ')')
def fdump(path):
    d = collections.Counter()
    for r in csv.DictReader(open(path), delimiter='\t'):
        d[(r['program'], r['form'])] += 1
    return d
FDIFF = ''
if F == 's39':
    fa, fb = fdump(f'{PO}/forms-dump.tsv'), fdump(O + '/forms-dump.tsv')
    dd = sorted((k, fb[k] - fa[k]) for k in set(fa) | set(fb) if fa[k] != fb[k])
    tot5 = {r['program']: r for r in csv.DictReader(open(W + '/in141/totals-b58ppp.tsv'), delimiter='\t')}['total']
    FDIFF = ("decided safe 4,272 -> 4,301 (+29; the relaxation makes subjects safe in the model), by program x form: "
             + ', '.join(f'{p} {f} {v:+d}' for (p, f), v in dd)
             + f"; withheld = the rq5 group's row-level side-condition rows at 58''' ({tot5['side-condition']}; generator {tot5['generator']}, held "
             f"{tot5['held']}, no-safe-form {tot5['no-safe-form']}, undefined {tot5['undefined']}, form-fact {tot5['form-fact']}); delivered by the tree "
             "(the four custody rows: 3 slice, 1 optref -> notplaced); reverted 18 -> 6 (brotli 2, tulipindicators 4: get_array 3 + ti_find_indicator 1)")
if S60:
    fa, fb = fdump(f'{PO}/forms-dump.tsv'), fdump(O + '/forms-dump.tsv')
    dd = sorted((k, fb[k] - fa[k]) for k in set(fa) | set(fb) if fa[k] != fb[k])
    tot5 = {r['program']: r for r in csv.DictReader(open(W + '/in146/totals-b60sp.tsv'), delimiter='\t')}['total']
    rvp = sorted((r['program'], r['form']) for r in csv.DictReader(open(O + '/forms-dump.tsv'), delimiter='\t') if r.get('delivery') == 'reverted') if 'delivery' in open(O + '/forms-dump.tsv').readline() else []
    FDIFF = ("decided safe 4,301 -> 4,530 (+229: the Ref > Owning > Raw order makes 229 slots model Owning, decided safe in the box forms), "
             "by program x form against 58''': " + ', '.join(f'{p} {f} {v:+d}' for (p, f), v in dd)
             + f"; withheld = the rq5 group's row-level side-condition rows at 60s' ({tot5['side-condition']}; generator {tot5['generator']}, held "
             f"{tot5['held']}, no-safe-form {tot5['no-safe-form']}, undefined {tot5['undefined']}, form-fact {tot5['form-fact']}); delivered by the tree "
             f"(= the ledger at 60s'); reverted 6 -> {FORMS['total']['reverted']}" + (f' {rvp}' if rvp else ''))
for f in ('slice', 'cursor'):
    for col in ('decided', 'delivered'):
        put(f'rq1.strata.{f}.{col}', FORMS[f][col], FO + f' row {f} col {col}', cause=FDIFF if FORMS[f][col] != rec[f'rq1.strata.{f}.{col}'] else '')
    CANDC = ''
    if cand[f + '.cand.union'] != rec[f'rq1.strata.{f}.cand']:
        cpp = eval(open(f'{PO}/cand.out').read().split('# per program ', 1)[1].splitlines()[0])
        css = eval(open(O + '/cand.out').read().split('# per program ', 1)[1].splitlines()[0])
        CANDC = (f'{f}.cand.union by program against {PREV}: ' + ', '.join(f'{q} {cpp.get(q, {}).get(f + ".cand.union", 0)} -> {css.get(q, {}).get(f + ".cand.union", 0)}'
                 for q in sorted(set(cpp) | set(css)) if cpp.get(q, {}).get(f + '.cand.union', 0) != css.get(q, {}).get(f + '.cand.union', 0))
                 + f'; {f}.cand (the model\'s array-like facts alone) {cand[f + ".cand"]}; the union adds decided-{f} subjects outside the fact'
                 + (' (the relaxation\'s new safe decisions)' if F == 's39' else ''))
    put(f'rq1.strata.{f}.cand', cand[f + '.cand.union'], cause=CANDC, src= f'{O}/cand.out ({f}.cand.union; cand.py on {CEN} + the frame\'s QualifierFacts '
        f'({"cache/qfacts/qfacts-s39.tsv, streamed from the S39 cache" if F == "s39" else "cache/qfacts/qfacts-60sp.tsv, streamed from era5c-r215-kindorder (= the rq5 group\'s qfacts-60sp.tsv byte for byte)"}) + forms-dump.tsv (rq5_forms_ef.py RQ5_FORMS_DUMP))')
for k in keys:
    m = re.match(r'rq5\.form\.(\w+)\.(\w+)$', k)
    if m:
        put(k, FORMS[m.group(1)][m.group(2)], FO + f' row {m.group(1)} col {m.group(2)}', cause=FDIFF if FORMS[m.group(1)][m.group(2)] != rec[k] else '')

# ---------------------------------------------------------------- RQ5 pairs / verify
PE = f'{O}/pair-table.out "pair sites" line (069 pair_table.py on {CEN})'
PAIRC = ''
if True:  # r146: against the previous frame
    def npk(Cd):
        st = set()
        for f_ in os.listdir(Cd):
            if f_.endswith('.raw-boundary-pairs.tsv'):
                for r in csv.DictReader(open(f'{Cd}/{f_}'), delimiter='\t'):
                    for q in r['peer_receipts'].split(';'):
                        if q and q.split(':', 1)[1].startswith('overlapping'):
                            st.add((r['program'], r['caller'], r['callee'], q.split(':', 1)[0]))
        return st
    na_, nb_ = npk({'s39': M + '/batch58pp', '60sp': TREE}[F]), npk(CEN)
    pa = re.findall(r'^(\w[\w.]*) (\{.*\})$', open(f'{PO}/pair-table.out').read(), re.M)
    pb_ = re.findall(r'^(\w[\w.]*) (\{.*\})$', pt, re.M)
    pmv = [f'{a[0]} rows {a[1]} -> {b[1]}' for a, b in zip(pa, pb_) if a != b]
    PAIRC = (f"against {PREV}: not-proven pair keys gone " + str(sorted(na_ - nb_)) + ', new ' + str(sorted(nb_ - na_)) + '; ' + '; '.join(pmv))
put('rq5.pair.sites', sum(sites.values()), PE + f': {sites}', cause=PAIRC)
put('rq5.pair.not-proven', sites['not-proven'], PE, cause=PAIRC)
put('rq5.pair.clear.classifier', sites['classifier'], PE)
put('rq5.pair.clear.certificate', sum(v for k, v in sites.items() if k not in ('not-proven', 'classifier')), PE + ' (sum of the certificate kinds incl. caller-parameter-pair)')
for k, s in {'type-rule': 'type-rule', 'distinct-roots': 'distinct-roots', 'disjoint-fields': 'disjoint-fields', 'static-vs-entry': 'static-vs-entry:exported-entry-static-waiver',
             'exported-entry-waiver': 'exported-entry-waiver', 'parameter-pair': 'parameter-pair', 'allocator-contract': 'allocator-contract'}.items():
    put(f'rq5.pair.clear.{k}', sites[s], PE)
BORROWCK = {'E0373', 'E0381', 'E0382', 'E0384', 'E0499', 'E0502', 'E0503', 'E0505', 'E0506', 'E0507', 'E0515', 'E0521', 'E0596', 'E0597', 'E0713', 'E0716'}
vrev, diags = [], []
for f in sorted(os.listdir(CEN)):
    if f.endswith('.raw-boundary-final-reverts.tsv'):
        for r in csv.DictReader(open(f'{CEN}/{f}'), delimiter='\t'):
            if r['kind'] == 'function' and r['attribution'] == 'verify-reverted' and not r['identity'].startswith('class#'):
                vrev.append((r['program'], r['identity']))
    if f.endswith('.raw-boundary-compiler-diagnostics.tsv'):
        for r in csv.DictReader(open(f'{CEN}/{f}'), delimiter='\t'):
            diags.append((r['program'], r['function'], r['error_code']))
bck = [d for d in diags if d[2] in BORROWCK]
_fra = collections.Counter()
for f in sorted(os.listdir(CEN)):
    if f.endswith('.raw-boundary-final-reverts.tsv'):
        for r in csv.DictReader(open(f'{CEN}/{f}'), delimiter='\t'):
            _fra[(r['program'], r['attribution'].split(':')[0] + (':' + r['attribution'].split(':')[1] if r['attribution'].startswith('held:') else ''))] += 1
FRA = ', '.join(f'{p} {a} {n}' for (p, a), n in sorted(_fra.items()))
VE = f'{O}/verify.out (verify_frame13.py on {CEN}) + <p>.raw-boundary-compiler-diagnostics.tsv / final-reverts.tsv'
put('rq5.verify.borrow-check', len(bck), VE + f': diagnostics {diags}; borrow-check codes among them: {len(bck)}')
put('rq5.verify.type', len(vrev), VE + f': functions verify-reverted on a type error: {vrev} (closure reverts not counted: '
    + str([(r['program'], r['identity']) for f in os.listdir(CEN) if f.endswith('final-reverts.tsv') for r in csv.DictReader(open(f'{CEN}/{f}'), delimiter='\t') if r['attribution'] == 'closure:partition']) + ')',
    cause=("58'' -> 58''': brotli ClusterBlocksDistance and BrotliHistogramCombineDistance (class#1498, E0599) no longer revert; tulipindicators "
           "smoke::get_array is new (E0308, expected &mut f64, found &mut [f64]; era-5c 167c s2), ti_find_indicator reverted by closure; = main 219 s4" if F == 's39' else
           f"58''' -> 60s': tulipindicators smoke::get_array and brotli BuildAndStoreCommandPrefixCode no longer revert (compiler diagnostics {len(diags)} at 60s', main 225 s5); "
           f"the final function reverts by attribution: {FRA}; compile-check type reverts {len(vrev)}"))

# ---------------------------------------------------------------- premises
def p7rows(t):
    sec = re.split(r'^rows only at ', t, flags=re.M)
    gone = [l for l in sec[1].splitlines()[1:] if l.startswith('   (')]
    new = [l for l in sec[2].splitlines()[1:] if l.startswith('   (')]
    nasg = int(re.search(r'assignment kinds: (\d+)', sec[3]).group(1)) if len(sec) > 3 else 0
    def nm(l):
        x = eval(l.strip())
        return f"{x[0]} {x[3].split('::')[-1]} {x[4]} ({x[2]})"
    def grp(ls):
        c = collections.Counter(nm(l) for l in ls)
        return ', '.join(f'{k}' + (f' x{v}' if v > 1 else '') for k, v in c.items())
    return (f"row-level against {PREV}: {len(gone)} rows leave" + (f' ({grp(gone)})' if gone else '') + f", {len(new) + nasg} enter "
            f"(non-assignment {len(new)}: {grp(new)}; assignment kinds {nasg}); 58''' rows that left at 60s' none")
pbd = open(O + '/premise-bd-vs-prev.out').read()
mpb = re.search(re.escape(os.path.basename(CEN)) + r" total (\d+) (\{.*?\}) call-bridge formals (\d+)", pbd)
need(mpb, 'premise bd')
pk = eval(mpb.group(2))
PB = (f'{O}/premise-bd-vs-prev.out (n141/premise_bd141.py over <p>.raw-boundary-premise-bridge-dereferenceable.tsv; = census-receipt '
      f'premise_bridge_dereferenceable={mpb.group(1)}' + ("; = main 219 'P7 267 (call-bridge 177, declaration-construction 71, assignment-view 11, "
      "assignment-option-construction 6, declaration-view 2)'" if F == 's39' else
      "; = main 225 'P7 283 (call-bridge 188)'") + ')')
P7C = ("row-level against 58'': 13 rows leave (brotli InitBlockSplitterDistance / InitContextBlockSplitter m, heman kmRay2FillWithEndpoints end, "
       "libzahl zswap b x5, tulipindicators smoke::get_array num x2, smoke::test_ind_name s / info, fuzzer::main_0 info_0: their functions or "
       "callees moved), 8 enter (brotli BrotliZopfliCreateCommands num_literals x2, InitBlockSplitterCommand m, libzahl zswap a x5)") if F == 's39' else p7rows(pbd)
put('premise.bridge-dereferenceable.call-bridge', pk.get('call-bridge', 0), PB, cause=P7C)
put('premise.bridge-dereferenceable.declaration-construction', pk.get('declaration-construction', 0), PB, cause=P7C)
put('premise.bridge-dereferenceable.declaration-view', pk.get('declaration-view', 0), PB, cause=P7C)
put('premise.bridge-dereferenceable.declaration-reborrow', pk.get('declaration-reborrow', 0), PB)
cv = open(O + '/cv-rows-vs-prev.out').read()
need('identical on all non-frame columns: True' in cv, 'call-view rows moved')
need('call-view formals identical: 11 / 11' in open(O + '/cvformals-vs-prev.out').read(), 'call-view formals moved')
need(open(O + '/optview-split.out').read() == open(f'{PO}/optview-split.out').read(), 'optview split moved')
CV = (f'{O}/cv-rows-vs-prev.out (n141/cv_rows141.py): the 78 placed raw -> Option<&T> call-argument view rows are IDENTICAL to {PREV}\'s on every '
      f'column after the 13 frame-header columns; optview-split.out identical; main 213a\'s reader (a cargo test) is not re-run; the 11 '
      f'call-view formals keep family / model kind / decision / reason (optional / ref / optional / -) at {FT} (cvformals-vs-prev.out, n141/cvformals146.py: 11 / 11); so the 63 rows are carried by identical input')
put('premise.bridge-dereferenceable.call-view', 63, CV, cause='CAVEAT: reader rule (b) also reads the held state; none of the 11 call-view formals is held at ' + FT)
put('premise.bridge-dereferenceable', int(mpb.group(1)) + 63, PB + ' + call-view 63 (' + CV[:160] + '...)', cause=P7C)
s17 = open(O + '/s17/join.out').read()
mtr = re.search(r"TOTAL typed-release (\{.*\})", s17); mrz = re.search(r"TOTAL realloc-nonzero (\{.*\})", s17)
need(mtr and mrz, 's17')
tr, rz = eval(mtr.group(1)), eval(mrz.group(1))
dtr = collections.Counter(l.split('\t')[0] for l in open(O + '/s17/decl-typed-release.txt'))
drz = collections.Counter(l.split('\t')[0] for l in open(O + '/s17/decl-realloc-nonzero.txt'))
SJ = (f'{O}/s17/join.out (r110 s17u premise_join.py re-pointed: the frame\'s retirement-final discharge receipts '
      f'({CA}/s17/out-{F}, final_discharges.py mmap scan of the frame\'s cache) joined through keymap141/{F}/reverse-index.tsv)')
S17C = ("re-derived from the S39 cache (115 read the L01^14u extraction); CONTROL: the same extraction + join on L01^14u reproduces "
        "r140's join.out, premise-sites.tsv, premise-targets.tsv and decl-typed-release.txt byte for byte") if F == 's39' else (
        "re-derived from era-5c's 60-KINDORDER cache; CONTROL: the same extraction + join on the S39 cache reproduces r141's join.out, "
        "premise-sites.tsv, premise-targets.tsv and both decl files byte for byte")
put('premise.typed-release.sites', tr['sites'], SJ + f': {tr}', cause=S17C)
put('premise.realloc-nonzero.sites', rz['sites'], SJ + f': {rz}', cause=S17C)
put('premise.typed-release.declarations', tr['declarations'], SJ + ' (' + ', '.join(f'{p} {n}' for p, n in dtr.most_common()) + ')', cause=S17C)
put('premise.realloc-nonzero.declarations', rz['declarations'], SJ + ' (' + ', '.join(f'{p} {n}' for p, n in drz.most_common()) + ')', cause=S17C)
ac = open(O + '/alloc-contract.out').read()
mac = re.search(r"brotli receipt kinds .* admitted (\d+) (\{.*\}) delivered forms (\{.*\}) unjoined (\d+)", ac)
need(mac, 'alloc')
acst = eval(mac.group(2))
acd = sum(v for (fam, dl), v in acst.items() if dl == 'realized-as-predicted')
AC = (f'{O}/alloc-contract.out (alloc_contract_r140.py, 045\'s printed method; control on main/b54p reproduces 045 (r140)): brotli '
      f'{mac.group(1)} admitted under allocator-contract:brotli-memory-manager/v1 = {acst}; urlparser libc/v1 apart')
put('premise.allocator-contract.declarations', acd, AC,
    cause=(("brotli's 99 admitted subjects at 58'': " + re.search(r"brotli receipt kinds .* admitted \d+ (\{.*\}) delivered forms", open(f'{PO}/alloc-contract.out').read()).group(1)
            + f" -> at 58''': {acst} (class#1498 ClusterBlocksDistance is no longer verify-reverted)") if F == 's39' else (
           ("brotli's 99 admitted subjects at 58''': " + re.search(r"brotli receipt kinds .* admitted \d+ (\{.*\}) delivered forms", open(f'{PO}/alloc-contract.out').read()).group(1)
            + f" -> at 60s': {acst}"))))
put('premise.allocator-contract.pair-sites', sites['allocator-contract'], PE + ': the allocator-contract column (the r140 verifier\'s vpairs.py = 045\'s pair-table count; '
    'the same counter as rq5.pair.clear.allocator-contract)')
rt = open(O + '/raw-twin.out').read()
mrt = re.search(re.escape(os.path.basename(RAW)) + r' functions (\d+) calls (\d+)', rt)
need(mrt, 'raw twin')
def twin_block(t, name):
    return t.split(name + ' functions', 1)[1].split('\n', 1)[1].strip()
RTC = ''
if S60:
    _a, _b = twin_block(open(PO + '/raw-twin.out').read(), 'batch58pps39'), twin_block(rt, os.path.basename(RAW))
    _da = {l.split()[0]: l.strip() for l in _a.splitlines()}; _db = {l.split()[0]: l.strip() for l in _b.splitlines()}
    RTC = "against 58''': " + '; '.join(f'{p}: {_da.get(p, "-")} -> {_db.get(p, "-")}' for p in sorted(set(_da) | set(_db)) if _da.get(p) != _db.get(p))
put('codegen.raw-twin.functions', mrt.group(1), f'{O}/raw-twin.out (r110 raw_twin.py batch58 {os.path.basename(RAW)})', cause=RTC if mrt.group(1) != rec['codegen.raw-twin.functions'] else '')
put('codegen.raw-twin.calls', mrt.group(2), f'{O}/raw-twin.out (r110 raw_twin.py batch58 {os.path.basename(RAW)}' + (': per program identical to 58)' if F == 's39' else ')'), cause=RTC if mrt.group(2) != rec['codegen.raw-twin.calls'] else '')

# ---------------------------------------------------------------- box.param
opr = open(O + '/owning-params.out').read()
mo1 = re.search(r'model-Owning formal slots: (\d+)', opr); mo2 = re.search(r'  delivered: (\d+) ', opr); mo3 = re.search(r'  held: Counter\((\{.*\})\)', opr)
mo4 = re.search(r'chain-slice .*: (\d+)', opr)
need(mo1 and mo2 and mo3 and mo4, 'owning params')
BP = (f'{O}/owning-params.out (r133 owning_params_58.py re-pointed: keymap141/{F}/keymap.tsv and the frame\'s QualifierFacts; '
      f'subject set and model_kind identical to the keymap 7,011 / 7,011)')
mfat = re.search(r'  by fatness: Counter\((\{.*\})\)', opr); mdep = re.search(r'  by depth: Counter\((\{.*\})\)', opr)
need(mfat and mdep, 'owning params fatness / depth')
fat = eval(mfat.group(1))
dlv = re.findall(r'^    (\S+) (\S+) \((\S+), .realized-as-predicted., (\S+), ', opr, re.M)
need(len(dlv) == int(mo2.group(1)), ('delivered rows', len(dlv), mo2.group(1)))
DLV = ', '.join(f"{p} {k.split('::')[-1]} ({e.strip(chr(39))})" for p, k, fam, e in dlv)
BPC = ''
if S60:
    BPC = (f"the Ref > Owning > Raw order (60s): model-Owning formal slots 14 -> {mo1.group(1)} (by depth {mdep.group(1)}, by fatness {mfat.group(1)}); "
           f"delivered {mo2.group(1)}: {DLV}; held {mo3.group(1)} (box-param-lend-withheld: the A9 reference lend withheld, wave-6a e3afd991e, main 225 s4)")
put('box.param.owning', mo1.group(1), BP + f': by depth {mdep.group(1)}, by fatness {mfat.group(1)}', cause=BPC if mo1.group(1) != rec['box.param.owning'] else '')
put('box.param.owning.delivered', mo2.group(1), BP + (': avl 3, bst 2, ht 1, quadtree quadtree_free::tree#1, tulipindicators ti_buffer_free::buffer#1' if F == 's39' else ': ' + DLV),
    cause=BPC if mo2.group(1) != rec['box.param.owning.delivered'] else '')
put('box.param.owning.held', sum(eval(mo3.group(1)).values()), BP + f': {mo3.group(1)}', cause=BPC if str(sum(eval(mo3.group(1)).values())) != rec['box.param.owning.held'] else '')
put('box.param.owning-array', fat.get('array-like', 0), BP + (': by fatness all ptr-default' if not fat.get('array-like') else f': by fatness {mfat.group(1)} (array-like = the QualifierFacts d0/dK fatness fact of the formal slot)'),
    cause=BPC if str(fat.get('array-like', 0)) != rec['box.param.owning-array'] else '')
put('box.param.chain-slice', mo4.group(1), BP + ': buffer buffer_new_with_string{,_length}::str#1 box-slice')

# ---------------------------------------------------------------- decl wins / ties (R945-1)
T5 = {'s39': R141 + '/trees/t5r945/per-program.tsv', '60sp': R146 + '/trees/t5r945-60sp/per-program.tsv'}[F]
t5 = list(csv.DictReader(open(T5), delimiter='\t'))
wins = [r['program'] for r in t5 if int(r['ours_made']) > int(r['crown_made'])]
ties = [r['program'] for r in t5 if int(r['ours_made']) == int(r['crown_made'])]
TW = (f'wins_ties_r945.py over the trees group\'s {T5} (Table 5 under R945-1, CROWN\'s counter in full; read-only'
      + (', md5 a9601198, 13:26Z' if F == 's39' else ', md5 854f5b66, 21:36Z') + '): per program ours_made vs crown_made over the same U')
WTC = ''
if S60:
    t5p = {r['program']: r for r in csv.DictReader(open(R141 + '/trees/t5r945/per-program.tsv'), delimiter='\t')}
    mv = [f"{r['program']} {t5p[r['program']]['ours_made']} -> {r['ours_made']}" for r in t5 if t5p[r['program']]['ours_made'] != r['ours_made']]
    wp = [r['program'] for r in t5p.values() if int(r['ours_made']) > int(r['crown_made'])]
    tp = [r['program'] for r in t5p.values() if int(r['ours_made']) == int(r['crown_made'])]
    WTC = (f"made against 58''': {', '.join(mv) or 'none'}; " + ('no win or tie changes side' if (sorted(wp), sorted(tp)) == (sorted(wins), sorted(ties)) else f'58\'\'\' wins {wp} ties {tp}'))
put('rq2.wins.decl', len(wins), TW + ': wins ' + ', '.join(wins), cause=('brotli 338 -> 343, heman 215 -> 217, tulipindicators 102 -> 114 made; no win or tie changes side' if F == 's39' else WTC))
put('rq2.ties.decl', len(ties), TW + ': ties ' + ', '.join(ties), cause=(WTC if S60 else ''))

# ---------------------------------------------------------------- rq3 / setup
RT = kv(O + '/rq3times.tsv')
RTH = open(O + '/rq3times.tsv').readline().strip()
need(len([k for k in RT if k.startswith('rq3.') and k.count('.') == 2]) == 23, 'rq3times: 20 + total + largest + rest')
SG = f'{O}/seed-g5.tsv (seed_g5.py re-pointed: the frame\'s solve dir; host-b entries read from the row\'s own cache dir)'
if not S60:
    TIM = ("carried: the record KEEPS the L01^14u census's single wall reading (report 100 Q1; the seat's call which run the cost keys cite); "
           "{ft}'s cache-only census reads {v} ({src})")
    put('rq3.largest.check-s', rec['rq3.largest.check-s'], TIM.format(ft=FT, v=g5['rq3.largest.check-s'], src=f'{O}/seed-g5.tsv'), verdict='carried')
    put('rq3.rest.check-s', rec['rq3.rest.check-s'], TIM.format(ft=FT, v=g5['rq3.rest.check-s'], src=f'{O}/seed-g5.tsv' + '; tulipindicators, the typed failure, writes no timings table'), verdict='carried')
    put('rq3.largest.emit-s', rec['rq3.largest.emit-s'], TIM.format(ft=FT, v=sn['rq3.largest.emit-s'], src=f'{O}/seed_numbers.out (worker_wall_s)'), verdict='carried')
    put('rq3.rest.emit-s', rec['rq3.rest.emit-s'], TIM.format(ft=FT, v=sn['rq3.rest.emit-s'], src=f'{O}/seed_numbers.out'), verdict='carried')
    put('rq3.largest.analysis-s', rec['rq3.largest.analysis-s'], "carried: the record keeps the L01^14u solve's progress.jsonl wall_s (report 100 Q1); no solve at the census"
        + " (S39's brotli solve: A2 on host-b, 12,982 s; notes Q)", verdict='carried')
    put('rq3.rest.analysis-s', rec['rq3.rest.analysis-s'], "carried: the record keeps the L01^14u solve's progress.jsonl wall_s (report 100 Q1); no solve at the census"
        + " (S39's other nineteen: ten on host-a, nine on host-b, concurrent, sum 35,717 s; notes Q)", verdict='carried')
    for k in RQ3P:
        put(k, RT[k], f'{O}/rq3times.tsv (n141/rq3times146.py on era5c-l01p14u-solve: the record\'s solve; CONTROL for 60s\'s re-seed)', verdict='carried')
else:
    RQ1RULE = ("RE-SEEDED: report 100's Q1 rule (the record keeps ONE wall reading per frame) now reads this frame's solve: the frame moved to "
               "era-5c's 60-KINDORDER solve (worktrees/era5c-r215-kindorder; analysis 1d8dcd40, configuration d9a474da, launch 2e94d9a5); "
               "every program ran on host-b (workers/<p>.json host, era-5c 172b), 03:01Z-11:24Z 10-13, up to 3 programs at once (launch..complete "
               "in progress.jsonl), where the L01^14u solve ran one program at a time on host-a; the CONTROL (the same reader on era5c-l01p14u-solve) "
               "reproduces the record's 23 values (20 + total + largest + rest)")
    SRT = f'{O}/rq3times.tsv (n141/rq3times146.py: progress.jsonl wall_s of each program\'s complete record; {RTH[2:]})'
    for k in RQ3P:
        p = k.split('.')[1]
        put(k, RT[k], SRT + (f' row {k}' if k != 'rq3.total.analysis-s' else ': the sum of the twenty'), cause=RQ1RULE)
    put('rq3.largest.analysis-s', RT['rq3.largest.analysis-s'], SRT + f": brotli {RT['rq3.brotli.analysis-s']} s, integer as seed_numbers.py prints it (format :.0f, half to even; "
        f"seed_numbers.py --solve era5c-r215-kindorder gives {sn['rq3.largest.analysis-s']})", cause=RQ1RULE)
    put('rq3.rest.analysis-s', RT['rq3.rest.analysis-s'], SRT + f": the other nineteen summed (seed_numbers.py gives {sn['rq3.rest.analysis-s']})", cause=RQ1RULE)
    need(RT['rq3.largest.analysis-s'] == sn['rq3.largest.analysis-s'] and RT['rq3.rest.analysis-s'] == sn['rq3.rest.analysis-s'], 'rq3times vs seed_numbers')
    CEMIT = ("RE-SEEDED with the analysis times (report 100's Q1 rule, one wall reading per frame): the frame moved, and this is the final frame's census "
             "(main/batch60sp, main 225: cache-only, alone under the census lock 18:52Z-21:21Z 10-13, on host-a); the record's previous reading was "
             "the L01^14u census's (batch 56's frame)")
    put('rq3.largest.check-s', g5['rq3.largest.check-s'], f'{O}/seed-g5.tsv (seed_g5.py: <p>.raw-boundary-timings.tsv initial_verify_s): brotli', cause=CEMIT)
    put('rq3.rest.check-s', g5['rq3.rest.check-s'], f'{O}/seed-g5.tsv: the other nineteen summed', cause=CEMIT)
    put('rq3.largest.emit-s', sn['rq3.largest.emit-s'], f'{O}/seed_numbers.out (per-program.kv worker_wall_s): brotli', cause=CEMIT)
    put('rq3.rest.emit-s', sn['rq3.rest.emit-s'], f'{O}/seed_numbers.out: the other nineteen summed', cause=CEMIT)
put('rq3.largest.verify-rounds', sn['rq3.largest.verify-rounds'], f'{O}/seed_numbers.out (brotli raw-boundary-outcome.tsv verify_rounds; seed_numbers.py --dry-run against a read-only record copy, md5 unchanged)',
    cause=("brotli verifies in one round at 60s': no compiler diagnostic (main 225 s5), so no revert round; at 58''' the second round reverted "
           "BuildAndStoreCommandPrefixCode (E0599)") if S60 and sn['rq3.largest.verify-rounds'] != rec['rq3.largest.verify-rounds'] else '')
put('rq3.rest.sloc', sn['rq3.rest.sloc'], f'{O}/seed_numbers.out (substrate SLOC, frame-independent)')
put('rq3.largest.rounds', g5['rq3.largest.rounds'], SG + ': brotli final_selections per construction, retirement-rounds records, sum-check ok',
    cause=('re-derived from the S39 cache (brotli = A2\'s host-b entry); 115 carried it as the L01^14u cache\'s' if F == 's39' else 're-derived from era-5c\'s 60-KINDORDER cache'))
put('setup.depth.third-level-slots', g5['setup.depth.third-level-slots'], SG + ': slots @dK, K >= 2, in the frame\'s model heads (libzahl 1, robotfindskitten 13, all ref)',
    cause=('re-derived from the S39 cache' if F == 's39' else 're-derived from era-5c\'s 60-KINDORDER cache'))
put('setup.solver', rec['setup.solver'], f"carried: the solve's solver (no solve at the census: cache only); seed_g5 re-read = {g5['setup.solver']}"
    + (" (the S39 row's ten host-a solves and A2's ten host-b solves both ran Z3 4.15.4 through the same env)" if F == 's39' else
       " (the 60-KINDORDER solve on host-b: ablation-env.sh LD_LIBRARY_PATH names Z3's release z3-4.15.4-x64-glibc-2.39)"), verdict='carried')
for k in keys:
    if k.startswith('rq3.inator.'):
        put(k, rec[k], 'carried: &inator timings on host-b (092 / rq3-inator 018a); independent of our code and census', verdict='carried')

# ---------------------------------------------------------------- RQ4
RQ4T = (f"the record's RQ4 suite rows were last run on batch 56's trees (= frame14u's = 58''s for urlparser); diff -rq "
        f"main/batch56/emitted-trees/<p> {RAW}/emitted-trees/<p>: libtree, rgba, quadtree, genann, buffer differ, urlparser identical"
        + ("; 58''' against 58'': only libtree among the six differs (wave-6o relay 187 runs RQ4 on 58''' now)" if F == 's39' else
           "; 60s' against 58''': the six trees are byte-identical (diff -rq main/batch58pps39 vs main/batch60sp), so an RQ4 run on 58''''s trees reads 60s''s"))
d56 = {p: os.popen(f'diff -rq {M}/batch56/emitted-trees/{p} {RAW}/emitted-trees/{p}').read() == '' for p in ('libtree', 'rgba', 'quadtree', 'urlparser', 'genann', 'buffer')}
need(d56 == {'libtree': False, 'rgba': False, 'quadtree': False, 'urlparser': True, 'genann': False, 'buffer': False}, d56)
NA = {'s39': 'not-at-58ppp', '60sp': 'not-at-60sp'}[F]
if S60:
    need(all(os.popen(f'diff -rq {M}/batch58pps39/emitted-trees/{p} {RAW}/emitted-trees/{p}').read() == '' for p in ('libtree', 'rgba', 'quadtree', 'urlparser', 'genann', 'buffer')), 'six trees 58ppp vs 60sp')
for k in keys:
    if not k.startswith('rq4.') or k in V:
        continue
    if '.crown.' in k:
        put(k, rec[k], "carried: CROWN's Miri runs on CROWN's trees; independent of our census", verdict='carried')
    elif k in ('rq4.checker', 'rq4.discipline'):
        put(k, rec[k], 'carried: the Miri toolchain / aliasing discipline of the run; it describes the checker, not a tree', verdict='carried')
    elif k.startswith('rq4.suite.urlparser.'):
        put(k, rec[k], 'carried: ' + RQ4T, verdict='carried')
    elif k == 'rq4.suite.coverage.delivered-functions':
        put(k, '-', f'{NA}: ' + RQ4T + f'; the census reading at {FT} is {g5[k]} ({O}/seed-g5.tsv: wave-6o coverage.py delivered() over the six) '
            'and must pair with executed-functions of the same census', verdict=NA)
    else:
        put(k, '-', f'{NA}: ' + RQ4T + '; wave-6o runs RQ4 on the landed trees', verdict=NA)

# ---------------------------------------------------------------- custody
put('census.custody-mismatch', CUST, f'{O}/ec3.txt (071 ec3_keys.py on {RAW}: <p>.raw-boundary-delivery-custody.json ledger vs tree)',
    cause=(f"the census's one typed failure: tulipindicators delivery custody identity-mismatch, ledger-only {CUST} "
           "(fuzzer::main_0::{argv#2, info_0#20}, smoke::test_ind_name::{info#4, s#49}), tree-only 0; ledger 2,682, tree 2,678; "
           "every delivered count in this group is by the tree" if F == 's39' else
           "custody data=true on all twenty: ledger-only 0, tree-only 0 (main batch60sp-custody.txt); the 58''' typed failure (tulipindicators, 4 ledger-only rows) is gone"))

# ---------------------------------------------------------------- P11 (R936-1; R959-1 integers-only)
P11K = ('global-value', 'global-storage', 'integer')
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree', 'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
HEADFULL = {'s39': '3eaf5228dd05ea2c419b46fd2d055bb6c4e3d667', '60sp': '32d966b9fc2ef56fcd40e95ee762f73b0e0be70a'}[F]
FRAMEENV = W + '/in146/l01p14u-s39-mutlend-o-env.sh'  # git show 32d966b9f:crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh
ENVS = {'60sp': [M + '/batch60sp-extra-env.sh', M + '/frame-extra-env.sh', 'worktrees/era5c-r215-kindorder/ablation-env.sh', FRAMEENV],
        's39': ['scratch/era-5c/r211/s39pp-extra-env.sh', M + '/frame-extra-env.sh', 'worktrees/era5c-r211-s39pp/ablation-env.sh']}[F]
for e in ENVS:
    need('CRAT_P11_SCOPE' not in open(e).read(), e)
prow = []
for p in PROGS:
    prow += list(csv.DictReader(open(f'{RAW}/{p}.raw-boundary-pair-premise.tsv'), delimiter='\t'))
need({r['code_frame'] for r in prow} == {HEADFULL}, 'pair-premise code frame')
need({r['scope'] for r in prow} <= {'integers-only'}, 'scope')
pk11 = collections.Counter(r['kind'] for r in prow)
p11 = [r for r in prow if r['kind'] in P11K]
WP = open(M + ('/batch58pps39-p11.txt' if F == 's39' else '/batch60sp-p11.txt')).read()
wg = int(re.search(r'P11 global kinds \(global-value \+ global-storage\): (\d+)', WP).group(1))
need(wg == sum(1 for r in p11 if r['kind'] != 'integer'), 'p11 waiver line')
P11S = (f'{RAW}/<p>.raw-boundary-pair-premise.tsv (r133/p11 producer re-pointed: one site = one row with kind in global-value | global-storage | '
        f'integer; every row\'s code_frame {HEADFULL[:9]} and scope integers-only; CRAT_P11_SCOPE absent from ' + ', '.join(os.path.basename(e) for e in ENVS)
        + f'); all kinds in the twenty tables {dict(pk11)}; = main {os.path.basename(WP.split(chr(10))[0]) if False else ("batch58pps39-p11.txt" if F == "s39" else "batch60sp-p11.txt")} '
        f'"P11 global kinds (global-value + global-storage): {wg}"')
P11C = ("the default scope integers-only (R959-1): a global's value or storage is inside the claim; the tables' 28 rows are P5's "
        "premise=allocator-contract (brotli)")
put('premise.global-int.sites', len(p11), P11S, cause=P11C)
for k in P11K:
    put(f'premise.global-int.{k}.sites', sum(1 for r in p11 if r['kind'] == k), P11S, cause=P11C)
for p in PROGS:
    put(f'premise.global-int.{p.replace(".", "")}.sites', sum(1 for r in p11 if r['program'] == p), P11S + f' ({p}: ' + (', '.join(f'{a} {b}' for a, b in sorted(collections.Counter(r['kind'] for r in prow if r['program'] == p).items())) or 'no row') + ')')

# ---------------------------------------------------------------- write
missing = [k for k in keys if k not in V]
need(not missing, ('missing', missing))
out = {'s39': W + '/ctl/staged-ctl.tsv', '60sp': H + '/staged.tsv'}[F]
os.makedirs(os.path.dirname(out), exist_ok=True)
n = collections.Counter()
rows = []
for k in keys:
    v, verdict, cause, src = V[k]
    r = rec[k]
    if verdict is None:
        verdict = 'equal' if v == r else 'differs'
    if verdict == 'carried':
        need(v == r, ('carried but differs', k, r, v))
    txt = (cause + '; src: ' + src) if cause else ('src: ' + src)
    if verdict == 'differs':
        txt += f"; previously at {PREV}: {r}"
    txt = txt.replace('\t', ' ').replace('\n', ' ').replace('|', '/')
    need('|' not in v and '\t' not in v, k + ': bad value')
    n[verdict] += 1
    rows.append((k, r, v, verdict, txt))
with open(out, 'w') as w:
    w.write('key\tvalue_now\tvalue_' + {'s39': '58ppp', '60sp': '60sp'}[F] + '\tverdict\tcause\n')
    for row in rows:
        w.write('\t'.join(row) + '\n')
print(out, len(keys), dict(n))
if F == 's39':
    # CONTROL: compare with r141/census/staged.tsv value_58ppp (the 58-triple-prime write's own staged cells) on its 345 keys
    lines = []
    bad = 0
    for k, r, v, verdict, _ in rows:
        if k not in r141:
            continue
        now141, v141, verd141 = r141[k]
        ok = v == v141
        if not ok:
            bad += 1
            lines.append(f'MISMATCH {k}: control {v} ({verdict}) vs r141 staged {v141} ({verd141}); record now {rec[k]}')
    lines.append(f'control: {len(r141) - bad} of {len(r141)} keys reproduce r141/census/staged.tsv value_58ppp; {bad} mismatches')
    open(W + '/ctl/ctl-compare.txt', 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(lines))
