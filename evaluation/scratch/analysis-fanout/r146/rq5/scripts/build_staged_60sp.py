#!/usr/bin/env python3
"""r146 group rq5 (relay analysis-fanout 146, the FINAL re-seed): stage RQ5's keys at 60s' (main/batch60sp, head
32d966b9fc2ef56fcd40e95ee762f73b0e0be70a, era-5c's 60-KINDORDER cache), BY THE EMITTED TREE. This is r141's
build_staged_58ppp.py re-pointed: the control frame moves 58'' -> 58''' and the staged frame 58''' -> 60s'; compute()
is r141's, verbatim.

  build_staged_60sp.py control    recompute every key's value at 58''' from the re-pointed producers' CONTROL outputs
                                  (../ctl58ppp: main/batch58pps39 with the S39 cache's streamed fatness file) and compare
                                  with r141/rq5/staged.tsv value_58ppp (every non-carried key); exit non-zero on a mismatch
  build_staged_60sp.py stage      the same computation at 60s' (../out60sp) -> ../staged.tsv (key, value_now, value_60sp,
                                  verdict, cause; cause WITHOUT the frame header)

Reads only: ../record-current.md (= docs origin/main paper/numbers-of-record.md at the r146 fetch, md5 8371d530), the
census dirs, the outputs under ../out60sp, ../ctl58ppp and r141/rq5. Every check fails closed through raise SystemExit."""
import collections, csv, glob, json, os, re, sys
csv.field_size_limit(10 ** 9)
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
rd = lambda f: list(csv.DictReader(open(f), delimiter='\t'))
MAIN = 'scratch/main'
R454F = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
CAUSES = ['held', 'no-safe-form', 'undefined', 'type-system', 'side-condition', 'form-fact', 'generator']
FORMS = ['box', 'boxslice', 'cursor', 'optref', 'ref', 'slice']
COLS = ('decided', 'delivered', 'held', 'notplaced', 'reverted', 'licensed', 'withheld')


def need(c, msg):
    if not c:
        raise SystemExit('build_staged_60sp: FAIL: ' + str(msg))


R141 = 'scratch/analysis-fanout/r141/rq5'
FRAMES = {
    '58ppp': dict(C=f'{MAIN}/batch58pps39', D=f'{HERE}/ctl58ppp', tag='58ppp', forms='forms-58ppp-rowlevel.out',
                  verify='verify-batch58ppp.out', tree=True, DEL=2678, U=4301, W=915),
    '60sp': dict(C=f'{MAIN}/batch60sp', D=f'{HERE}/out60sp', tag='60sp', forms='forms-60sp-rowlevel.out',
                 verify='verify-batch60sp.out', tree=True, DEL=2715, U=4530, W=918),
}


def ledger_only(C):
    lo = set()
    for f in sorted(glob.glob(C + '/*.raw-boundary-delivery-custody.json')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        c = json.load(open(f))['comparison']
        led, tree = set(c.get('delivered_by_ledger') or []), set(c.get('delivered_by_tree') or [])
        need(not (tree - led), 'tree-only rows in ' + p)
        lo |= {(p, k) for k in led - tree}
    return lo


def forms(f):
    t = {}
    for l in open(f):
        if l.startswith(('#', 'form')):
            continue
        c = l.rstrip('\n').split('\t')
        t[c[0]] = dict(zip(['decided', 'withheld', 'licensed', 'delivered', 'reverted', 'notplaced', 'held'], map(int, c[1:])))
    return t


def compute(fr):
    F = FRAMES[fr]
    C, D, T = F['C'], F['D'], F['tag']
    R454 = {(r['program'], r['owner'], r['binding']) for r in rd(R454F) if r['counts_toward_N'] == 'true'}
    need(len(R454) == 36, 'R454')
    LO = ledger_only(C) if F['tree'] else set()
    U, DEL, LEDGER = set(), set(), set()
    for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        sj = {r['subject_key']: r for r in rd(f.replace('subject-outcomes', 'subjects'))}
        for o in rd(f):
            k = o['subject_key']
            key = re.sub(r'#\d+$', '', k)
            owner, _, b = key.rpartition('::')
            if (p, owner, b) in R454:
                continue
            led = o['delivery'] == 'realized-as-predicted'
            d = led and (p, k) not in LO
            if led:
                LEDGER.add((p, k))
            if d:
                DEL.add((p, k))
            if o['family'] in SAFE or led or sj[k]['decision'] in SAFE:
                U.add((p, k))
    need((len(DEL), len(U)) == (F['DEL'], F['U']), (fr, len(DEL), len(U)))
    rows = rd(f'{D}/rq5-rows-{T}.tsv')
    need({(r['program'], r['subject_key']) for r in rows} == U - DEL and len(rows) == len(U - DEL), 'row set != U - DEL')
    V = collections.Counter(r['cause'] for r in rows)
    V = {c: V.get(c, 0) for c in CAUSES}
    FIVE = sum(V[c] for c in ('no-safe-form', 'undefined', 'held', 'form-fact', 'generator'))
    NDEL, INS = len(DEL), len(U)
    LIC = NDEL + FIVE
    need(V['type-system'] == 0 and INS - NDEL == FIVE + V['side-condition'], 'partition')
    need(LIC + V['side-condition'] == INS, 'licensed + side-condition != universe')
    H = {(r['program'], r['subject_key']): r for r in rd(f'{D}/rate/holds.tsv') if r['in_scope'] == '1'}
    W = {k for k, r in H.items() if r['withheld_r956'] == '1'}
    need(len(W) == F['W'] and not (W & DEL), ('W', len(W)))
    DEN = INS - len(W)
    CZ = {(r['program'], r['subject_key']): r for r in rows}
    S = {k for k, r in CZ.items() if r['cause'] == 'side-condition'}
    need(W <= set(CZ), 'a withheld subject is not an RQ5 row')
    WS, WnS, SnW = W & S, W - S, S - W
    need(DEN - LIC == len(SnW) - len(WnS), 'R956-1 vs licensed')
    FT = forms(f'{D}/{F["forms"]}')
    need(FT['total']['withheld'] == V['side-condition'] and FT['total']['licensed'] == LIC and FT['total']['delivered'] == NDEL
         and FT['total']['decided'] == INS and FT['total']['held'] == V['held'], 'forms do not reconcile')
    vtxt = open(f'{D}/{F["verify"]}').read()
    m = re.search(r"compiler-rejected only \((\[[^\]]*\])\): programs (\d+); rows (\d+) = ([\d.]+) %; wholecrate (\d+) = ([\d.]+) %", vtxt)
    need(m, 'verify output')
    m2 = re.search(r'verify\.unit-lost-rate (\d+)/(\d+) =', vtxt)
    need(m2 and int(m2.group(2)) == NDEL, 'verify denominator is not the delivered count')
    vals = {}
    for c in CAUSES:
        vals[f'rq5.cause.{c}'] = str(V[c])
    vals['rq5.licensed'] = str(LIC)
    vals['rq5.licensed-rate'] = f'{100 * NDEL / LIC:.1f}%'
    vals['rq5.undelivered-licensed'] = str(FIVE)
    for fm in FORMS:
        for col in COLS:
            vals[f'rq5.form.{fm}.{col}'] = str(FT[fm][col])
    for col in ('reverted', 'notplaced', 'held'):
        vals[f'rq5.form.total.{col}'] = str(FT['total'][col])
    vals['verify.rejected-programs.compiler'] = m.group(2)
    vals['verify.unit-lost-rate.compiler'] = f'{100 * int(m.group(3)) / NDEL:.2f}%'
    vals['verify.wholecrate-lost-rate.compiler'] = f'{100 * int(m.group(5)) / NDEL:.1f}%'
    ctx = dict(V=V, FIVE=FIVE, LIC=LIC, NDEL=NDEL, INS=INS, W=W, DEN=DEN, WS=WS, WnS=WnS, SnW=SnW, CZ=CZ, FT=FT, LO=LO,
               LEDGER=LEDGER, rows=rows, verify=m, vtxt=vtxt)
    return vals, ctx


REC = {}
for l in open(f'{HERE}/record-current.md'):
    if l.startswith('| ') and l.count(' | ') >= 5:
        c = l.rstrip('\n').split(' | ')
        REC[c[0][2:].strip()] = (c[1].strip(), c[2].strip())

F3, S = "58'''", "60s'"
PREV = {r['key']: r for r in rd(f'{R141}/staged.tsv')}
CARRIED = [k for k, r in PREV.items() if r['verdict'] in ('carried', 'not-at-58ppp')]
mode = sys.argv[1] if len(sys.argv) > 1 else ''

if mode == 'control':
    vals, _ = compute('58ppp')
    bad = []
    for k, r in PREV.items():
        if k in CARRIED:
            continue
        if vals.get(k) != r['value_58ppp']:
            bad.append((k, vals.get(k), r['value_58ppp']))
    extra = set(vals) - set(PREV)
    now_ne = [k for k, r in PREV.items() if REC.get(k, ('?',))[0] != r['value_58ppp']]
    print(f'control at 58ppp: {len(vals)} computed keys, {len(PREV) - len(CARRIED)} compared with r141 value_58ppp, '
          f'mismatches {len(bad)}, computed but not in r141 {sorted(extra)}; carried/not-at keys {len(CARRIED)}; '
          f'record value != r141 value_58ppp: {len(now_ne)}')
    for b in bad:
        print('  MISMATCH', *b)
    if bad or extra or now_ne:
        raise SystemExit('control failed')
    sys.exit(0)
need(mode == 'stage', 'usage: control | stage')

# ============================================================= 60s' values and causes
vals, X = compute('60sp')
vpp, Y = compute('58ppp')  # the same producers on 58''' (= the control), for the move texts
V, FIVE, LIC, NDEL, INS, DEN = X['V'], X['FIVE'], X['LIC'], X['NDEL'], X['INS'], X['DEN']
rows = X['rows']
kinds = collections.Counter(r['kind'] for r in rows)
BASE = {(r['program'], r['subject_key']): r for r in rd(f'{R141}/out/rq5-rows-58ppp.tsv')}
need(BASE == {(r['program'], r['subject_key']): r for r in rd(f'{HERE}/ctl58ppp/rq5-rows-58ppp.tsv')}, 'base != control row file')
NOW = X['CZ']


def outcomes(C):
    out = {}
    for f in glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv'):
        p = os.path.basename(f).split('.raw-boundary')[0]
        for o in rd(f):
            out[(p, o['subject_key'])] = o
    return out


def deliv(C, tree):
    lo = ledger_only(C) if tree else set()
    return {k: o['delivery'] == 'realized-as-predicted' and k not in lo for k, o in outcomes(C).items()}


OA, OB = outcomes(FRAMES['58ppp']['C']), outcomes(FRAMES['60sp']['C'])
DPP, DPPP = deliv(FRAMES['58ppp']['C'], True), deliv(FRAMES['60sp']['C'], True)
TR = collections.defaultdict(list)
for k in sorted(set(BASE) | set(NOW)):
    b, r = BASE.get(k), NOW.get(k)
    src = b['cause'] if b else ('delivered' if DPP.get(k) else 'outside')
    dst = r['cause'] if r else ('delivered' if DPPP.get(k) else 'outside')
    kd = r['kind'] if r else 'left'
    if src != dst or kd != 'unchanged':
        TR[(src, dst, kd)].append(k)
n_left = sum(len(v) for (s, d, kd), v in TR.items() if kd == 'left')
need(n_left == 43, ('left rows', n_left))
short = lambda k: k[0] + ' ' + re.sub(r'^(src::)+', '', k[1]).replace('src::', '')


def names(keys, cap=40):
    s = sorted(short(k) for k in keys)
    return ', '.join(s[:cap]) + (f' and {len(s) - cap} more' if len(s) > cap else '')


# R956-1 relation
SnW, WnS, WS = X['SnW'], X['WnS'], X['WS']
casc_ihf = sum(1 for k in SnW if NOW[k]['label'] == 'held:into-held-formal')
wns = collections.Counter(NOW[k]['cause'] for k in WnS)
wns_s = ', '.join(f'{c} {wns[c]}' for c in CAUSES if wns.get(c))
need(DEN == 3612 and f'{100 * NDEL / DEN:.2f}' == '75.17', "R956-1 is not main 225's 2,715 / 3,612 = 75.17 %")
need(len(X['W']) == 918, 'W')
LEDN = len(X['LEDGER'])
need(LEDN == 2715 and len(X['LO']) == 0, 'ledger 2,715 / custody 0')

PREFIX = "analysis-fanout r146 (relay 146) group rq5: "
PART = (f"THE PARTITION at {S} by the emitted tree under D6 (R770-1, R775; asserted by build_staged_60sp.py): the six "
        f"causes partition the {INS - NDEL:,} decided-safe rows in scope that the tree does not deliver ({INS:,} - {NDEL:,}; "
        f"the ledger delivers {LEDN:,} too: custody ledger-only 0, tree-only 0, so P9 reads no row); five of them "
        f"(no-safe-form {V['no-safe-form']}, undefined {V['undefined']}, held {V['held']}, form-fact {V['form-fact']}, "
        f"generator {V['generator']}; together {FIVE} = rq5.undelivered-licensed) are licensed but not realized "
        f"({NDEL:,} + {FIVE} = {LIC:,} = rq5.licensed), and side-condition ({V['side-condition']:,}) stands beside them "
        f"({LIC:,} + {V['side-condition']:,} = {INS:,}); rq5.cause.type-system is a seventh key, 0; R956-1 with D6 is "
        f"{NDEL:,} / ({INS:,} - {len(X['W'])}) = {NDEL:,} / {DEN:,} = {100 * NDEL / DEN:.2f} % (= main 225), and its {DEN:,} "
        f"stands {DEN - LIC} above rq5.licensed ({len(SnW)} side-condition rows not withheld (into-held-formal cascades "
        f"{casc_ihf}, the rest class-held cascades and own labels that are not R956-1 holds) - {len(WnS)} withheld rows "
        f"licensed ({wns_s}); W∩S {len(WS)}); row file r146/rq5/out60sp/rq5-rows-60sp.tsv, totals "
        f"r146/rq5/out60sp/totals-b60sp.tsv")
fam = lambda O, k: O[k]['family'] if k in O else '-'
new_out = [k for (s, d, kd), v in TR.items() if kd == 'new' and s == 'outside' for k in v]
new_lost = [k for (s, d, kd), v in TR.items() if kd == 'new' and s == 'delivered' for k in v]
need(len(new_out) + len(new_lost) == kinds['new'], 'new rows')
new_own = [k for k in new_out if fam(OB, k) == 'box']
new_ref = [k for k in new_out if fam(OB, k) != 'box']
need(all(fam(OA, k) == 'raw' for k in new_out), 'a newly decided-safe row was not model Raw at 58ppp')
own_lab = collections.Counter(NOW[k]['label'] for k in new_own)
own_lab_s = ', '.join(f'{l} {n}' for l, n in own_lab.most_common())
own_prog = collections.Counter(k[0] for k in new_own)
own_prog_s = ', '.join(f'{p} {n}' for p, n in own_prog.most_common())
ref_lab = collections.Counter(f"{NOW[k]['label']} ({NOW[k]['cause']})" for k in new_ref)
ref_lab_s = ', '.join(f'{l} {n}' for l, n in ref_lab.most_common())
lost_s = '; '.join(f"{short(k)} ({fam(OA, k)} -> model {fam(OB, k)}, {NOW[k]['label']}, {NOW[k]['cause']})" for k in sorted(new_lost))
left_del = [k for (s, d, kd), v in TR.items() if kd == 'left' and d == 'delivered' for k in v]
left_out = [k for (s, d, kd), v in TR.items() if kd == 'left' and d == 'outside' for k in v]
ld_lab = collections.Counter(BASE[k]['label'] for k in left_del)
ld_s = ', '.join(f'{l} {n}' for l, n in ld_lab.most_common())
lo_lab = collections.Counter(BASE[k]['label'] for k in left_out)
lo_s = ', '.join(f'{l} {n}' for l, n in lo_lab.most_common())
need(all(fam(OB, k) == 'raw' for k in left_out), 'a row that left the decided-safe set is not model Raw at 60sp')
swap_fns = {OB[k]['owner_fn'] for k in new_out + new_lost}
left_swapped = sum(1 for k in left_out if OA[k]['owner_fn'] in swap_fns)
relab = sorted(k for (s, d, kd), v in TR.items() if kd == 'relabelled' for k in v)
relab_s = '; '.join(f"{short(k)} {BASE[k]['label']} -> {NOW[k]['label']} ({BASE[k]['cause']} -> {NOW[k]['cause']}"
                    f"{', P0' if BASE[k]['cause'] == NOW[k]['cause'] else ', P8'})" for k in relab)
need(kinds.get('custody-ledger-only', 0) == 0 and kinds.get('family-changed', 0) == 0, 'kinds')
METHOD = (f"RQ5 row by row at {S} (r141/rq5's audit_rowlevel.py unchanged, rules P0-P9; control: re-run on main/batch58pps39 "
          f"with r141's arguments it reproduces r141/rq5/out's row file, final rows, totals, label map, left list and "
          f"printout byte for byte): base = the {F3} row file of record (r141/rq5/out/rq5-rows-58ppp.tsv, 1,623 rows); census "
          f"main/batch60sp (main 225); rows from rq5_columns.py (docs copy) and rq5_cause_map.py (both byte-identical to "
          f"r141 on batch58pps39); {kinds['unchanged']:,} rows keep the {F3} row-level cause (same program, subject, label, "
          f"family), and every unchanged first-order or into-held-formal row was re-read by its own receipt at {S} "
          f"(check_unchanged.py): 0 read another cause outside P0; {kinds['relabelled']} relabelled rows read by receipt: "
          f"{relab_s}; {kinds['new']} new rows: {len(new_out)} newly decided safe, all model Raw at {F3}: {len(new_own)} now "
          f"model Owning under the Ref > Owning > Raw order (by label {own_lab_s}; by program {own_prog_s}; each read by P8, "
          f"the label default: no absent fact named, R770-1 -> generator) and {len(new_ref)} now model Ref or optional "
          f"through a pair re-break ({ref_lab_s}); {len(new_lost)} delivered at {F3} and not at {S}: {lost_s}; custody "
          f"ledger-only rows 0; {n_left} rows of {F3} left the set: {len(left_del)} delivered at {S} ({ld_s}) and "
          f"{len(left_out)} no longer decided safe (model Raw at {S}: {lo_s}; {left_swapped} of them in a function where "
          f"another subject entered the decided-safe set or left delivery, the re-breaks of main 225 section 0); the "
          f"60-KINDORDER cache's QualifierFacts (streamed, qfacts_stream2.py) equal the S39 cache's slot for slot (59,603), "
          f"so the fatness input is unchanged")


def moves(c):
    parts = []
    for (s, d, kd), v in sorted(TR.items()):
        if d == c and s != c:
            how = {'outside': f'newly decided safe at {S}', 'delivered': f'delivered at {F3} and not at {S}'}.get(s, f'from {s}')
            parts.append(f"+{len(v)} {how}{' (' + kd + ')' if kd not in ('new',) else ''}: {names(v)}")
        elif s == c and d != c:
            how = {'outside': f'no longer decided safe at {S}', 'delivered': f'delivered at {S}'}.get(d, f'to {d}')
            parts.append(f"-{len(v)} {how}{' (' + kd + ')' if kd not in ('left',) else ''}: {names(v)}")
    return '; '.join(parts)


out = []


def add(k, v, cause):
    need(k in REC, 'key not in the record: ' + k)
    now = REC[k][0]
    verdict = 'equal' if now == v else 'differs'
    if verdict == 'differs':
        cause += f"; previously at {F3}: {now}"
    for bad in ('\t', '\n', '|'):
        need(bad not in cause and bad not in v, f'{k}: forbidden character in cause/value')
    out.append((k, now, v, verdict, cause))


for c in CAUSES:
    mv = moves(c)
    why = f"{V[c]:,} ({F3}: {Y['V'][c]:,})" + (': ' + mv if mv else ', every row unchanged')
    add(f'rq5.cause.{c}', vals[f'rq5.cause.{c}'], PREFIX + PART + '; ' + METHOD + '; this key: ' + why)
add('rq5.licensed', vals['rq5.licensed'], PREFIX + PART + '; ' + METHOD + f"; this key: {NDEL:,} + {FIVE} = {LIC:,} = {INS:,} - "
    f"{V['side-condition']:,} ({F3}: {Y['LIC']:,}; the universe grows by {INS - Y['INS']} (decided safe {INS:,} vs "
    f"{Y['INS']:,}: the slots the Ref > Owning > Raw order makes model Owning count as decided safe) and side-condition "
    f"moves by {V['side-condition'] - Y['V']['side-condition']:+d})")
add('rq5.licensed-rate', vals['rq5.licensed-rate'], PREFIX + PART + '; ' + METHOD + f"; this key: {NDEL:,} / {LIC:,} = "
    f"{100 * NDEL / LIC:.2f} % by the tree (= the ledger: custody 0); {F3}: {Y['NDEL']:,} / {Y['LIC']:,} = "
    f"{100 * Y['NDEL'] / Y['LIC']:.2f} %")
add('rq5.undelivered-licensed', vals['rq5.undelivered-licensed'], PREFIX + PART + '; ' + METHOD +
    f"; this key: {LIC:,} - {NDEL:,} = {FIVE} by the tree (= the ledger); {F3}: {Y['FIVE']}")

# forms
FL = forms(f'{HERE}/out60sp/forms-60sp-ledger.out')
FPP = Y['FT']
BOXN = X['FT']['box']['delivered'] + X['FT']['boxslice']['delivered']
need(BOXN == 212, "Box != main 225's 212")
FORMNOTE = ("rq5_forms_tree.py (r141's, unchanged; control: on main/batch58pps39 with --tree-custody and the S39 cache's "
            "streamed fatness file it reproduces r141/rq5/out/forms-58ppp-rowlevel.out, and without the flag "
            "forms-58ppp-ledger.out, byte for byte) with --emitted-form on main/batch60sp, --tree-custody, the d0 fatness "
            "file streamed from the 60-KINDORDER cache (r146/rq5/out60sp/qfacts-60sp.tsv.fat: 56,914 slots, byte-identical "
            "to the S39 cache's and to r133's L01^14u fatfacts-l01p14u.tsv) and the cause column ALIGNED to the row-level "
            "reading (rows = r146/rq5/out60sp/rows-final-b60sp.tsv) -> r146/rq5/out60sp/forms-60sp-rowlevel.out (the ledger "
            f"reading forms-60sp-ledger.out is byte-identical: custody 0): withheld = rq5.cause.side-condition "
            f"{V['side-condition']:,}, licensed = rq5.licensed {LIC:,}, delivered = {NDEL:,} (by the tree), held = {V['held']}, "
            f"decided = {INS:,}; Box delivered + boxslice delivered = {X['FT']['box']['delivered']} + "
            f"{X['FT']['boxslice']['delivered']} = {BOXN} = main 225's Box (box 92, box-slice 21 + opt-box-slice 99); the "
            f"model Owning rows the order adds sit in box / boxslice decided and notplaced (box-param-lend-withheld, "
            f"box-construction-unmappable, unsupported-decl-shape)")
need(FL == X['FT'], 'ledger forms differ from the tree forms with custody 0')
for fm in FORMS:
    for col in COLS:
        k = f'rq5.form.{fm}.{col}'
        n, p = X['FT'][fm][col], FPP[fm][col]
        txt = f"{S} {n}, {F3} {p}" + (f" ({n - p:+d})" if n != p else " (no move)")
        add(k, vals[k], PREFIX + FORMNOTE + '; this key: ' + txt)
for col in ('reverted', 'notplaced', 'held'):
    k = f'rq5.form.total.{col}'
    n, p = X['FT']['total'][col], FPP['total'][col]
    txt = f"{S} {n}, {F3} {p}" + (f" ({n - p:+d})" if n != p else " (no move)")
    if col == 'reverted':
        txt += (" (the 1 = brotli's closure:partition row in BuildAndStoreBlockSwitchEntropyCodes, a planning-time revert "
                "with no compiler diagnostic; brotli BuildAndStoreCommandPrefixCode's E0599 and tulipindicators "
                "smoke::get_array's E0308 of 58''' do not occur, compiler diagnostics 0)")
    add(k, vals[k], PREFIX + FORMNOTE + '; this key: ' + txt)

# verify
vm = X['verify']
VR = ("the rule of analysis-fanout 045 unchanged (r141's verify_tree.py with --tree-custody; control: on main/batch58pps39 "
      "it reproduces r141/rq5/out/verify-batch58ppp.out byte for byte; the record's compiler-rejected-only variant: "
      "programs with raw_boundary_reverted_count > 0 (per-program.kv) that have a compiler-diagnostics row; delivered = by "
      f"the emitted tree); at {S} reverted_count>0 = {{brotli: 1}} (BuildAndStoreBlockSwitchEntropyCodes, closure:partition, "
      "1 ref row); compiler diagnostics: none in any program (main 225: diagnostics 0), so the one revert is planning-time "
      "(no diagnostic) and no program is compiler-rejected; r146/rq5/out60sp/verify-batch60sp.out, reverted-split-60sp.out")
nrej, nrows, nwhole = int(vm.group(2)), int(vm.group(3)), int(vm.group(5))
need((nrej, nrows, nwhole) == (0, 0, 0), ('verify values', nrej, nrows, nwhole))
add('verify.rejected-programs.compiler', vals['verify.rejected-programs.compiler'], PREFIX + VR +
    f"; this key: {nrej} ({F3}: 2, brotli and tulipindicators)")
add('verify.unit-lost-rate.compiler', vals['verify.unit-lost-rate.compiler'], PREFIX + VR +
    f"; this key: {nrows} / {NDEL:,} = {100 * nrows / NDEL:.2f} % (the planning-time revert is not counted under the "
    f"compiler-only rule; {F3}: 6 / 2,678 = 0.22 %, brotli 2 + tulipindicators 4)")
add('verify.wholecrate-lost-rate.compiler', vals['verify.wholecrate-lost-rate.compiler'], PREFIX + VR +
    f"; this key: {nwhole} / {NDEL:,} = {100 * nwhole / NDEL:.2f} % (no compiler-rejected program; {F3}: 949 + 629 = "
    f"1,578 / 2,678 = 58.92 %)")

# carried / not-at
for k in sorted(CARRIED):
    r = PREV[k]
    if r['verdict'] == 'not-at-58ppp':
        out.append((k, REC[k][0], REC[k][0], 'not-at-60sp', "empty pending key in the record (no definition of record at "
                    "this census); not produced"))
    elif k.startswith('rq5.crown.'):
        out.append((k, REC[k][0], REC[k][0], 'carried', f"carried: status {REC[k][1]}, kept for provenance (Rule 5); "
                    "a superseded CROWN-side row that no census re-derives (its input is not the census or the cache)"))
    else:
        out.append((k, REC[k][0], REC[k][0], 'carried', "carried: a frame-of-record key of L01^11 (the L01^11 solve's "
                    "row-level audit), not re-derived at a census; its input (the L01^11 frame) is unchanged by 60s'"))
keys = [o[0] for o in out]
need(sorted(keys) == sorted(PREV), 'key set differs from r141/rq5/staged.tsv')
need(len(set(keys)) == len(keys), 'duplicate key')
with open(f'{HERE}/staged.tsv', 'w') as w:
    w.write('key\tvalue_now\tvalue_60sp\tverdict\tcause\n')
    for r in out:
        for x in r:
            need('\t' not in str(x) and '\n' not in str(x) and '|' not in str(x), 'tab/newline/pipe')
        w.write('\t'.join(str(x) for x in r) + '\n')
vc = collections.Counter(r[3] for r in out)
print('keys', len(out), dict(vc))
for r in out:
    if r[3] == 'differs':
        print(' ', r[0], r[1], '->', r[2])
