#!/usr/bin/env python3
"""r146/trees: staged.tsv -- the tree-derived keys at 60s' (main/batch60sp, head 32d966b9f) beside the record (58''').

Record = r146/record-current.md (docs origin/main:paper/numbers-of-record.md, md5 8371d530 = analysis-fanout 117's
58''' re-seed; parsed into record-rows.json by scratch/parse_record.py, which reproduces r141's parse exactly).

Every producer is r141/trees' copy re-pointed by path only (r141 -> r146; the 58''' side batch58pps39 is now the
CONTROL; the new side batch60sp / ours60sp / *-60sp dirs). The control re-run on batch58pps39 reproduced r141/trees'
58''' outputs byte for byte (notes.md); here every frame-dependent control value must equal r141/trees/staged.tsv's
value_58ppp (= the record), or this script stops (SystemExit).

  pos / uses (Table 4, typed counter T1/T2)  t4/<out>/stage.json                    (t4/build_stage.py)
  decl-uses (Table 5 uses, AS EMITTED)       t5/as-emitted{-60sp,}.out               (t5/as_emitted.py)
  alldecl (Table 4 decls, R945-1)            t4r945{-60sp,}/keys.tsv + the vau fix (brotli population_end, +3)
  decl (Table 5 decls, as emitted, R945-1)   t5r945{-60sp,}/keys.tsv + R947-2 (tulipindicators' 12 twin Box locals)
  decl-twin (Table 5, twin, R945-1)          t5r945{-60sp,}/keys.tsv
  decl-uses-twin                              twin/du-ours{60sp,58pps39}.tsv (decl_uses_twin.py)
  formal.outputs.*                            own{-60sp,}/per-program.tsv             (own_scan.py)
  rq2.wins.decl / rq2.ties.decl              ties/out945-{60sp,58pps39}/ties-decl945.tsv (ties945.py: R945-1 cells)
Frame-independent keys (*.before, *.crown, *.laertes, their totals / medians, rq2.total.decl.{crown,laertes}-rate):
  carried; each recomputed value is printed in the cause."""
import collections, csv, filecmp, json, os, re, statistics
from fractions import Fraction as F

H = 'scratch/analysis-fanout/r146/trees'
R141 = 'scratch/analysis-fanout/r141/trees'
MAIN = 'scratch/main'
csv.field_size_limit(10**9)
recrows = json.load(open(f'{H}/record-rows.json'))
rec = {r['key']: r['value'] for r in recrows}
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
K = lambda p: p.replace('.', '')
pct = lambda a, b: f'{100.0 * a / b:.1f}%'
tsv = lambda f: list(csv.DictReader(open(f), delimiter='\t'))


def need(cond, msg):
    if not cond:
        raise SystemExit(f'STOP: {msg}')


SRC = {
    'NEW': dict(t4='t4/out-ours-60sp', ae='t5/as-emitted-60sp.out', ad='t4r945-60sp', t5='t5r945-60sp',
                du='twin/du-ours60sp.tsv', own='own-60sp', ties='ties/out945-60sp', twin='twin/batch60sp',
                census='main/batch60sp'),
    'CTL': dict(t4='t4/out-ours-58pps39', ae='t5/as-emitted.out', ad='t4r945', t5='t5r945',
                du='twin/du-ours58pps39.tsv', own='own', ties='ties/out945-58pps39', twin='twin/batch58pps39',
                census='main/batch58pps39'),
}
T12 = {('tulipindicators', f'indicators::{k}') for k in (
    'adxr::ti_adxr::adxr', 'cci::ti_cci::sum', 'cvi::ti_cvi::lag', 'hma::ti_hma::buff', 'mass::ti_mass::sum',
    'mfi::ti_mfi::down', 'mfi::ti_mfi::up', 'stoch::ti_stoch::d_sum', 'stoch::ti_stoch::k_sum',
    'stochrsi::ti_stochrsi::rsi', 'ultosc::ti_ultosc::bp_buf', 'ultosc::ti_ultosc::r_buf')}


def values(S):
    v, cite, info = {}, {}, {}
    for r in json.load(open(f"{H}/{S['t4']}/stage.json")):
        if re.match(r'^rq1\.[^.]+\.(pos|uses)\.(delivered|rate)$|^rq2\.wins\.pos$|^rq2\.total\.pos\.as-emitted-rate$',
                    r['key']):
            v[r['key']] = r['value']
            cite[r['key']] = f"r146/trees/{S['t4']}/stage.json (typed counter on {S['census']})"
    # rq2.wins.pos: the programs (exact fractions; brotli against CROWN only, as seed_pos.py)
    pp = {r['program']: r for r in tsv(f"{H}/{S['t4']}/per-program.tsv")}
    wins = []
    for p in PROGS:
        r = pp[p]
        b = int(r['ours.pos.before'])
        o, c = F(int(r['ours.pos.delivered']), b), F(int(r['crown.pos.delivered']), b)
        l = F(0) if p == 'brotli' else F(int(r['laertes.pos.delivered']), int(r['laertes.pos.before']))
        if o > max(c, l):
            wins.append(p)
    need(str(len(wins)) == v['rq2.wins.pos'], f"wins.pos list {wins} vs stage {v['rq2.wins.pos']}")
    info['wins.pos'] = wins
    # decl-uses as emitted
    rates = []
    for l in open(f"{H}/{S['ae']}"):
        c = l.rstrip('\n').split('\t')
        if c[0] == 'program':
            continue
        k = 'total' if c[0] == 'TOTAL' else K(c[0])
        v[f'rq1.{k}.decl-uses.delivered'] = c[6]
        v[f'rq1.{k}.decl-uses.rate'] = c[8]
        for s in ('delivered', 'rate'):
            cite[f'rq1.{k}.decl-uses.{s}'] = (f"r146/trees/{S['ae']} (AS EMITTED: official_raw (twin -) + official "
                                              f"(twin wrapper)) over t5/out/<side>/*/uses.tsv")
        if c[0] != 'TOTAL' and int(c[1]):
            rates.append(100.0 * int(c[6]) / int(c[1]))
    v['rq1.median.decl-uses.rate'] = f'{statistics.median(rates):.1f}%'
    cite['rq1.median.decl-uses.rate'] = f"median of the 19 as-emitted rates (in25 > 0), r146/trees/{S['ae']}"
    # alldecl (R945-1) + the vau fix (checked to recur)
    A = {r['key']: r for r in tsv(f"{H}/{S['ad']}/keys.tsv")}
    ls = [(r['owner'], r['name']) for r in tsv(f"{H}/{S['ad']}/decls/ours-brotli.tsv") if r['join'] == 'last-segment']
    need(sorted(ls) == [(f'enc::{m}::ShannonEntropy', 'population_end')
                        for m in ('bit_cost', 'compress_fragment_two_pass', 'metablock')], f'vau joins {ls}')
    for p in PROGS:
        for r in tsv(f"{H}/{S['ad']}/decls/ours-{p}.tsv"):
            need(r['join'] != 'last-segment' or p == 'brotli', f'last-segment join outside brotli {p} {r}')
    ad = {}
    for p in PROGS:
        num, den = int(A[f'rq1.{K(p)}.alldecl.delivered']['r945']), int(A[f'rq1.{K(p)}.alldecl.delivered']['denominator'])
        if p == 'brotli':
            num += 3
        ad[p] = (num, den)
        v[f'rq1.{K(p)}.alldecl.delivered'] = str(num); v[f'rq1.{K(p)}.alldecl.rate'] = pct(num, den)
    tn, td = sum(a for a, _ in ad.values()), sum(b for _, b in ad.values())
    v['rq1.total.alldecl.delivered'] = str(tn); v['rq1.total.alldecl.rate'] = pct(tn, td)
    v['rq1.median.alldecl.rate'] = f'{statistics.median(100.0 * a / b for a, b in ad.values()):.1f}%'
    for k in [k for k in v if '.alldecl.' in k]:
        cite[k] = (f"r146/trees/{S['ad']}/keys.tsv (alldecl945.py on {S['t4']}/ours; R945-1)"
                   + (' + the vau correction +3 (brotli enc::{bit_cost,compress_fragment_two_pass,metablock}::'
                      'ShannonEntropy::population_end: still the only last-segment joins, joined to enc::encode\'s raw '
                      'one; re-typed to usize in the emitted tree)' if ('brotli' in k or 'total' in k or 'median' in k)
                      else ''))
    # decl / decl-twin (R945-1) + R947-2 (re-derived; must be exactly the 12 tulipindicators keys)
    D = {r['key']: r for r in tsv(f"{H}/{S['t5']}/keys.tsv")}
    twelve = set()
    for p in PROGS:
        cls = json.load(open(f"{H}/{S['t5']}/per-key/ours-{p}.json"))
        safe = {k for k, x in cls.items() if x[1] == 'safe-form' or x[1].startswith('shape:')}
        w = {r['key'] for r in tsv(f"{H}/{S['twin']}/{p}.walker-slots.tsv") if r['walker'] != 'none'}
        twelve |= {(p, k) for k in safe - w}
    need(twelve == T12, f'R947-2 set moved: {sorted(twelve ^ T12)}')
    dm, tw = {}, {}
    for p in PROGS:
        n, b = int(D[f'rq1.{K(p)}.decl.delivered']['R945-1']), int(D[f'rq1.{K(p)}.decl.delivered']['denominator'])
        if p == 'tulipindicators':
            n -= 12
        dm[p] = (n, b)
        v[f'rq1.{K(p)}.decl.delivered'] = str(n); v[f'rq1.{K(p)}.decl.rate'] = pct(n, b)
        t = int(D[f'rq1.{K(p)}.decl-twin.rate']['numerator']); tw[p] = (t, b)
        v[f'rq1.{K(p)}.decl-twin.rate'] = pct(t, b)
    dn, db = sum(a for a, _ in dm.values()), sum(b for _, b in dm.values())
    v['rq1.total.decl.delivered'] = str(dn); v['rq1.total.decl.rate'] = pct(dn, db)
    v['rq1.median.decl.rate'] = f'{statistics.median(100.0 * a / b for a, b in dm.values()):.1f}%'
    tn = sum(a for a, _ in tw.values())
    v['rq1.total.decl-twin.rate'] = pct(tn, db); v['rq2.total.decl.twin-rate'] = pct(tn, db)
    v['rq1.median.decl-twin.rate'] = f'{statistics.median(100.0 * a / b for a, b in tw.values()):.1f}%'
    info['decl.total'] = (dn, db); info['decl-twin.total'] = tn
    for k in [k for k in v if re.search(r'\.decl(-twin)?\.|decl\.twin-rate', k)]:
        cite[k] = (f"r146/trees/{S['t5']}/keys.tsv (r945.py/compute.py on t5/out/<side>; R945-1)"
                   + (' + R947-2 (tulipindicators as emitted: minus the 12 twin Box locals; re-derived: R945-1 '
                      'pointer-typed safe forms minus the strict walker\'s as-emitted slots = exactly the 12 keys of '
                      '56 / 58 / 58\'\' / 58\'\'\' and again at 60s\')' if re.search(r'tulipindicators\.decl\.|total\.decl\.|median\.decl\.', k) else ''))
    # decl-uses-twin
    for c in [l.rstrip('\n').split('\t') for l in open(f"{H}/{S['du']}")][1:]:
        if c[0] == 'TOTAL':
            v['rq1.total.decl-uses-twin.rate'] = c[6]
        elif c[0].startswith('MEDIAN'):
            v['rq1.median.decl-uses-twin.rate'] = f"{float(c[1].split()[1]):.1f}%"
        else:
            v[f'rq1.{K(c[0])}.decl-uses-twin.rate'] = c[6]
    for k in [k for k in v if 'decl-uses-twin' in k]:
        cite[k] = (f"r146/trees/{S['du']} (decl_uses_twin.py over t5/out; rate = (in25 - sum official_raw) / in25)")
    # formal.outputs
    own = tsv(f"{H}/{S['own']}/per-program.tsv")
    no = sum(r['owning'] == 'yes' for r in own)
    v['formal.outputs.owning'] = str(no); v['formal.outputs.non-owning'] = str(len(own) - no)
    info['owning'] = [r['program'] for r in own if r['owning'] == 'yes']
    info['owning.brotli'] = [r['owning_decls_typed'] for r in own if r['program'] == 'brotli'][0]
    for k in ('formal.outputs.owning', 'formal.outputs.non-owning'):
        cite[k] = (f"r146/trees/{S['own']}/per-program.tsv (own_scan.py on {S['census']}/emitted-trees + "
                   f"{S['t4']} positions.tsv; typed and text readings agree 20/20)")
    # wins / ties (R945-1)
    for r in tsv(f"{H}/{S['ties']}/ties-decl945.tsv"):
        if r['variant'] == 'as-emitted':
            v['rq2.wins.decl'], v['rq2.ties.decl'] = r['wins'], r['ties']
            info['wins.decl'], info['ties.decl'] = r['win_programs'], r['tie_programs']
        if r['variant'] == 'twin':
            info['twin.wins'] = r['wins']
        if r['variant'] == 'as-emitted-no-R947-2':
            info['noR9472.wins'] = r['wins']
    cite['rq2.wins.decl'] = (f"r146/trees/{S['ties']}/ties-decl945.tsv (ties945.py over {S['t5']}/per-program.json: "
                             f"R945-1 Table 5 cells, ours as emitted with R947-2, exact fractions): strictly above "
                             f"max(CROWN, Laertes): {info['wins.decl'].replace(',', ', ')}")
    cite['rq2.ties.decl'] = (f"r146/trees/{S['ties']}/ties-decl945.tsv (as rq2.wins.decl): equal to max(CROWN, "
                             f"Laertes): {info['ties.decl'].replace(',', ', ')}")
    # twin vs census ledger (the join)
    info['twin.summary'] = json.load(open(f"{H}/{S['twin']}/summary.json"))
    return v, cite, info


NEW, citeN, infoN = values(SRC['NEW'])
CTL, citeC, infoC = values(SRC['CTL'])


def frame_independent(t4, t5side, r118, ad, t5):
    fi = {}
    for f in (f'{t4}/stage.json', f't5/{t5side}-stage.json', f'{r118}/stage.json'):
        for r in json.load(open(f'{H}/{f}')):
            fi[r['key']] = r['value']
    for r in tsv(f'{H}/{ad}/keys.tsv'):
        if re.match(r'^rq2\.', r['key']):
            fi[r['key']] = r['r945']
    for r in tsv(f'{H}/{t5}/keys.tsv'):
        if re.match(r'^rq2\.|.*\.decl\.before$', r['key']):
            fi[r['key']] = r['R945-1']
    return fi


fi = frame_independent('t4/out-ours-60sp', 'ours60sp', 'r118/b60sp', 't4r945-60sp', 't5r945-60sp')
fic = frame_independent('t4/out-ours-58pps39', 'ours58pps39', 'r118/b58pps39', 't4r945', 't5r945')

# ---- the key set and the control
GROUP = re.compile(r'^rq1\.[^.]+\.(pos|uses|decl-uses|alldecl|decl|decl-twin|decl-uses-twin)\.(before|delivered|rate)$'
                   r'|^rq2\.[^.]+\.(pos|uses|decl-uses|alldecl|decl)\.(crown|laertes|crown-rate|laertes-rate|twin-rate|as-emitted-rate)$'
                   r'|^rq2\.wins\.pos$|^formal\.outputs\.(owning|non-owning)$|^rq2\.(wins|ties)\.decl$')
FI = re.compile(r'\.before$|\.crown$|\.laertes$|crown-rate$|laertes-rate$')
r141 = tsv(f'{R141}/staged.tsv')
keys = [r['key'] for r in r141]
need(keys == [r['key'] for r in recrows if GROUP.match(r['key'])], "the key set is not r141/trees/staged.tsv's")
v58ppp = {r['key']: r['value_58ppp'] for r in r141}
need(all(rec[k] == v58ppp[k] for k in keys), 'the record copy does not hold 58\'\'\' (r141 value_58ppp) on every key')
ctl_bad = [(k, v58ppp[k], CTL.get(k)) for k in keys if not FI.search(k) and CTL.get(k) != v58ppp[k]]
need(not ctl_bad, f'control mismatch {ctl_bad}')
fi_bad = [(k, fic.get(k), fi.get(k)) for k in keys if FI.search(k) and fic.get(k) != fi.get(k)]
need(not fi_bad, f'a frame-independent key moved between the control and 60s\' {fi_bad}')
missing = [k for k in keys if not FI.search(k) and k not in NEW]
need(not missing, f'frame-dependent keys without a producer {missing}')
need(infoC['twin.summary']['twin_census_only'] == 0 and infoC['twin.summary']['twin_walker_only'] == 0, 'ctl twin join')
need(infoN['twin.summary']['twin_census_only'] == 0 and infoN['twin.summary']['twin_walker_only'] == 0, '60sp twin join')

# ---- which emitted trees moved (the diff -rq, in Python)
def tree_files(root):
    out = set()
    for dp, _, fs in os.walk(root):
        for f in fs:
            out.add(os.path.relpath(os.path.join(dp, f), root))
    return out


A_T, B_T = f'{MAIN}/batch58pps39/emitted-trees', f'{MAIN}/batch60sp/emitted-trees'
fa, fb = tree_files(A_T), tree_files(B_T)
need(fa == fb, f'emitted tree file sets differ: {sorted(fa ^ fb)[:5]}')
moved_files = sorted(f for f in fa if not filecmp.cmp(f'{A_T}/{f}', f'{B_T}/{f}', shallow=False))
TREE_MOVED = sorted({f.split('/')[0] for f in moved_files})
need(TREE_MOVED == ['brotli', 'heman', 'libzahl', 'tulipindicators'], f'trees moved: {moved_files}')

# ---- identity diff 58''' -> 60s' (main's census_by_identity.py, run into work/) and custody
idd = collections.defaultdict(lambda: collections.defaultdict(set))
for r in tsv(f'{H}/work/idd-60sp-vs-58pps39.tsv'):
    idd[r['program']][r['change']].add(r['subject'].replace('src::', ''))
need(sum(len(x['gained']) for x in idd.values()) == 39 and sum(len(x['lost']) for x in idd.values()) == 6,
     'ledger identity diff is not +39 / -6')
need('ledger-only identities named: 4' in open(f'{MAIN}/batch58pps39-custody.txt').read(), '58\'\'\' custody receipt')
c60 = open(f'{MAIN}/batch60sp-custody.txt').read()
need('ledger-only (counted, raw in the tree): 0' in c60 and 'tree-only (delivered in the tree, not counted): 0' in c60
     and 'count by the emitted tree: 2715' in c60, '60s\' custody receipt')
CUSTODY4 = {'fuzzer::main_0::argv', 'fuzzer::main_0::info_0', 'smoke::test_ind_name::info', 'smoke::test_ind_name::s'}
IH = lambda f: {f'enc::encode::InitializeH{h}::{x}' for h in (2, 4, 5, 40, 41, 42) for x in ('params', 'self_0')}
SPL = lambda f: {f'enc::metablock::{s}::{x}' for s in ('InitBlockSplitterDistance', 'InitContextBlockSplitter')
                 for x in ('histograms', 'm', 'new_array', 'new_array_0')}
EXPECT = {
    'brotli': (IH(0) | SPL(0) | {'enc::block_splitter::HistogramAddHistogramDistance::self_0',
                                 'enc::block_splitter::HistogramAddHistogramLiteral::v',
                                 'enc::cluster::HistogramAddHistogramCommand::v',
                                 'enc::compress_fragment_two_pass::BuildAndStoreCommandPrefixCode::bits',
                                 'enc::metablock::InitBlockSplitterCommand::histograms'},
               {'enc::block_splitter::HistogramAddHistogramDistance::v', 'enc::block_splitter::HistogramAddHistogramLiteral::self_0',
                'enc::cluster::HistogramAddHistogramCommand::self_0', 'enc::encode::GetHashTable::table_size',
                'enc::metablock::InitBlockSplitterCommand::self_0'}),
    'heman': ({f'kazmath::{m}' for m in ('aabb2::kmAABB2Initialize::pBox', 'aabb3::kmAABB3Initialize::pBox',
                                          'mat3::kmMat3Multiply::pOut', 'mat3::kmMat3Transpose::pOut',
                                          'plane::kmPlaneFromPoints::pOut', 'quaternion::kmQuaternionMultiply::pOut',
                                          'vec2::kmVec2MidPointBetween::pOut', 'vec3::kmVec3TransformCoord::pOut',
                                          'quaternion::kmQuaternionToAxisAngle::pAngle')},
              {'kazmath::quaternion::kmQuaternionToAxisAngle::pIn'}),
    'libzahl': ({'zsplit::zsplit::low'}, set()),
    'tulipindicators': ({'indicators_index::ti_find_indicator::name', 'smoke::get_array::line', 'smoke::get_array::num',
                         'smoke::get_array::s'}, set()),
}
need(set(idd) == set(EXPECT), f'programs with identity moves {sorted(idd)}')
for p, (g, l) in EXPECT.items():
    need(idd[p]['gained'] == g and idd[p]['lost'] == l, f'{p} identity sets moved: {idd[p]}')

# ---- the measured diffs (work/diffs.py, work/decl_diffs.py over the counter tables)
DF = json.load(open(f'{H}/work/diffs.json'))
DD = json.load(open(f'{H}/work/decl_diffs.json'))
need({p for p in DF if any(DF[p][k] for k in ('to_safe', 'to_raw', 'uses', 'decl_uses'))} == set(TREE_MOVED),
     'counter tables moved outside the four trees')
need(set(DD) == set(TREE_MOVED), 'declaration tables moved outside the four trees')
POSN = {p: len(DF[p]['to_safe']) - len(DF[p]['to_raw']) for p in TREE_MOVED}
need(POSN == {'brotli': 20, 'heman': 16, 'libzahl': 1, 'tulipindicators': 9}, f'position moves {POSN}')
for p in TREE_MOVED:
    need(int(NEW[f'rq1.{K(p)}.pos.delivered']) - int(CTL[f'rq1.{K(p)}.pos.delivered']) == POSN[p], f'{p} pos vs table')
    need(int(NEW[f'rq1.{K(p)}.uses.delivered']) - int(CTL[f'rq1.{K(p)}.uses.delivered']) == -DF[p]['uses_net'], f'{p} uses')
    need(int(NEW[f'rq1.{K(p)}.decl-uses.delivered']) - int(CTL[f'rq1.{K(p)}.decl-uses.delivered']) == -DF[p]['decl_uses_net'],
         f'{p} decl-uses')
tul = {x.split(' ')[1] for x in DF['tulipindicators']['to_safe']}
need(tul == {'smoke::get_array::line', 'smoke::get_array::num', 'smoke::get_array::s', 'indicators_index::ti_find_indicator::name',
             'fuzzer::main_0::argv', 'fuzzer::main_0::info_0', 'smoke::test_ind_name::info', 'smoke::test_ind_name::s',
             'smoke::test_ind_name::answers'}, f'tulipindicators positions {tul}')
need(sorted(x.split(' ')[1] for x in DF['heman']['to_safe'] if x.startswith('return')) ==
     sorted(f'kazmath::{m}::_0' for m in ('aabb2::kmAABB2Initialize', 'aabb3::kmAABB3Initialize', 'mat3::kmMat3Multiply',
                                          'mat3::kmMat3Transpose', 'plane::kmPlaneFromPoints', 'quaternion::kmQuaternionMultiply',
                                          'vec2::kmVec2MidPointBetween', 'vec3::kmVec3TransformCoord')), 'heman returns')

WHY = {
    'brotli': ("brotli +25 / -5 by identity vs 58''' (the ledger, = the tree): gained InitializeH{2, 4, 5, 40, 41, 42}::"
               "{params, self_0} 12 (held at 58''' as missing-required-site, the six functions reverted), "
               "InitBlockSplitterDistance and InitContextBlockSplitter::{histograms, m, new_array, new_array_0} 8 "
               "(seam-site-overlap at 58''', the two functions reverted; new_array / new_array_0 now Option<Box<[T]>>), "
               "the pair re-breaks HistogramAddHistogramDistance::self_0, HistogramAddHistogramLiteral::v, "
               "HistogramAddHistogramCommand::v and InitBlockSplitterCommand::histograms 4 (kind-raw at 58'''), "
               "BuildAndStoreCommandPrefixCode::bits (its function verify-reverted at 58''', a slice now); lost "
               "HistogramAddHistogramDistance::v, HistogramAddHistogramLiteral::self_0, HistogramAddHistogramCommand::"
               "self_0 and GetHashTable::table_size (box-param-lend-withheld: the A9 lend withheld) and "
               "InitBlockSplitterCommand::self_0 (kind-raw); brotli's function reverts 44 -> 35 (the nine above)"),
    'heman': ("heman +9 / -1 by identity vs 58''' (the ledger, = the tree): gained the eight Box formals "
              "kmAABB2Initialize::pBox, kmAABB3Initialize::pBox, kmMat3Multiply::pOut, kmMat3Transpose::pOut, "
              "kmPlaneFromPoints::pOut, kmQuaternionMultiply::pOut, kmVec2MidPointBetween::pOut, "
              "kmVec3TransformCoord::pOut (box-param-reseat, Option<Box<T>>, kind-raw at 58''') and "
              "kmQuaternionToAxisAngle::pAngle; lost kmQuaternionToAxisAngle::pIn (box-param-lend-withheld)"),
    'libzahl': ("libzahl +1 / -0 by identity vs 58''' (the ledger, = the tree): zsplit::low (&mut; held:into-held-formal "
                "at 58''', zmul's function revert gone: libzahl's reverts 15 -> 14); zswap stays a: &mut, b raw"),
    'tulipindicators': ("tulipindicators +8 / -0 vs 58''' BY THE EMITTED TREE (the ledger reads +4): "
                        "ti_find_indicator::name and smoke::get_array::{line, num, s}, whose two functions the compile "
                        "check reverted at 58''' (ti_find_indicator by closure, get_array verify-reverted; no revert "
                        "at 60s'), and the four custody rows fuzzer::main_0::{argv, info_0}, smoke::test_ind_name::"
                        "{info, s} that 58''' counted in the ledger but kept raw in the tree, now delivered in the "
                        "tree (custody ledger-only 4 -> 0)"),
}
ALL = '; '.join(WHY[p] for p in TREE_MOVED)
SRCS = ("identities: main/census_by_identity.py batch58pps39 -> batch60sp, r146/trees/work/idd-60sp-vs-58pps39.tsv; "
        "custody main/batch{58pps39,60sp}-custody.txt; 60s' = 32d966b9f, the Ref > Owning > Raw order with every A9 "
        "reference lend withheld, era-5c's 60-KINDORDER cache")
PK = {K(p): p for p in PROGS}


def fmtu(d, n):
    items = sorted(d.items(), key=lambda kv: kv[1])
    s = lambda k: k.replace('src::', '').rpartition('::')[2]
    neg = [f'{s(k)} {v:+d}' for k, v in items if v < 0]
    pos = [f'{s(k)} {v:+d}' for k, v in items if v > 0]
    return ', '.join(neg[:n] + (['...'] if len(neg) > n else [])), ', '.join(pos[:n] + (['...'] if len(pos) > n else []))


def uses_text(p, fam):
    col, net = ('uses', 'uses_net') if fam == 'uses' else ('decl_uses', 'decl_uses_net')
    d = DF[p][col]
    if not d:
        return ''
    neg, pos = fmtu(d, 8)
    what = "raw-pointer uses" if fam == 'uses' else "raw uses on CROWN's population"
    t = f"{p}'s {what} move {DF[p][net]:+d} net (per-function uses.tsv diff, t{'4' if fam == 'uses' else '5'}): "
    t += ' '.join(x for x in (neg and f'falling {neg};', pos and f'rising {pos};') if x)
    return t + ' '


EXTRA = {
    ('brotli', 'uses'): ("brotli's rises are the lost formals' functions (InitBlockSplitterCommand +16, its self_0 now raw) "
                         "and the callers that now bridge (HasherSetup +6: the six InitializeH* calls pass `&*params`, one "
                         "dereference of a raw root each); the fall includes the twin wrapper __crat_raw_EncodeWindowBits, "
                         "no longer emitted (-10); "),
    ('brotli', 'decl-uses'): ("brotli's CROWN-population rises include HasherSetup +6 (the six InitializeH* calls pass "
                              "`&*params`) and InitBlockSplitterCommand +13 (its self_0 now raw); "),
    ('heman', 'pos'): ("heman's positions move +16 beside its +8 net identities: the eight Box formals' functions now "
                       "also return Option<Box<T>> (kmAABB2Initialize, kmAABB3Initialize, kmMat3Multiply, kmMat3Transpose, "
                       "kmPlaneFromPoints, kmQuaternionMultiply, kmVec2MidPointBetween, kmVec3TransformCoord: eight return "
                       "positions that are not census subjects); "),
    ('heman', 'alldecl'): ("heman's declarations move +16: 9 formals, the eight Option<Box<T>> returns, less pIn; "),
    ('heman', 'decl'): ("heman's Table 5 moves +9 (the nine gained formals are in CROWN's universe; pIn is not); "),
    ('tulipindicators', 'pos'): ("tulipindicators' positions move +9: the 8 identities and the array local "
                                 "smoke::test_ind_name::answers ([*mut f64; 10] -> [Option<Box<[f64]>>; 10], not a census "
                                 "subject); none is in CROWN's 134-slot universe, so Table 5 (decl, decl-uses) does not "
                                 "move; "),
    ('tulipindicators', 'alldecl'): ("tulipindicators' declarations move +9: the 8 identities and the array local "
                                     "smoke::test_ind_name::answers; "),
    ('libzahl', 'uses'): ("libzahl's raw-pointer uses RISE by 2 although zsplit::low is gained: the callers now bridge "
                          "`&mut *low.as_mut_ptr()` (zmul x2, zsqr x1, one dereference of a raw root each) against zsplit "
                          "-1; written as measured, never clamped; "),
    ('brotli', 'decl'): ("brotli's Table 5 moves +12 / -4 on CROWN's universe (the InitializeH* self_0 six, "
                         "HistogramAddHistogramDistance::self_0, the four histograms / m of the splitters and "
                         "InitBlockSplitterCommand::histograms in; HistogramAddHistogramLiteral::self_0, HistogramAddHistogramCommand::"
                         "self_0, GetHashTable::table_size, InitBlockSplitterCommand::self_0 out); "),
}


def extra(p, fam):
    fam = {'decl-uses-twin': 'decl-uses', 'decl-twin': 'decl'}.get(fam, fam)
    ps = [p] if p in PK.values() else TREE_MOVED
    t = ''
    for q in ps:
        if fam in ('uses', 'decl-uses'):
            t += uses_text(q, fam)
        t += EXTRA.get((q, fam), '')
    return t


need(infoC['twin.wins'] == infoN['twin.wins'] and infoC['noR9472.wins'] == infoN['noR9472.wins'], 'twin / no-R947-2 wins moved')
strict = {r['key']: r for r in tsv(f'{H}/ties/out-batch60sp/ties-decl.tsv')}
strictc = {r['key']: r for r in tsv(f'{H}/ties/out-batch58pps39/ties-decl.tsv')}
need(strict['rq2.wins.decl']['value'] == strictc['rq2.wins.decl']['value'] == '5'
     and strict['rq2.ties.decl']['value'] == strictc['rq2.ties.decl']['value'] == '3', 'strict ties_decl moved')
SPECIAL_EQ = {
    'rq2.wins.pos': (f"unchanged at 60s': the programs whose position rate is strictly the highest of the three "
                     f"(brotli against CROWN only), exact fractions over t4 per-program.tsv: "
                     f"{', '.join(infoN['wins.pos'])}; ties: none; none of the four moved programs crosses (brotli "
                     f"{NEW['rq1.brotli.pos.rate']} vs CROWN, heman {NEW['rq1.heman.pos.rate']}, libzahl "
                     f"{NEW['rq1.libzahl.pos.rate']}, tulipindicators {NEW['rq1.tulipindicators.pos.rate']} stay on the "
                     f"same side); "),
    'formal.outputs.owning': (f"unchanged at 60s': the same ten owning programs ({', '.join(infoN['owning'])}); brotli's "
                              f"owning-typed declarations {infoC['owning.brotli']} -> {infoN['owning.brotli']} (the four "
                              f"splitter new_array locals, Option<Box<[T]>>), heman's eight Box formals; no program "
                              f"crosses; "),
    'formal.outputs.non-owning': "unchanged at 60s' (see formal.outputs.owning); ",
    'rq2.wins.decl': (f"unchanged at 60s' under R945-1: brotli {NEW['rq1.brotli.decl.delivered']}/846 = "
                      f"{NEW['rq1.brotli.decl.rate']} and heman {NEW['rq1.heman.decl.delivered']}/360 = "
                      f"{NEW['rq1.heman.decl.rate']} rise but were already wins; libzahl rises to "
                      f"{NEW['rq1.libzahl.decl.rate']} and stays below CROWN; no tie program moves; twin reading "
                      f"{infoN['twin.wins']}, without R947-2 {infoN['noR9472.wins']} (both as at 58'''); the strict "
                      f"ties_decl.py at 60s' gives 5 (ties/out-batch60sp, as at 58'''); "),
    'rq2.ties.decl': "unchanged at 60s' under R945-1 (no tie program moved); the strict ties_decl.py gives 3 (as at 58'''); ",
}
n = collections.Counter()
out = ['key\tvalue_now\tvalue_60sp\tverdict\tcause']
for k in keys:
    v = rec[k]
    if FI.search(k):
        r = fi.get(k)
        note = ("carried: frame-independent (input / CROWN / Laertes side; the same counter outputs, input trees and "
                "artifact at 60s', only our emitted trees moved); "
                + (f"recomputed at 60s' = {r} (the same at the 58''' control)"
                   + ('' if r == v else ' over the programs with a Laertes tree; the record value is R891-1\'s '
                                        '(analysis-fanout 097, relay 120: brotli counted at 0.0 over the twenty, as '
                                        'CROWN\'s Table 2 dagger); the same at 58\'\'\'')
                   if r is not None else 'not recomputed by these producers'))
        out.append('\t'.join([k, v, v, 'carried', note])); n['carried'] += 1
        continue
    b = NEW[k]
    verdict = 'equal' if b == v else 'differs'
    n[verdict] += 1
    seg, fam = k.split('.')[1], k.split('.')[2] if k.count('.') >= 2 else ''
    if k in SPECIAL_EQ:
        need(verdict == 'equal', f'{k} moved but its cause text says unchanged')
        cause = SPECIAL_EQ[k] + citeN[k]
    elif verdict == 'equal':
        cause = citeN[k]
        if seg == 'tulipindicators' and fam in ('decl', 'decl-twin', 'decl-uses', 'decl-uses-twin'):
            cause = ("equal at 60s' although tulipindicators' tree moved (+8 by the tree): none of the gained "
                     "bindings is in CROWN's 134-slot universe; ") + cause
    else:
        cause = (WHY[PK[seg]] if seg in PK else 'aggregate of the per-program moves: ' + ALL) \
            + ' (' + SRCS + '); ' + extra(PK.get(seg, seg), fam) + 'value from ' + citeN[k] \
            + f"; previously at 58''': {v}"
    for ch in ('\t', '\n', '|'):
        need(ch not in cause, f'forbidden character in the cause of {k}')
    need('58\'\'\' = ' not in cause[:12], 'frame header')
    out.append('\t'.join([k, v, b, verdict, cause]))
need(all(r.split('\t')[3] != 'differs' or r.endswith(f"previously at 58''': {r.split(chr(9))[1]}") for r in out[1:]),
     'a differs row does not end with its previous value')
open(f'{H}/staged.tsv', 'w').write('\n'.join(out) + '\n')
json.dump(NEW, open(f'{H}/v60sp.json', 'w'), indent=1)
json.dump(CTL, open(f'{H}/vctl58ppp.json', 'w'), indent=1)
print(len(keys), dict(n))
print('control (58\'\'\') == r141 value_58ppp on every frame-dependent key; carried keys equal at control and 60s\'')
print('trees moved:', TREE_MOVED, moved_files)
print('twin vs census ledger at 60s\':', infoN['twin.summary'])
for k in keys:
    if k in NEW and NEW[k] != rec[k]:
        print(f'  {k}: {rec[k]} -> {NEW[k]}')
