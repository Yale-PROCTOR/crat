#!/usr/bin/env python3
"""r146 / conf -- analysis-fanout relay 146: the conformance group's keys staged at 60s' (head 32d966b9f, census
main/batch60sp, main 225; cache era-5c's 60-KINDORDER era5c-r215-kindorder). STAGE ONLY: writes staged.tsv here.

Producers = r141/conf's, re-pointed (scripts/): run_py.sh, run_stream.sh, run_x.sh (+ window.sh), ec3_keys.py, sib.py,
ec1/ec1_ident.py (batches from argv), ec1/ec1_variants.py, guarded.py, conf_keys.py (a copy in each g2 dir), tools/ec4_rows.py.
Outputs: ctl/  = the producers on main/batch58pps39 with the S39 cache (THE CONTROL)
         60sp/ = the producers on main/batch60sp with the 60-KINDORDER cache
The control: values(ctl) must equal r141/conf/staged.tsv's value_58ppp on all 34 keys (and the receipts byte for byte).
Every check fails closed through raise SystemExit (no assert)."""
import csv, glob, hashlib, json, os, re, subprocess

W = 'scratch/analysis-fanout/r146/conf'
R141 = W + '/r141-copy'
REC = W + '/record-base.md'
M = 'scratch/main'
DOCS = 'crat/docs'


def die(m):
    raise SystemExit('build_staged r146/conf: FAIL: ' + m)


def need(c, m):
    if not c:
        die(m)


def same(a, b):
    return open(a, 'rb').read() == open(b, 'rb').read()


def receipts(path, cond):
    rows = {}
    for line in open(path):
        if not line.startswith('conformance ' + cond + ' '):
            continue
        kv = dict(t.split('=', 1) for t in line.split()[2:] if '=' in t)
        need(kv['program'] not in rows, 'duplicate %s %s in %s' % (cond, kv['program'], path))
        rows[kv['program']] = kv
    need(len(rows) > 0, 'no %s rows in %s' % (cond, path))
    return rows


def S(rows, k):
    return sum(int(r.get(k, 0) or 0) for r in rows.values())


def byprog(rows, k):
    return ', '.join('%s %s' % (p, r[k]) for p, r in sorted(rows.items(), key=lambda x: (-int(x[1][k]), x[0])) if int(r[k]))


def n(v):
    return format(v, ',')


# ---------------------------------------------------------------- the record base
raw = open(REC, 'rb').read()
need(hashlib.md5(raw).hexdigest().startswith('8371d530'), 'record base md5 is not 8371d530')
ROW = re.compile(r'^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) \| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$')
rec, order = {}, []
for l in raw.decode('utf-8').split('\n'):
    m = ROW.match(l)
    if m and not l.startswith('| key |'):
        k = m.group('key')
        need(k not in rec, 'duplicate record key ' + k)
        rec[k] = m.groupdict()
        order.append(k)
r141 = {r['key']: r for r in csv.DictReader(open(R141 + '/staged.tsv'), delimiter='\t')}
need(len(r141) == 34, 'r141 staged not 34 keys')
VKEYS = ['ec4.validator.certified', 'ec4.validator.viol', 'ec4.validator.check-sat', 'ec4.validator.digest-match',
         'ec4.validator.certified.at-58pp', 'ec4.validator.viol.at-58pp', 'ec4.validator.check-sat.at-58pp',
         'ec4.validator.digest-match.at-58pp']
need(all(k in rec for k in VKEYS), 'validator keys missing from the record')
need(sorted(k for k in order if k.startswith('ec4.validator')) == sorted(VKEYS), 'the record has other validator keys')
need(all(k in rec for k in r141), 'an r141 key is not in the record')
KEYS = [k for k in order if k in r141 or k in VKEYS]
need(len(KEYS) == 42, '%d keys, not 42' % len(KEYS))

# ---------------------------------------------------------------- tools and controls
for f in os.listdir(W + '/tools'):
    if f.endswith('.py') and f != 'resid_scan.py':
        need(same(W + '/tools/' + f, R141 + '/tools/' + f), 'tool differs from r141: ' + f)
        dp = subprocess.run(['git', '-C', DOCS, 'show', 'origin/main:agents/tools/conformance/' + f], capture_output=True).stdout
        need(dp == open(W + '/tools/' + f, 'rb').read(), 'tool differs from docs origin/main: ' + f)
need(same(W + '/tools/resid_scan.py', R141 + '/work/resid_scan.py'), 'resid_scan')
for f in glob.glob(W + '/ctl/**/*.err', recursive=True) + glob.glob(W + '/60sp/**/*.err', recursive=True):
    need(os.path.getsize(f) == 0, 'non-empty stderr: ' + f)
for f in glob.glob(W + '/ctl/conf/*.exit') + glob.glob(W + '/60sp/conf/*.exit'):
    need(open(f).read().startswith('exit=0 '), 'stream exit: ' + f)
for lab in ('ctl', '60sp'):
    need(open(W + '/%s/x/rc.txt' % lab).read() == 'c2b rc=0\nx rc=0\n', 'x rc ' + lab)
# CONTROL, receipts byte for byte against r141's own
CTLPAIRS = [('ctl/conf/' + f, 'conf-s39/' + f) for f in ('c1.txt', 'c2.txt', 'c3.txt', 'c3-table.tsv', 'c4.txt',
                                                          'c4-receipts.txt', 'control-final-replay.tsv')]
CTLPAIRS += [('ctl/x/x.txt', 'x58ppp/x.txt'), ('ctl/x/c2b.txt', 'x58ppp/c2b.txt'), ('ctl/ec4/ec4.txt', 'ec4-58ppp/ec4.txt'),
             ('ctl/ec3/ec3.txt', 'ec3/ec3-s39.txt'), ('ctl/ec3/perm-t2.txt', 'ec3/perm-s39-t2.txt'),
             ('ctl/ec1/ec1_ident.out', 'ec1/ec1_ident.out'), ('ctl/ec1/ec1_variants.out', 'ec1/ec1_variants.out'),
             ('ctl/decline/s39.tsv', 'decline/s39.tsv'), ('ctl/g2/departures-batch58pps39.tsv', 'g2/departures-batch58pps39.tsv')]
for a, b in CTLPAIRS:
    need(same(W + '/' + a, R141 + '/' + b), 'control receipt differs: ' + a)
need([l for l in open(W + '/ctl/g2/keys.tsv')] ==
     [l.replace('scratch/analysis-fanout/r141/conf/conf-s39', W + '/ctl/conf') for l in open(R141 + '/g2/keys-s39.tsv')],
     'control conf_keys differs (modulo the conf dir path)')
need(open(W + '/ctl/sib/sib.out').read().split('\n')[0] == [l for l in open(R141 + '/sib/sib.out') if l.startswith('batch58pps39\t')][0].rstrip('\n'),
     'control sib differs')
need(same(W + '/scripts/selected-071.txt', R141 + '/ec3/selected-071.txt'), 'selected-071')


# ---------------------------------------------------------------- values from one producer set
def values(lab, batch):
    o = W + '/' + lab
    c1 = receipts(o + '/conf/c1.txt', 'FactFidelity')
    c2 = receipts(o + '/conf/c2.txt', 'RetainedLifecycle')
    c3 = receipts(o + '/conf/c3.txt', 'FormConformance')
    c4 = receipts(o + '/conf/c4-receipts.txt', 'CoreCoverage')
    gr = receipts(o + '/x/x.txt', 'GeneratedRetirement')
    orl = receipts(o + '/x/x.txt', 'OwnershipRealization')
    need(all(len(x) == 20 for x in (c1, c2, c3, c4)), lab + ': C1-C4 not twenty programs')
    need(S(gr, 'unwind') == 0, lab + ': unwind drops')
    ec4 = open(o + '/ec4/ec4.txt').read()

    def e4(name):
        m = re.search(r'^' + re.escape(name) + r'=(\d+)(?:/(\d+))?', ec4, re.M)
        need(m, 'ec4 line ' + name)
        return int(m.group(1)), (int(m.group(2)) if m.group(2) else None)
    e3 = dict(l.rstrip('\n').split('\t')[:2] for l in open(o + '/ec3/ec3.txt') if not l.startswith('#'))
    perm = [l for l in open(o + '/ec3/perm-t2.txt') if l.strip()]
    sel = [l for l in open(W + '/scripts/selected-071.txt') if l.strip()]
    sib = {l.split('\t')[0]: dict(t.split('=') for t in l.strip().split('\t')[1:]) for l in open(o + '/sib/sib.out')}[batch]
    ck = {r['key']: r for r in csv.DictReader(open(o + '/g2/keys.tsv'), delimiter='\t')}
    ec1 = [l for l in open(o + '/ec1/ec1_ident.out') if l.startswith('ROW %s ' % batch)]
    tot = [l for l in open(o + '/ec1/ec1_ident.out') if l.startswith(batch + ' class-joined ')]
    need(len(tot) == 1 and int(tot[0].split()[2]) == len(ec1), lab + ': ec1 total line')
    dl = [l for l in open(glob.glob(o + '/decline/*.tsv')[0]).read().strip().split('\n')]
    mm = re.match(r'# complete rc=0 with entry_sha256 = manifest (\d+)/20; repair=guarded (\d+)/20; guarded_fallbacks=0 (\d+)/20$', dl[-1])
    need(mm and len(dl) == 21, lab + ': decline reader')
    src, mapped = S(c2, 'source_release_sites'), S(c2, 'matched')
    cres, _ = e4('ec4.cover.control.residual_rows'); cret, _ = e4('ec4.cover.control.retirement_nonempty')
    cinv, _ = e4('ec4.cover.control.invalid_loans'); coep, _ = e4('ec4.cover.control.ordinary_error_points')
    v = {
        'ec1.both': '', 'ec1.necessity': '', 'ec1.replay-only': '', 'conf.import.entries': '', 'conf.import.reach-entries': '',
        'ec1.compiler-only': str(len(ec1)),
        'ec2.destructions': str(S(c2, 'emitted_release_sites') + S(gr, 'implicit_release_sites')),
        'ec2.duplicated': str(S(c2, 'extra_emitted')),
        'ec2.mapped': str(mapped),
        'ec2.retained-raw': str(src - S(orl, 'closed_explicit')),
        'ec2.unmapped': str(src - mapped + S(gr, 'unreceipted')),
        'ec2.waived': str(S(gr, 'implicit_release_sites')),
        'ec3.bridge-ledger': e3['ec3.bridge-ledger'], 'ec3.bridge-tree': e3['ec3.bridge-tree'].split()[0],
        'ec3.ledger': e3['ec3.ledger'], 'ec3.tree': e3['ec3.tree'], 'ec3.reconciled': e3['ec3.reconciled'],
        'ec3.perm-detected': str(sum(l.rstrip().endswith('... ok') for l in perm)), 'ec3.perm-total': str(len(sel)),
        'waiver.sibling-sites': sib['count'], 'waiver.sibling-sites.programs': sib['programs'],
        'ec4.clean': str(e4('ec4.clean')[0]), 'ec4.core': str(e4('ec4.core')[0]), 'ec4.fact': str(e4('ec4.fact')[0]),
        'ec4.form': str(e4('ec4.form')[0]), 'ec4.retire': str(e4('ec4.retire')[0]),
        'ec4.cover.decline': str(20 - min(int(mm.group(1)), int(mm.group(2)), int(mm.group(3)))),
        'ec4.cover.repair': str(cres + cret), 'ec4.cover.viol': str(cinv + coep),
        'conf.cert.total': ck['conf.cert.total']['value'], 'conf.cert.matched': ck['conf.cert.matched']['value'],
        'conf.fact.subjects': ck['conf.fact.subjects']['value'],
        'conf.retire.sites': ck['conf.retire.sites']['value'], 'conf.retire.matched': ck['conf.retire.matched']['value'],
    }
    need(int(v['ec2.mapped']) == int(v['conf.retire.matched']), lab + ': ec2.mapped != conf.retire.matched')
    need(sum(r.get('entry_sha256_matches') == 'yes' for r in c1.values()) == 20, lab + ': C1 sha256 not 20/20')
    return v, dict(c1=c1, c2=c2, c3=c3, c4=c4, gr=gr, orl=orl, rr=receipts(o + '/x/x.txt', 'RemainingRoots'),
                   c2b=receipts(o + '/x/c2b.txt', 'RetainedLifecycle'), ec4=ec4, e3=e3, ck=ck, ec1=ec1, dl=dl)


vc, _ = values('ctl', 'batch58pps39')
need(set(vc) == set(r141), 'value keys != r141 keys: %s' % sorted(set(vc) ^ set(r141)))
bad = [k for k in r141 if vc[k] != r141[k]['value_58ppp']]
need(not bad, 'CONTROL FAILED: ' + ', '.join('%s %r != %r' % (k, vc[k], r141[k]['value_58ppp']) for k in bad))
v, X = values('60sp', 'batch60sp')
_, XC = values('ctl', 'batch58pps39')

# 60s' cross-checks against main 225 and main's custody_count.py
cc = open(W + '/60sp/custody/cc.txt').read()
need('count by the emitted tree: 2715 (realized 2715 - 0 + 0)' in cc and 'receipt: data=true' in cc, 'custody_count')
need((v['ec3.ledger'], v['ec3.tree'], v['ec3.reconciled']) == ('2715', '2715', '2715'), 'ec3 is not main 225\'s 2,715')
need(not [l for l in open(W + '/60sp/ec3/ec3.txt') if l.startswith('# mismatch')], 'custody mismatch rows at 60s\'')
need(S(X['c2'], 'waiver_drop') == 23, 'C2 waiver_drop not main 225\'s 23 implicit closes')
need(same(W + '/60sp/conf/c4.txt', W + '/ctl/conf/c4.txt'), 'C4 --kinds moved')
need(same(W + '/60sp/conf/c2.txt', W + '/ctl/conf/c2.txt') is False, 'expected C2 waiver_drop change')
for p, r in X['c2'].items():
    for f in ('source_release_sites', 'emitted_release_sites', 'matched', 'unmatched_source', 'extra_emitted'):
        need(r[f] == XC['c2'][p][f], 'C2 %s %s moved' % (p, f))
ec1v = open(W + '/60sp/ec1/ec1_variants.out').read()
need('batch60sp\tfnkey=0\td6=0' in ec1v and 'batch60\tfnkey=0\td6=0' in ec1v and 'batch60s\tfnkey=0\td6=0' in ec1v, 'ec1 variants')
diag = sum(sum(1 for _ in open(f)) - 1 for f in glob.glob(M + '/batch60sp/*.raw-boundary-compiler-diagnostics.tsv'))
need(diag == 0, 'compiler diagnostics at 60s\'')
sibl = open(W + '/60sp/sib/sib.out').read()
need('batch60sp\tjson_files=20\tcount=0\tdescriptors=0\tprograms=0\ttsv_files=20\ttsv_rows=0' in sibl, 'sibling 60s\'')
man = list(csv.DictReader(open(M + '/batch60sp-manifest.tsv'), delimiter='\t'))
ctl6 = {r['program']: r for r in csv.DictReader(open(W + '/60sp/conf/control-final-replay.tsv'), delimiter='\t')}
need(sorted(r['fingerprint'] + '.json' for r in man) == sorted(r['file'] for r in ctl6.values()), 'control files != 60sp manifest')
need(sorted(os.path.basename(r['accepted_artifact']) for r in X['c1'].values()) == sorted(r['fingerprint'] + '.json' for r in man),
     'C1 entries != 60sp manifest')
need(X['dl'][-1] == '# complete rc=0 with entry_sha256 = manifest 20/20; repair=guarded 20/20; guarded_fallbacks=0 20/20', 'decline 60s\'')
loans = sum(int(r['loans_invalid_true']) + int(r['loans_invalid_false']) for r in ctl6.values())

# ---------------------------------------------------------------- causes (60s', no frame header)
RUN = ("wave-6o's census-side checkers (docs origin/main agents/tools/conformance, byte-identical to r141's copies) + "
       "analysis-fanout 008's resid_scan.py, run at main/batch60sp (main 225: head 32d966b9f, analyses a5495bf59; status=complete "
       "data=true, 20 / 20, cache_hits 20/20, diagnostics 0): C2, C3 (+ --table), C4 --kinds and receipts (--contracts = "
       "crates/pointer_replacer/src at 32d966b9f, git archive) by r146/conf/scripts/run_py.sh; C1 c1_fact_fidelity.py "
       "--verify-sha256 against era-5c's 60-KINDORDER cache (worktrees/era5c-r215-kindorder/cache/era5b-model-cache-v1, "
       "manifest main/batch60sp-manifest.tsv; 20 / 20 entry_sha256_matches=yes) and the clean-final-replay control (resid_scan.py "
       "over the manifest's 20 entries, streamed under a 30 GiB MemAvailable guard) by run_stream.sh; C2b --panic-abort and X "
       "(x_instruments.py, rustc --emit=mir one program at a time) by run_x.sh in the run window (SLOT-FREE START 21:37:03Z / "
       "END 21:38:29Z 2026-10-13); receipts in scratch/analysis-fanout/r146/conf/60sp/{conf, x, ec4}; "
       "CONTROL: the same re-pointed producers on main/batch58pps39 with the S39 cache reproduce r141/conf's receipts byte for "
       "byte and r141/conf/staged.tsv's value_58ppp on all 34 keys")
CEN = ("census main/batch60sp (main 225: head 32d966b9f = 60s 4eb66851b + wave-6a's e3afd991e (every A9 reference lend "
       "withheld) + era-5c's final-frame files; analyses a5495bf59; cache-only on era-5c's 60-KINDORDER cache, keycheck 20 / 20 "
       "on analysis 1d8dcd40, configuration d9a474da, launch 2e94d9a5; status=complete data=true, 20 / 20 emitted, 0 degraded "
       "programs, diagnostics_new=0)")
gr, orl, c2, c3, c4 = X['gr'], X['orl'], X['c2'], X['c3'], X['c4']
c3o, c4o, orlo = XC['c3'], XC['c4'], XC['orl']
src, mapped, emitted = S(c2, 'source_release_sites'), S(c2, 'matched'), S(c2, 'emitted_release_sites')
implicit, recd, unrec = S(gr, 'implicit_release_sites'), S(gr, 'receipted'), S(gr, 'unreceipted')
closed_x = S(orl, 'closed_explicit')
XS = ("X at 60s' (r146/conf/60sp/x/x.txt): GeneratedRetirement implicit_release_sites %d (%s), receipted %d, unreceipted %d, "
      "unwind 0; OwnershipRealization closed_explicit %d (%s), owners %s" % (implicit, byprog(gr, 'implicit_release_sites'), recd,
                                                                           unrec, closed_x, byprog(orl, 'closed_explicit'),
                                                                           n(S(orl, 'owners'))))
OWN = ("58''' -> 60s' in X: tulipindicators gains one Box owner closed at its C free site (closed_explicit 1 -> 2) and one "
       "implicit scope-exit close, smoke::test_ind_name's answers#114 ([Option<Box<[f64]>>; 10], receipt waiver-drop-scope-exit "
       "(field transaction), lib.rs:20643); heman's eight box-param-reseat formals (kmAABB2Initialize::pBox, kmAABB3Initialize::pBox, "
       "kmMat3Multiply / kmMat3Transpose / kmPlaneFromPoints / kmQuaternionMultiply / kmVec2MidPointBetween / kmVec3TransformCoord "
       "::pOut) are owners transferred, with no release site (owners 25 -> 33); brotli owners 472 -> 488, closed_explicit 67 as at "
       "58'''")
WD = byprog(c2, 'waiver_drop')
PREV = " previously at 58''': %s"
LEDGER = ("main's custody_count.py at main/batch60sp: ledger-only 0, tree-only 0, count by the emitted tree 2,715 (realized 2,715 - 0 + 0) "
          "= the ledger; 071 ec3_keys.py at main/batch60sp (r146/conf/60sp/ec3/ec3.txt; CONTROL: at batch58pps39 it reproduces r141's "
          "ec3-s39.txt byte for byte): ledger 2,715 (per-program.kv realized_subjects 2,669 + realized_model_raw_family 46), tree "
          "2,715, reconciled 2,715, mismatch 0; custody issues none, observation states expected-form-observed 2,715 / owner-reverted 32. "
          "By identity by the tree against 58''' (batch58pps39): +43 / -6 (brotli +25 / -5, heman +9 / -1, tulipindicators +8, libzahl +1; "
          "the four ledger-only tulipindicators rows of 58''' are delivered in the tree at 60s'); against 60 +15 / -8 (main 225 section 2)")
c3d = '; '.join('%s %s -> %s' % (p, c3o[p]['delivered'], c3[p]['delivered']) for p in sorted(c3) if c3[p]['delivered'] != c3o[p]['delivered'])
c4d = '; '.join('%s outside %s -> %s of %s -> %s (%s)' % (p, c4o[p]['outside'], c4[p]['outside'], n(int(c4o[p]['constructs'])),
                n(int(c4[p]['constructs'])), c4[p]['outside_kinds'])
                for p in sorted(c4) if c4[p]['constructs'] != c4o[p]['constructs'] or c4[p]['outside'] != c4o[p]['outside'])
CK = ("086 conf_keys.py at main/batch60sp + r146/conf/60sp/conf (r146/conf/60sp/g2/keys.tsv, departures-batch60sp.tsv; CONTROL: at "
      "batch58pps39 + the control's conf it reproduces r141's keys-s39.tsv and departures-batch58pps39.tsv)")
pairs = re.search(r'pairs (.*?); per program (.*)$', X['ck']['conf.cert.total']['provenance'])
fams = re.search(r'by family (.*?); rows', X['ck']['conf.cert.matched']['provenance']).group(1)
CERT = ("realized subjects whose delivered class differs from the model kind: pairs %s; per program matched/total %s; matched by "
        "family %s. 58''' -> 60s': +4, all brotli ref -> opt-box-slice matched by allocator-contract: "
        "src::enc::metablock::InitBlockSplitterDistance::{new_array#41, new_array_0#98} and "
        "InitContextBlockSplitter::{new_array#48, new_array_0#105}; no departure lost; Owning -> Ref departures 0 (main 225 section 4); "
        "heman's three raw -> ref without a certificate (kmRay2IntersectBox::{next_point#45, other_point#59, this_point#41}) as at "
        "58'''; heman's eight Box formals are model Owning delivered Box, not departures" % (pairs.group(1), pairs.group(2), fams))
CTLD = ("THE CLEAN-FINAL-REPLAY CONTROL OF THE ACCEPTED CANDIDATE, NOT the BorrowCoverage certificate check of the delivered "
        "assignment; re-derived from the 60-KINDORDER cache entries")
PERM = ("the 14 tests of 071 perm/selected.txt (docs agents/artifacts/2026-10-06-analysis-fanout-071/perm/selected.txt) are all "
        "'... ok' in the assembler's t2 full-suite log at 32d966b9f (scratch/assembler/batch-60sp-r/b60spr-t2-suite.log; "
        "b60spr-gates.txt: head=32d966b9f, 5,549 passed / 36 failed = the standing 36, added_vs_core and missing_vs_core empty, "
        "t2 = t4); extract scratch/analysis-fanout/r146/conf/60sp/ec3/perm-t2.txt; the same 14 names as "
        "at 58'''; not re-run (cargo test)")
SIB = ("main/batch60sp/<p>.raw-boundary-pending-sibling-overlap.json reads count 0 with descriptors [] in all twenty programs and "
       "each .tsv carries only its header (r146/conf/scripts/sib.py; CONTROL: batch58pps39 0 / 0 as r141 read it). No call "
       "argument is waived as a pending sibling since R829-1's pair hold (batch 57)")
NAX = ("no instrument at 60s' either (analysis-fanout 086 disposition (d) drop; 071 section 4); the row stays empty")
st = {}
NA = ('not-at-60sp', '')
st['ec1.both'] = NA + (NAX,)
st['ec1.necessity'] = NA + ("no instrument at 60s' (needs the replay-only cell; analysis-fanout 086 disposition (d)); the row stays empty",)
st['ec1.replay-only'] = NA + (NAX,)
st['ec1.compiler-only'] = ('differs', v['ec1.compiler-only'],
    "%s; the record's class-aware join (r141's ec1_ident.py with the batches from argv: r146/conf/scripts/ec1/ec1_ident.py, every "
    "row printed in 60sp/ec1/ec1_ident.out): reverted subjects with model kind ref / owning whose function, or a member of its "
    "final-revert class, carries a compiler diagnostic: 0, because no program carries a compiler diagnostic (20 "
    "<p>.raw-boundary-compiler-diagnostics.tsv header-only; main 225 diagnostics 0). By identity against the 4 at 58''': all four "
    "realize at 60s' (brotli compress_fragment_two_pass::BuildAndStoreCommandPrefixCode::bits#3 as slice; tulipindicators "
    "smoke::get_array::{line#4, s#2} as slice, num#34 as optional). The one reverted safe-model subject, brotli "
    "brotli_bit_stream::BuildAndStoreBlockSwitchEntropyCodes::self_0#1 (reverted as at 58''' and 60), has no diagnostic in its "
    "function or class. Function-keyed join 0, the D6 alternative 0 (r146/conf/scripts/ec1/ec1_variants.py); batch60 0 and "
    "batch60s 0 by the same join (60s' reverted safe-model subjects 1, 60s 94). CONTROL: the same join gives 18 / 17 / 4 at "
    "batch58 / batch58pp / batch58pps39, row for row = r141's ec1_ident.out.%s" % (CEN, PREV % rec['ec1.compiler-only']['value']))
st['ec2.destructions'] = ('differs', v['ec2.destructions'],
    "%s; %s. Emitted destructions: %d explicit release sites (C2 emitted_release_sites, all matched) + %d implicit Box closes "
    "(X GeneratedRetirement: %s; all scope-exit, 0 overwrite, 0 unwind). %s; brotli none-drop rows 129 -> 133 and heman 0 -> 2 "
    "(owners X proves act on None; not counted).%s" % (RUN, XS, emitted, implicit, byprog(gr, 'implicit_release_sites'), OWN,
                                                       PREV % rec['ec2.destructions']['value']))
st['ec2.duplicated'] = ('equal', v['ec2.duplicated'], "%s; C2 extra_emitted %s of %d." % (RUN, v['ec2.duplicated'], src))
st['ec2.mapped'] = ('equal', v['ec2.mapped'], "%s; C2 matched %d of %d source release sites (%s); per program as at 58''' (C2 "
    "moves only in waiver_drop)." % (RUN, mapped, src, byprog(c2, 'matched')))
st['ec2.retained-raw'] = ('differs', v['ec2.retained-raw'],
    "%s; %s. Retained raw free sites (a coverage outcome, not a failure): the %d matched explicit release sites less the %d whose "
    "owner is a Box closed by an explicit drop at the C free site; DERIVED from the two receipts. 58''' -> 60s': closed_explicit "
    "93 -> 94, tulipindicators 1 -> 2; the other programs equal. %s.%s" % (RUN, XS, src, closed_x, OWN, PREV % rec['ec2.retained-raw']['value']))
st['ec2.unmapped'] = ('equal', v['ec2.unmapped'], "%s; C2 unmatched_source %d + X GeneratedRetirement unreceipted %d." % (RUN, src - mapped, unrec))
st['ec2.waived'] = ('differs', v['ec2.waived'],
    "%s; X GeneratedRetirement %d implicit release sites, %d receipted, %d unreceipted (%s): the 8 at 58''' + tulipindicators "
    "smoke::test_ind_name's answers#114 scope-exit close (receipt waiver-drop-scope-exit (field transaction)). This is not the "
    "leak-parity row (the census group's key): the census receipt (C2 waiver_drop, main 225's implicit closes) reads %d = %s; "
    "heman's 4 are scope-exit receipts beside its Box formals, which X counts as transferred owners with no implicit release site.%s"
    % (RUN, implicit, recd, unrec, byprog(gr, 'implicit_release_sites'), S(c2, 'waiver_drop'), WD, PREV % rec['ec2.waived']['value']))
E3 = CEN + '; ' + LEDGER
st['ec3.ledger'] = ('differs', v['ec3.ledger'], E3 + ". This key is the ledger's figure; it equals the tree's 2,715 (ec3.tree), "
    "the count of record." + PREV % rec['ec3.ledger']['value'])
st['ec3.tree'] = ('differs', v['ec3.tree'], E3 + ". The delivered count of record (by the emitted tree); the ledger reads the same "
    "2,715." + PREV % rec['ec3.tree']['value'])
st['ec3.reconciled'] = ('differs', v['ec3.reconciled'], E3 + ". Ledger and tree agree on all 2,715 identities; the census has no "
    "typed failure." + PREV % rec['ec3.reconciled']['value'])
st['ec3.bridge-ledger'] = ('equal', v['ec3.bridge-ledger'], "%s; 071 ec3_keys.py at main/batch60sp: applied custody bridge receipts "
    "%s, all matched-raw; 0 pending, 0 waived-pending." % (CEN, v['ec3.bridge-ledger']))
st['ec3.bridge-tree'] = ('equal', v['ec3.bridge-tree'], "%s; 071 ec3_keys.py at main/batch60sp: %s applied receipts rendered "
    "(matched-raw); tree-only witnesses 0, receipt-without-render 0." % (CEN, v['ec3.bridge-tree']))
st['ec3.perm-detected'] = ('equal', v['ec3.perm-detected'], PERM + '.')
st['ec3.perm-total'] = ('equal', v['ec3.perm-total'], PERM + '.')
st['waiver.sibling-sites'] = ('equal', v['waiver.sibling-sites'], "%s; %s." % (CEN, SIB))
st['waiver.sibling-sites.programs'] = ('equal', v['waiver.sibling-sites.programs'], "%s; programs with a pending-sibling-overlap "
    "row: 0 of 20; %s." % (CEN, SIB))
st['ec4.clean'] = ('equal', v['ec4.clean'],
    "%s; ec4_rows.py over r146/conf/60sp/ec4 (60sp/conf's c1 / c2 / c3 / c4-receipts / control + 60sp/x/x.txt): C1 0 mismatches "
    "of %s with 20 / 20 sha256 yes, C2 0 unmapped / 0 duplicated of %d, C3 0 unclassified of %s, X GeneratedRetirement 0 "
    "unreceipted, the control clean (re-derived from the 60-KINDORDER entries): %s of 20. X RemainingRoots: %d unproved (%s: "
    "lodepng's two field-transaction owners as at 58''' + tulipindicators' answers#114 field-transaction owner), counted clean as "
    "by 130a. The census has no delivery-custody failure at 60s'." % (RUN, n(S(X['c1'], 'subjects')), src, n(S(c3, 'delivered')),
                                                                      v['ec4.clean'], S(X['rr'], 'unproved'), byprog(X['rr'], 'unproved')))
st['ec4.core'] = ('differs', v['ec4.core'],
    "%s; C4 CoreCoverage (c4-receipts.txt; an inventory, not a failure): %s of %s construct occurrences outside the modeled core "
    "(contract calls %s, opaque calls %s). 58''' -> 60s': %s -> %s of %s -> %s: %s; the other sixteen equal; the --kinds table "
    "(c4.txt) byte-identical to 58'''.%s" % (RUN, n(int(v['ec4.core'])), n(S(c4, 'constructs')), n(S(c4, 'contract_calls')),
                                             n(S(c4, 'opaque_calls')), n(S(c4o, 'outside')), n(int(v['ec4.core'])),
                                             n(S(c4o, 'constructs')), n(S(c4, 'constructs')), c4d, PREV % rec['ec4.core']['value']))
st['ec4.cover.decline'] = ('equal', v['ec4.cover.decline'],
    "%s; %s. Declines 0: the 20 manifest entries are present and sha256-matched by C1 (20 / 20 yes), each with a final replay "
    "read by the control; the solve's records (r141's guarded.py over worktrees/era5c-r215-kindorder/progress.jsonl, all "
    "twenty): complete rc=0 with entry_sha256 = the manifest's 20 / 20, receipt repair=guarded 20 / 20, guarded_fallbacks=0 20 / 20 "
    "(guarded_verifications 2 each, a5_mode precise_replay); CONTROL: the reader on the S39 solve gives r141's 20 / 20 / 20 row "
    "for row." % (RUN, CTLD))
st['ec4.cover.repair'] = ('equal', v['ec4.cover.repair'],
    "%s; %s. Repairs the final replay still needs: residual-conflict rows 0 (the family captured with 0 rows in all 20 entries), "
    "final retirement conflicts / demotions / unresolved non-empty in 0 of 20." % (RUN, CTLD))
st['ec4.cover.viol'] = ('equal', v['ec4.cover.viol'],
    "%s; %s. Invalid loans 0 of %s final-round loans (per program the loan counts equal those of the S39 entries), ordinary "
    "error points 0, 20 / 20 programs clean." % (RUN, CTLD, n(loans)))
st['ec4.fact'] = ('equal', v['ec4.fact'],
    "%s; C1 FactFidelity against the 60-KINDORDER cache's sealed model maps (streamed; --verify-sha256, 20 / 20 yes): 0 mismatches "
    "of %s subjects (consumed_eq_accepted %s; per program the subject counts equal those at 58''')." % (RUN, n(S(X['c1'], 'subjects')),
                                                                                                      n(S(X['c1'], 'consumed_eq_accepted'))))
st['ec4.form'] = ('equal', v['ec4.form'],
    "%s; C3 FormConformance: 0 unclassified of %s delivered (= the tree's 2,715; no ledger-only rows at 60s'), classified %s, "
    "extension %s, administrative %s; 58''' -> 60s' delivered: %s." % (RUN, n(S(c3, 'delivered')), n(S(c3, 'classified')),
                                                                     S(c3, 'extension'), S(c3, 'administrative'), c3d))
st['ec4.retire'] = ('equal', v['ec4.retire'],
    "%s; C2 RetainedLifecycle (explicit): unmatched_source %d + extra_emitted %d of %d source release sites (C2 waiver_drop %d: %s)."
    % (RUN, src - mapped, S(c2, 'extra_emitted'), src, S(c2, 'waiver_drop'), WD))
st['conf.cert.total'] = ('differs', v['conf.cert.total'], "%s; %s; %s.%s" % (CEN, CK, CERT, PREV % rec['conf.cert.total']['value']))
st['conf.cert.matched'] = ('differs', v['conf.cert.matched'], "%s; %s; %s.%s" % (CEN, CK, CERT, PREV % rec['conf.cert.matched']['value']))
st['conf.fact.subjects'] = ('equal', v['conf.fact.subjects'],
    "%s; %s: sum of C1 subjects= over 20 programs (60sp/conf/c1.txt) = %s; cross-check from the census: subjects.tsv rows with "
    "model_kind != unmodeled = %s. The denominator of ec4.fact." % (RUN, CK, n(S(X['c1'], 'subjects')), n(int(v['conf.fact.subjects']))))
st['conf.import.entries'] = NA + ("no producer at 60s' in any group: survey STOP 2's reading at batch 48 (1,146); no census table or "
                                  "conformance checker carries it; the row stays empty",)
st['conf.import.reach-entries'] = NA + ("no producer at 60s' in any group: survey STOP 2's reading at batch 48 (397); no census "
                                        "table or checker carries it; the row stays empty",)
st['conf.retire.sites'] = ('equal', v['conf.retire.sites'], "%s; %s: sum of C2 source_release_sites= over 20 programs "
                           "(60sp/conf/c2.txt) = %d." % (RUN, CK, src))
st['conf.retire.matched'] = ('equal', v['conf.retire.matched'], "%s; %s: sum of C2 matched= over 20 programs (60sp/conf/c2.txt) = "
                             "%d (= ec2.mapped)." % (RUN, CK, mapped))

# ---------------------------------------------------------------- the validator keys
VAL = json.load(open(W + '/validator-state.json'))
if VAL['filed']:
    die('wave-6o 151 filed: wire its receipts here before staging')
VN = ("wave-6o's BorrowCoverage validator over batch60sp is relay 189 / report 151 (the release built at 60s 4eb66851b, "
      "SLOT-FREE BUILD END 17:15:04Z 2026-10-13); NOT FILED at staging (docs origin/main agents/reports/wave-6o/ ends at %s, "
      "checked after git fetch at %s): no 60s' value; the 58''' receipts (wave-6o 149) do not stand for 60s' (the model entries "
      "changed: C1's accepted artifacts differ from the S39 entries in 20 of 20 programs)" % (VAL['last'], VAL['checked']))
for k in VKEYS[:4]:
    st[k] = NA + (VN,)
for k in VKEYS[4:]:
    st[k] = ('carried', rec[k]['value'], "carried, input identical: a comparison row fixed at 58'' by definition (wave-6o 148's "
             "receipt table against main/batch58pp/per-program.kv); the 60s' census does not re-measure 58''; value as staged by "
             "analysis-fanout 117")
need(all(X['c1'][p]['subjects'] == XC['c1'][p]['subjects'] for p in X['c1']), 'C1 subject counts moved')
ctlc = {r['program']: r for r in csv.DictReader(open(W + '/ctl/conf/control-final-replay.tsv'), delimiter='\t')}
need(all(int(ctl6[p]['loans_invalid_true']) + int(ctl6[p]['loans_invalid_false']) == int(ctlc[p]['loans_invalid_true']) + int(ctlc[p]['loans_invalid_false']) for p in ctl6), 'loan counts moved')
need((S(orl, 'owners'), S(orlo, 'owners'), orl['brotli']['owners'], orl['heman']['owners'], orlo['heman']['owners'], closed_x, S(orlo, 'closed_explicit')) == (666, 638, '488', '33', '25', 94, 93), 'X owner numbers in the causes')
need(sum(XC['c1'][p]['accepted_artifact'] != X['c1'][p]['accepted_artifact'] for p in X['c1']) == 20, 'entries not all changed')

need(set(st) == set(KEYS), 'staged keys != group keys: %s' % sorted(set(st) ^ set(KEYS)))
out = ['key\tvalue_now\tvalue_60sp\tverdict\tcause']
cnt = {}
for k in KEYS:
    verdict, val, cause = st[k]
    now = rec[k]['value']
    need(verdict in ('equal', 'differs', 'carried', 'not-at-60sp'), 'verdict ' + k)
    if k in v:
        need(val == v[k], 'staged value is not the measured value: ' + k)
    if verdict == 'equal':
        need(val == now, 'equal but %s != %s: %s' % (val, now, k))
    if verdict == 'differs':
        need(val != now and cause.endswith(PREV % now), 'differs row: ' + k)
    if verdict == 'not-at-60sp':
        need(val == '', 'not-at row with a value: ' + k)
    if verdict == 'carried':
        need(val == now and 'carried' in cause, 'carried row: ' + k)
    for bad in ('\t', '\n', '|'):
        need(bad not in cause and bad not in val, 'forbidden character in ' + k)
    out.append('\t'.join([k, now, val, verdict, cause]))
    cnt[verdict] = cnt.get(verdict, 0) + 1
open(W + '/staged.tsv', 'w').write('\n'.join(out) + '\n')
print('control: 34 / 34 keys = r141 value_58ppp; staged %d keys: %s' % (len(KEYS), ', '.join('%s %d' % kv for kv in sorted(cnt.items()))))
for k in KEYS:
    if st[k][0] == 'differs':
        print('  differs %s %s -> %s' % (k, rec[k]['value'], st[k][1]))
