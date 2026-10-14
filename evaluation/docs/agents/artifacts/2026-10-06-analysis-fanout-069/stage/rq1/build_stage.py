#!/usr/bin/env python3
"""relay 095 item 1, PART rq1: stage the RQ1-side keys at the L01^14 frame census (main/frame14).
Read-only: reads the census dir, main 179b's artifacts, the 040 crown_units.py output, numbers-of-record on
docs origin/main (for 'was'); writes stage.json beside this script.
Run: nice -n 10 python3 build_stage.py"""
import csv, glob, json, os, re, subprocess, collections
csv.field_size_limit(10 ** 9)
HERE = os.path.dirname(os.path.abspath(__file__))
C = 'scratch/main/frame14'
A = 'docs/agents/artifacts/2026-10-06-main-179b'
NOR = subprocess.run(['git', '-C', 'crat/docs', 'show', 'origin/main:paper/numbers-of-record.md'],
                     capture_output=True, text=True, check=True).stdout
was = {}
for l in NOR.splitlines():
    m = re.match(r'^\| ([A-Za-z][A-Za-z0-9._-]*) \|([^|]*)\|', l)
    if m:
        was[m.group(1)] = m.group(2).strip()

PRE = ('at the frame of record L01^14 (landed <DATE>): census scratch/main/frame14 '
       '(code 4a47f16f7, analyses 0cede10fd, analysis frame era5c-l01p14-v1; cache era5c-l01p14-restored-solve, '
       '20/20 hits; ended 2026-10-06 07:23Z; status=complete data=true delivery=clean 20/20 emitted); '
       'analysis-fanout relay 095 item 1, part rq1 (staged by '
       'scratch/analysis-fanout/r095/stage/rq1/build_stage.py); ')
rows = []
def stage(key, value, layer, unit, prov, defsrc):
    assert key in was, key
    assert '|' not in value + prov, key
    rows.append(dict(key=key, value=value, layer=layer, unit=unit, provenance=PRE + prov, was=was[key],
                     definition_source=defsrc))

# ---- 1. rq1.frame14.* (R709-1's definition) --------------------------------------------------------------
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
n = deliv = safe = 0
for f in sorted(glob.glob(C + '/*.raw-boundary-subject-outcomes.tsv')):
    for r in csv.DictReader(open(f), delimiter='\t'):
        n += 1
        d = r['delivery'] == 'realized-as-predicted'
        deliv += d
        safe += (r['family'] in SAFE or d)
R454 = 36
clause = open(A + '/frame14-clause-line.txt').read()
assert 'count 3,361 / 4,275 = 78.62 %' in clause and 'decided safe 4,311 less R454 36' in clause
assert (n, deliv, safe - R454) == (7011, 3361, 4275), (n, deliv, safe)
rate = f'{deliv / (safe - R454) * 100:.2f}%'
assert rate == '78.62%'
CMD1 = ('command: a glob over frame14/*.raw-boundary-subject-outcomes.tsv (7,011 subject rows) counting '
        "delivery == realized-as-predicted, and family in {ref, slice, optional, box, cursor} or delivered "
        '(= 4,311), less the 36 R454 already-reference bindings (main 179b, agents/artifacts/2026-10-06-main-179b/'
        'frame14-clause-line.txt: count 3,361 / 4,275 = 78.62 %, decided safe 4,311 less R454 36); ')
DEF1 = ('Same definition as the rate of record (R709-1): realized-as-predicted subjects over the same census\'s '
        'in-scope safe decisions, less the 36 R454 bindings. R757-2 as worded (>= 78.2 %) MET at this census '
        '(needs >= 3,344). The old definition; R812-1\'s form (the stop-gap table withdraws 19: 3,361 / 4,256 = '
        '78.97 %) is not this key. ')
stage('rq1.frame14.delivered', str(deliv), 'delivered', 'count',
      CMD1 + DEF1 + 'This key: the numerator (delivered).', 'analysis-fanout 058 §6 (R709-1); main 179b §1')
stage('rq1.frame14.safe-decisions', str(safe - R454), 'decided', 'count',
      CMD1 + DEF1 + 'This key: the denominator (the frame\'s own in-scope safe decisions).',
      'analysis-fanout 058 §6 (R709-1); main 179b §1')
stage('rq1.frame14.realization-rate', rate, 'delivered', 'percent',
      CMD1 + DEF1 + f'This key: {deliv} / {safe - R454}.', 'analysis-fanout 058 §6 (R709-1); main 179b §1')
# the three keys of record take these values at the landing (their own provenance says so)
NOTE_REC = ('AT L01^14\'s LANDING (R822-1) this key takes rq1.frame14.*\'s value (its provenance, analysis-fanout '
            '058); 54\' read 3,375 / 4,270 / 79.0 %. ')
stage('rq1.frame-delivered', str(deliv), 'delivered', 'count',
      CMD1 + NOTE_REC + 'Realized-as-predicted subjects at the frame.', 'analysis-fanout 045 / 058 (R709-1)')
stage('rq1.frame-safe-decisions', str(safe - R454), 'decided', 'count',
      CMD1 + NOTE_REC + 'The census\'s in-scope safe decisions (R709-1), less R454\'s 36.',
      'analysis-fanout 045 / 058 (R709-1)')
stage('rq1.frame-realization-rate', f'{deliv / (safe - R454) * 100:.1f}%', 'delivered', 'percent',
      CMD1 + NOTE_REC + f'{deliv:,} / {safe - R454:,} = {rate} (one decimal, as this key has carried since 045).',
      'analysis-fanout 045 / 058 (R709-1)')

# ---- 2. CROWN by unit (rq2.crown.units*; 040's crown_units.py) ------------------------------------------
cu = open(HERE + '/crown-units-frame14.out').read().splitlines()
assert cu[0] == "{'delivered': 52, 'no-row': 3, 'undelivered': 6} of 61", cu[0]
und = [l.split('\t') for l in cu[1:]]
assert len(und) == 9
m61 = open(A + '/frame14-crown61.txt').read()
assert '# CROWN by unit: 52 / 61 (48 subjects + 4 fields)' in m61
main_false = sorted(l.split('\t')[1] for l in m61.splitlines() if l.endswith('\tFalse'))
assert main_false == sorted(u[1] for u in und), 'main and 040 disagree on the undelivered units'
unj = [u[1] for u in und if u[3] == 'no-row' and '::field' not in u[1]]
assert unj == ['src::bst::deleteNode::temp', 'src::bst::deleteNode::temp_0',
               'src::test::test_buffer_slice__range_error::a']
just = ['src::src::quadtree::quadtree::field0@d0']
gap = sorted(u[1] for u in und if u[1] not in unj + just)
assert gap == sorted(['src::src::bounds::quadtree_bounds::field0@d0', 'src::src::bounds::quadtree_bounds::field1@d0',
                      'src::src::bounds::quadtree_bounds_free::bounds', 'src::src::node::quadtree_node_free::node',
                      'src::src::point::quadtree_point_free::point'])
CMD2 = ('command: nice -n 10 python3 docs/agents/artifacts/2026-10-03-analysis-fanout-040/'
        'crown_units.py scratch/main/frame14 > r095/stage/rq1/crown-units-frame14.out '
        '(over wave-6a\'s 61-unit join crown61-emitted-l01p5.tsv; independent of main\'s crown61.py, whose '
        'agents/artifacts/2026-10-06-main-179b/frame14-crown61.txt reads the same 52 / 61 and the same nine '
        'undelivered units); ')
stage('rq2.crown.units', '61', 'n/a', 'count',
      CMD2 + 'CROWN\'s owning units on rs-crown (avl 10, bst 7, buffer 28, ht 2, quadtree 14), R507-1; unchanged.',
      'analysis-fanout 040 (R789-3 item 1)')
stage('rq2.crown.units.delivered', '52', 'delivered', 'count',
      CMD2 + '52 = 48 subjects + 4 fields (avl left/right, bst left/right). Against 54\' (48): +4 = quadtree\'s four '
      'receiver hand-over units (quadtree_bounds_new::bounds, quadtree_point_new::point, test_bounds::bounds, '
      'test_points::point), which 55 delivered first (main 179b §4: 55 had 52 too).',
      'analysis-fanout 040 / 045; main 179b §4 (E4)')
stage('rq2.crown.units.unjoinable', '3', 'n/a', 'count',
      CMD2 + 'no census subject row: bst deleteNode::temp, temp_0; buffer test_buffer_slice__range_error::a '
      '(the same three as frame 13 and 54\').', 'analysis-fanout 040 (R789-3 item 1)')
stage('rq2.crown.units.justified', '1', 'n/a', 'count',
      CMD2 + 'quadtree quadtree.root (field0), the sole OUR-CONSERVATISM-JUSTIFIED row of the 09-01 ledger '
      '(agents/tasks/2026-09-01-seat129-two-strategy-reads.md §5.3); still undelivered (no field-transaction row).',
      'analysis-fanout 040 (R789-3 item 1)')
stage('rq2.crown.units.ceiling', '57', 'n/a', 'count',
      CMD2 + '61 - 3 unjoinable - 1 justified.', 'analysis-fanout 040 (R789-3 item 1)')
stage('rq2.crown.units.gap', str(len(gap)), 'n/a', 'count',
      CMD2 + 'units inside the ceiling still undelivered (all quadtree, model-raw): the fields quadtree_bounds.nw, '
      'quadtree_bounds.se (no field-transaction row) and the release functions\' parameters '
      'quadtree_bounds_free::bounds, quadtree_node_free::node, quadtree_point_free::point (degraded:unchanged); '
      '52 + 5 = 57. The same five identities as 040\'s gap.', 'analysis-fanout 040 (R789-3 item 1)')

# ---- 3. the copy-lend arm (main 179b §3, frame14-pairs.txt) ------------------------------------------------
pl = open(A + '/frame14-pairs.txt').read().splitlines()
lines = [l for l in pl if l[:3] in ('OK ', '?? ', 'NO ', 'XX ')]
assert len(lines) == 48 and all(l[:3] in ('OK ', '?? ') for l in lines)
assert 'listed locals moving as listed: 44 / 48' in pl and 'model-kind moves OFF the list: 0 {}' in pl
ok = [l for l in lines if l.startswith('OK')]
per_ok = collections.Counter(l.split()[1] for l in ok)
per_listed = collections.Counter(l.split()[1] for l in lines)
assert per_ok == {'brotli': 40, 'heman': 2, 'binn': 2} and per_listed == {'brotli': 40, 'heman': 2, 'binn': 6}
pairs = {p: per_listed[p] // 2 for p in per_listed}
assert pairs == {'brotli': 20, 'binn': 3, 'heman': 1}
for l in ok:
    mv = re.search(r'model (\S+) \(listed (\S+)\)', l)
    assert mv and mv.group(1) == mv.group(2) and mv.group(1) in ('ref->raw', 'raw->ref'), l
CMD3 = ('source: agents/artifacts/2026-10-06-main-179b/frame14-pairs.txt (main 179b §3: each of era-5c 144 §3\'s '
        'listed locals, model kind 55 -> frame read from the census subject rows; 55\'s model is L01^13 = the arm-off '
        'control); command: build_stage.py counts the 48 listed-local lines by verdict (OK = moved as listed, ?? = '
        'no census subject row) and asserts the footer lines \'listed locals moving as listed: 44 / 48\' and '
        '\'model-kind moves OFF the list: 0\'; ')
COMMON3 = ('The 48 = 24 pairs x 2 locals. At the census 44 / 48 listed locals move as listed: every brotli pair (40 '
           'locals), heman\'s pair (kmQuaternionToAxisAngle #1 ref->raw, #3 raw->ref) and binn\'s binn_is_valid #3 / #4; '
           'binn\'s other two pairs (binn_is_valid #12 / #16 and #20 / #21) are model slots with no census subject '
           'row, so the census cannot read them (era-5c 144: \'these are the model\'s slots\'); their swap is the '
           'solve comparison\'s (rq3-inator 014a / 014c, era-5c 144 §3). 0 model-kind moves off the list. So the '
           'census confirms 22 of the 24 pairs whole and contradicts none. Delivery is not this key: brotli\'s pairs '
           'net +1 delivered (15 kind-raw -> delivered, 14 -> kind-raw), heman +1 / -1. ')
stage('analysis.copy-lend.swaps', '24', 'decided', 'count',
      CMD3 + COMMON3 + 'This key: the paired swaps on the twenty (brotli 20, binn 3, heman 1).',
      'analysis-fanout 058 §6 (the second host\'s 24, era-5c 144 §3); relay 095 item 1')
for p in ('brotli', 'binn', 'heman'):
    extra = {'brotli': ' All 20 confirmed at the census (40 / 40 locals).',
             'binn': ' All in binn_is_valid; 1 confirmed at the census (#3 / #4), 2 on non-subject model slots.',
             'heman': ' kmQuaternionToAxisAngle; confirmed at the census (2 / 2 locals).'}[p]
    stage(f'analysis.copy-lend.swaps.{p}', str(pairs[p]), 'decided', 'count',
          CMD3 + COMMON3 + f'This key: {p}\'s.' + extra,
          'analysis-fanout 058 §6; relay 095 item 1')
stage('analysis.copy-lend.owners-created', '0', 'decided', 'count',
      CMD3 + COMMON3 + 'This key: slots the arm makes Owning that are not Owning with it off: 0. At the census every '
      'listed move is ref <-> raw and no other census subject\'s model kind moves against 55 (L01^13, the arm-off '
      'control); the non-subject model slots are the solve comparison\'s 0 (rq3-inator 014a / 014c).',
      'analysis-fanout 058 §6; relay 095 item 1 (owners created 0)')

# ---- 4. leak parity (census-receipt.txt implicit_close_*) -------------------------------------------------
rec = dict(l.split('=', 1) for l in open(C + '/census-receipt.txt').read().splitlines() if '=' in l and not l.startswith('tree='))
assert open(C + '/census-receipt.txt').read() == open(A + '/census-receipt-frame14.txt').read()
sc, ov, uw = (int(rec[k]) for k in ('implicit_close_scope_exit', 'implicit_close_overwrite', 'implicit_close_unwind'))
assert (sc, ov, uw) == (18, 0, 0)
assert rec['implicit_close_sources'] == 'box-drops:7,return-certificate:9,field-transaction:2'
assert rec['implicit_close_box_share_unpublished'] == 'brotli:error'
CMD4 = ('command: grep \'^implicit_close\' scratch/main/frame14/census-receipt.txt (byte-identical '
        'to agents/artifacts/2026-10-06-main-179b/census-receipt-frame14.txt): implicit_close_scope_exit=18 '
        'overwrite=0 unwind=0; sources box-drops 7 + return-certificate 9 + field-transaction 2; by program '
        'buffer 1, quadtree 15, lodepng 2; implicit_close_box_share_unpublished=brotli:error, so brotli\'s share is '
        'not in the count (as at 55); panic strategy abort. The waiver-drop receipts (addendum 101), counted per '
        'kind; the same values as 55\'s census. ')
stage('waiver.leak-parity', str(sc + ov + uw), 'delivered', 'count',
      CMD4 + 'This key: all implicit closes (scope-exit + overwrite + unwind).', 'analysis-fanout 062 / 041 (the existing rows)')
stage('waiver.leak-parity-overwrite', str(ov), 'delivered', 'count', CMD4 + 'This key: overwrite.', 'analysis-fanout 062 / 041')
stage('waiver.leak-parity-scope', str(sc), 'delivered', 'count', CMD4 + 'This key: scope-exit.', 'analysis-fanout 062 / 041')
stage('waiver.leak-parity-unwind', str(uw), 'delivered', 'count', CMD4 + 'This key: unwind.', 'analysis-fanout 062 / 041')

# ---- 5. RQ1's six shipped suites (frame14-six-suites.tsv) -------------------------------------------------
six = list(csv.DictReader(open(A + '/frame14-six-suites.tsv'), delimiter='\t'))
assert [r['program'] for r in six] == ['libtree', 'rgba', 'quadtree', 'buffer', 'genann', 'urlparser']
CMD5 = ('source: agents/artifacts/2026-10-06-main-179b/frame14-six-suites.tsv / .txt (main 179b §4; R818-1: the six '
        'shipped suites on the emitted tree of the frame census, main\'s line stating per program the shipped suite '
        'and how it ran); command: build_stage.py reads the emitted_verdict / c_verdict / runs columns. ')
passed = 0
for r in six:
    p = r['program']
    ev, cv = r['emitted_verdict'], r['c_verdict']
    assert ev.startswith('pass (') , (p, ev)
    passed += 1
    stage(f'rq1.tests.{p}.pass', 'pass', 'delivered', 'text (the suite\'s own verdict on the emitted tree)',
          CMD5 + f'{p}: {r["shipped_suite"]}; run as {r["how_run"]}; emitted {ev}; stdout equals C {r["emitted_stdout_equals_c"]}. '
          'THE PAPER\'S TEST KEY (R818-1).', 'R818-1; main 134c / 179b §4')
    if p == 'urlparser':
        assert cv.startswith('FAIL') and 'test=-6' in cv
        cval = 'abort'
        cnote = (f'C {cv}: {r["note"]}')
    else:
        assert cv.startswith('pass ('), (p, cv)
        cval = 'pass'
        cnote = f'C {cv}.'
    stage(f'rq1.tests.{p}.c-pass', cval, 'n/a', 'text (the suite\'s own verdict on the C original)',
          CMD5 + f'{p}: {cnote} This key: the same suite\'s verdict on the C original.', 'R818-1')
lt = six[0]
assert lt['emitted_stdout_equals_c'] == '9/9' and len(lt['runs'].split(',')) == 9
stage('rq1.tests.libtree.suite-size', '9', 'n/a', 'count',
      CMD5 + 'libtree: nine test directories under libtree-3.1.1/c/tests/ (each a Makefile check target), run 9/9 '
      '(test-01 .. test-08, test-10); /bin/ls is no longer a tenth run in main\'s line. Confirms main 134c\'s 9. '
      'This key: the number of tests in the shipped suite.', 'R818-1 (the existing row)')
stage('rq1.tests.suites.passed', str(passed), 'n/a', 'count',
      CMD5 + f'Of the six, the programs whose emitted tree passes its whole shipped suite: {passed} / 6 (frame14-six-suites.txt: '
      '\'six_suites: 6/6 pass on the emitted tree\'). The C originals: 5 / 6 (urlparser\'s C aborts on its own '
      'heap overflow under _FORTIFY_SOURCE=3).', 'R818-1 (the existing row)')
stage('rq1.tests.suites.programs', '6', 'n/a', 'count',
      CMD5 + 'The programs that ship a test suite (libtree, rgba, quadtree, urlparser, genann, buffer); unchanged.',
      'R818-1 (the existing row)')

# ---- 6. the loop-bound keys of 068 (no recomputation; the census read the same cache entries) ------------
fp = {}
for l in open(C + '/per-program.kv'):
    m1 = re.search(r'raw_boundary_cache_fingerprint=([0-9a-f]{64})', l); m2 = re.search(r' program=(\S+)', l)
    fp[m2.group(1)] = m1.group(1)
rec067 = {r['program']: r['key'] for r in csv.DictReader(open(
    'docs/agents/artifacts/2026-10-06-analysis-fanout-067/records.tsv'), delimiter='\t')}
assert len(fp) == 20 and len(rec067) == 19 and all(fp[p] == rec067[p] for p in rec067)
SOLVE = 'worktrees/era5c-l01p14-restored-solve/cache/era5b-model-cache-v1/'
assert all(os.path.exists(SOLVE + h + '.json') for h in fp.values())
vb = next(json.loads(l) for l in open('docs/agents/artifacts/2026-10-06-analysis-fanout-067/vread.jsonl') if '"brotli"' in l)
assert vb['program'] == 'brotli' and vb['bytes'] == os.path.getsize(SOLVE + fp['brotli'] + '.json') == 8555623927
CMD6 = ('NOT recomputed (relay 095 item 1: the loop-bound keys of 068). Confirmation that the frame census read the '
        'solve 068 / 067 read: frame14/per-program.kv raw_boundary_cache_fingerprint equals 067 records.tsv\'s key for '
        'all nineteen programs there, every one of the twenty fingerprints is an entry of '
        'worktrees/era5c-l01p14-restored-solve/cache/era5b-model-cache-v1/, and brotli\'s entry '
        '(35d2d2d1...) is 8,555,623,927 bytes = 067 vread.jsonl\'s brotli bytes; cache_manifest_sha256 e8c0eeb4... on '
        'all twenty (command: build_stage.py section 6). ')
for k in ('analysis.rounds.max', 'analysis.rounds.per-program', 'analysis.guarded.fallbacks', 'analysis.guarded.cap',
          'analysis.guarded.cap.per-program', 'analysis.unknown-solves', 'analysis.pins.programs'):
    line = next(l for l in NOR.splitlines() if l.startswith(f'| {k} |'))
    cells = [c.strip() for c in line.strip().strip('|').split('|')]
    v, layer, unit, prov = cells[1], cells[3], cells[4], cells[5]
    assert prov.startswith('provisional: analysis-fanout 068')
    body = prov[len('provisional: '):].replace(' Of record when the frame lands (R822-1, R844-1);', ' Of record with the frame (R822-1, R844-1);')
    stage(k, v, layer, unit, CMD6 + body, 'analysis-fanout 068 (relay 090; R844-1) from 067 (relay 088)')

json.dump(rows, open(HERE + '/stage.json', 'w'), indent=1, ensure_ascii=False)
for r in rows:
    print(f"{r['key']}\t{r['was']!r} -> {r['value']!r}")
print(len(rows), 'rows')
