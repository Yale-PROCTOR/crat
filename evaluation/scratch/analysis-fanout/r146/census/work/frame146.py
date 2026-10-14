"""frame146.py -- analysis-fanout r146 / census (relay 146): ONE switch for every re-pointed producer.

FRAME=s39   -> the CONTROL: main/batch58pps39 (58'''), code 3eaf5228d, the S39 cache (era5c-r211-s39pp);
               the outputs must reproduce r141/census/staged.tsv value_58ppp.
FRAME=60sp  -> 60s' (the final frame): main/batch60sp, code 32d966b9f, era-5c's 60-KINDORDER cache (era5c-r215-kindorder).

THE COUNT OF RECORD IS BY THE EMITTED TREE (relay 141): a subject the outcome ledger counts delivered but whose
program's delivery custody keeps raw is NOT delivered. TREE_EXCL is that set (4 at 58''', 0 at 60s'); tree-only rows
must be empty (fail closed otherwise). Every check raises SystemExit (never assert)."""
import glob
import json
import os

FRAME = os.environ.get('FRAME')
if FRAME not in ('s39', '60sp'):
    raise SystemExit('frame146: set FRAME=s39 (control) or FRAME=60sp (60s\'), got %r' % FRAME)

MAIN = 'scratch/main'
AW = 'dev/worktrees'
CFG = {
    's39': dict(TAG='b58ppp', CEN='batch58pps39', HEAD='3eaf5228d', HEADFULL='3eaf5228d',
                SOLVE=AW + '/era5c-r211-s39pp', ANALYSES='2c6824c70',
                DELIV=2678, DELIV_LEDGER=2682, UNIV=4301, WH=915, DEN=3386, SAFE_RAW=4337,
                HOLDS=('248', '263', '403', '1')),
    '60sp': dict(TAG='b60sp', CEN='batch60sp', HEAD='32d966b9f', HEADFULL='32d966b9fc2ef56fcd40e95ee762f73b0e0be70a',
                 SOLVE=AW + '/era5c-r215-kindorder', ANALYSES='a5495bf59',
                 DELIV=2715, DELIV_LEDGER=2715, UNIV=4530, WH=918, DEN=3612, SAFE_RAW=4566,
                 HOLDS=('251', '262', '404', '1')),
}[FRAME]
TAG = CFG['TAG']
C = MAIN + '/' + CFG['CEN']
SOLVE = CFG['SOLVE']
CACHE = SOLVE + '/cache/era5b-model-cache-v1'
OUTROOT = 'scratch/analysis-fanout/r146/census/work'


def tree_excl(census=None):
    """{(program, subject_key)}: ledger-only rows of the delivery custody (raw in the emitted tree)."""
    D = census or C
    ex, tree_only, unread = set(), [], []
    for f in sorted(glob.glob(D + '/*.raw-boundary-delivery-custody.json')):
        p = os.path.basename(f).split('.raw-boundary')[0]
        try:
            c = json.load(open(f))['comparison']
        except Exception:
            unread.append(p)
            continue
        led, tree = set(c.get('delivered_by_ledger') or []), set(c.get('delivered_by_tree') or [])
        ex |= {(p, k) for k in led - tree}
        tree_only += [(p, k) for k in tree - led]
    if unread:
        raise SystemExit('frame146: custody unreadable: %s' % unread)
    if tree_only:
        raise SystemExit('frame146: tree-only custody rows (not handled): %s' % tree_only)
    want = CFG['DELIV_LEDGER'] - CFG['DELIV']
    if len(ex) != want:
        raise SystemExit('frame146: %d ledger-only rows, expected %d' % (len(ex), want))
    return ex


EXCL = tree_excl()


def delivered(program, subject_key, delivery):
    return delivery == 'realized-as-predicted' and (program, subject_key) not in EXCL


def need(cond, msg):
    if not cond:
        raise SystemExit('FAIL: ' + str(msg))
