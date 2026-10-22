#!/usr/bin/env python3
"""third-party step `tables`: the comparison tools' times and statuses, and the checks of what was fetched.

Writes, under $THIRD_PARTY:
  times.tsv  key<TAB>trials<TAB>min<TAB>status, one row per program and tool (rq2 reads it; the value of a key is
             `min` when it is set, else `status`):
               rq3.<p>.crown-s                CROWN, the three calls' wall (GNU time), min over trials
               rq3.<p>.laertes-s              Laertes in the mode of record (emulation), min over trials; `crash` when
                                              the tool does not complete (the record's word)
               rq3.<p>.laertes-own-mode       Laertes without the emulation: `ok` | `stops` (one trial)
               rq3.inator.<q>.host-s          &inator's own phase timers (times.txt), min over completed trials
               rq3.inator.<q>.c2rust-s        c2rust 0.21.0-p1's `transpile` wall, min over trials whose output equals
                                              the translation of record
             Totals are not written here (rq2 derives them). Programs not run are absent.
  check.txt  the trees and inputs against the record: CROWN's output trees and the artifact's comparison/ against
             expected-trees.tsv (beside third-party/ in the artifact), &inator's outputs present, c2rust's identity.
             CROWN's analysis_results/{ownership,mutability,fatness}.json are maps written in hash order, so their
             bytes differ from trial to trial. expected-trees.tsv's third column is the sha256 of the record's file
             as json.dumps(obj, sort_keys=True, separators=(",", ":")): such a file is `equal (content)` when that
             digest matches."""
import hashlib, json, os, re, sys

T = os.path.abspath(os.environ['THIRD_PARTY'])
HOME = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TWENTY = os.environ['TWENTY'].split()
EIGHT = os.environ['EIGHT'].split()


def key_of(p):
    return 'jsonh' if p == 'json.h' else p


def wall(path):
    try:
        t = open(path).read()
    except OSError:
        return None
    m = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)', t)
    if not m:
        return None
    s = 0.0
    for x in m.group(1).split(':'):
        s = s * 60 + float(x)
    return s


def kv(path):
    d = {}
    if os.path.exists(path):
        for l in open(path):
            for part in l.split():
                if '=' in part:
                    k, v = part.split('=', 1)
                    d[k] = v
    return d


def trial_dirs(base):
    if not os.path.isdir(base):
        return []
    return [os.path.join(base, x) for x in sorted(os.listdir(base), key=lambda s: int(s[1:])) if re.match(r'^t\d+$', x)]


rows = []


def row(key, walls, status):
    walls = [w for w in walls if w is not None]
    rows.append((key, ','.join('%.2f' % w for w in walls), '%.2f' % min(walls) if walls and status == 'ok' else '',
                 status))


for p in TWENTY:
    k = key_of(p)
    ts = trial_dirs(os.path.join(T, 'crown', 'runs', p))
    if ts:
        ok = [t for t in ts if kv(os.path.join(t, 'status')).get('exit') == '0']
        row(f'rq3.{k}.crown-s', [wall(os.path.join(t, 'time.txt')) for t in ok], 'ok' if len(ok) == len(ts) else 'crash')
    ts = trial_dirs(os.path.join(T, 'laertes', 'runs', 'emulate', p))
    if ts:
        ok = [t for t in ts if kv(os.path.join(t, 'status')).get('complete') == '1']
        row(f'rq3.{k}.laertes-s', [wall(os.path.join(t, 'time.txt')) for t in ok], 'ok' if ok and len(ok) == len(ts) else 'crash')
    ts = trial_dirs(os.path.join(T, 'laertes', 'runs', 'noemulate', p))
    if ts:
        c = kv(os.path.join(ts[0], 'status')).get('complete') == '1'
        rows.append((f'rq3.{k}.laertes-own-mode', '', '', 'ok' if c else 'stops'))

for q in EIGHT:
    ts = trial_dirs(os.path.join(T, 'inator', 'runs', q))
    if ts:
        sums = []
        for t in ts:
            f = os.path.join(t, 'results', 'times.txt')
            if kv(os.path.join(t, 'meta.txt')).get('exit_code') == '0' and os.path.exists(f):
                sums.append(sum(int(x) for x in open(f).read().split()[:3]) / 1e9)
        row(f'rq3.inator.{q}.host-s', sums, 'ok' if sums else 'crash')
    ts = trial_dirs(os.path.join(T, 'c2rust', 'runs', q))
    if ts:
        good = [t for t in ts if kv(os.path.join(t, 'meta.txt')).get('exit_code') == '0'
                and re.search(r'^ident identical=(\d+)/\1$', open(os.path.join(t, 'meta.txt')).read(), re.M)]
        row(f'rq3.inator.{q}.c2rust-s', [wall(os.path.join(t, 'inner.time')) for t in good],
            'ok' if len(good) == len(ts) else 'differs from the translation of record')

with open(os.path.join(T, 'times.tsv'), 'w') as f:
    f.write('key\ttrials\tmin\tstatus\n')
    for r in rows:
        f.write('\t'.join(r) + '\n')

# ---- checks
out = []
exp_path = os.path.join(os.path.dirname(HOME), 'expected-trees.tsv')
if os.path.exists(exp_path):
    exp = [(l.rstrip('\n').split('\t') + [''])[:3] for l in open(exp_path) if l.strip()]
    groups = {}
    for path, h, canon_h in exp:
        g = 'trees/crown/' + path.split('/')[2] if path.startswith('trees/crown/') else path.split('/')[0]
        if path == 'crown/evaluation.csv' and os.environ.get('SMALL') == '1':
            continue   # CROWN's table covers the twenty: a full run only
        if g.startswith('trees/crown/') and not os.path.isdir(os.path.join(T, 'trees', 'crown', path.split('/')[2])):
            continue   # not run (--small, or CROWN did not complete)
        f = os.path.join(T, path)
        if not os.path.exists(f):
            v = 'missing'
        elif hashlib.sha256(open(f, 'rb').read()).hexdigest() == h:
            v = 'equal'
        elif canon_h:
            c = json.dumps(json.load(open(f)), sort_keys=True, separators=(',', ':'))
            v = 'equal (content)' if hashlib.sha256(c.encode()).hexdigest() == canon_h else 'differs'
        else:
            v = 'differs'
        groups.setdefault(g, {}).setdefault(v, []).append(path)
    for g in sorted(groups):
        c = groups[g]
        out.append('%-40s %s' % (g, ', '.join('%s %d' % (v, len(c[v])) for v in ('equal', 'equal (content)', 'differs', 'missing') if v in c)))
        for v in ('differs', 'missing'):
            for path in c.get(v, [])[:20]:
                out.append('    %s %s' % (v, path))
else:
    out.append('expected-trees.tsv not found (%s): trees not checked' % exp_path)
ev = os.path.join(T, 'crown', 'evaluation.csv')
out.append('crown/evaluation.csv: %s' % ('present' if os.path.exists(ev) else 'absent (written by a full run only)'))
for q in EIGHT:
    d = os.path.join(T, 'inator', q)
    if os.path.isdir(os.path.join(T, 'inator', 'runs', q)):
        out.append('inator/%s: %s' % (q, 'rtypes.txt + stypes.txt' if os.path.exists(os.path.join(d, 'rtypes.txt')) else 'no output'))
for q in EIGHT:
    for t in trial_dirs(os.path.join(T, 'c2rust', 'runs', q)):
        m = re.search(r'^ident (.*)$', open(os.path.join(t, 'meta.txt')).read(), re.M)
        out.append('c2rust/%s/%s: %s' % (q, os.path.basename(t), m.group(1) if m else 'no identity line'))
ad = os.path.join(T, 'laertes', 'inputs', 'ADAPTATION.tsv')
if os.path.exists(ad):
    same = open(ad).read() == open(os.path.join(HOME, 'laertes', 'ADAPTATION.tsv')).read()
    out.append("laertes/inputs: header adaptation %s the record's" % ('=' if same else 'DIFFERS from'))
open(os.path.join(T, 'check.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
print('times.tsv: %d rows' % len(rows))
