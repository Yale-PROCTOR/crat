#!/usr/bin/env python3
"""rq3/: Table miri (Miri under Tree Borrows on the five programs, for our translations and, given the third-party
outputs, Laertes's and CROWN's) and the shipped test suites run natively on the six.

  rq3.py native            the six shipped suites on the emitted trees, natively (harness/runtime_census.py)
  rq3.py miri <tool>       pass D on the five for one tool (ours | crown | laertes)
  rq3.py keys              results/rq3/keys.txt + results/tables/miri.{csv,tex}

Environment (set by the artifact's run.sh; defaults for a run from the unpacked source root):
  SRC          the translator's source root (benchmarks/crown/libtree/tests, deps_crate/)
  RESULTS      the results root (default $SRC/results)
  TREES        our emitted trees, one directory per program (default $RESULTS/trees)
  SUBSTRATE    the prepared inputs, one directory per program (default $RESULTS/substrate): the text the declared
               repairs are matched against in an output (an edit applies only where the output kept the input's text)
  THIRD_PARTY  the comparison tools' outputs (default $RESULTS/third-party): trees/crown/<p>/ (CROWN's output) and
               comparison/laertes-{crown,laertes}/after/<p>/ (the Laertes translations CROWN's artifact distributes)
  SMALL        1: genann's runs (ours and CROWN's) are skipped
  MIRI_CAP     seconds per Miri run (default 28800, eight hours)
  RQ3_OUT      this step's results (default $RESULTS/rq3)
  RQ3_JOBS     Miri processes at a time (default 1)
  MIRI_TOOLCHAIN  the rustup toolchain whose miri runs the programs (default nightly-2026-09-17)

Pass D = Miri with `-Zmiri-tree-borrows -Zmiri-disable-isolation -Zmiri-ignore-leaks`, panic=abort, the oracle
extents (a slice whose length the translation fabricated gets its real extent: harness/miri_oracle.py) and the
declared repairs of the input defects (repairs.tsv, applied identically to every tool's tree: harness/miri_repair.py).
"""
import concurrent.futures, csv, glob, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
RQ3 = os.path.dirname(HERE)
HARNESS = os.path.join(RQ3, 'harness')
REPAIRS = os.path.join(RQ3, 'repairs.tsv')
SRC = os.path.abspath(os.environ.get('SRC', os.getcwd()))
RESULTS = os.path.abspath(os.environ.get('RESULTS', os.path.join(SRC, 'results')))
TREES = os.path.abspath(os.environ.get('TREES', os.path.join(RESULTS, 'trees')))
THIRD_PARTY = os.path.abspath(os.environ.get('THIRD_PARTY', os.path.join(RESULTS, 'third-party')))
SMALL = os.environ.get('SMALL', '0') == '1'
CAP = int(os.environ.get('MIRI_CAP', '28800'))
JOBS = int(os.environ.get('RQ3_JOBS', '1'))
OUT = os.path.abspath(os.environ.get('RQ3_OUT', os.path.join(RESULTS, 'rq3')))
TABLES = os.path.join(RESULTS, 'tables')
os.environ.setdefault('SUBSTRATE', os.path.join(RESULTS, 'substrate'))

SIX = ['libtree', 'rgba', 'quadtree', 'urlparser', 'genann', 'buffer']     # the programs that ship a test suite
FIVE = ['buffer', 'genann', 'libtree', 'quadtree', 'rgba']                  # Table miri (urlparser: an input defect)
LONG = ('genann',)                                                          # ours to the eight-hour cap, CROWN's ~2 h
SKIP_SMALL = 'skipped (--small: 8 h cap)'
TOOLS = ('ours', 'crown', 'laertes')
LAERTES_SRC = {'genann': 'laertes-laertes'}                                 # the others: laertes-crown


def log(*a):
    print('rq3:', *a, flush=True)


def census(tool):
    return os.path.join(OUT, 'census', tool)


def link_trees():
    """Our trees as the harness reads them: <census>/emitted-trees/<p>."""
    d = os.path.join(census('ours'), 'emitted-trees')
    os.makedirs(d, exist_ok=True)
    for p in SIX:
        if os.path.isdir(os.path.join(TREES, p)):
            link = os.path.join(d, p)
            if os.path.lexists(link):
                os.remove(link)
            os.symlink(os.path.join(TREES, p), link)


def native():
    """The six suites, natively, on our emitted trees (the C originals too where $THIRD_PARTY carries them)."""
    link_trees()
    sys.path.insert(0, HARNESS)
    import runtime_census as rc
    inputs = {'test'} | {r[0] for r in rc.PROGRAMS['libtree']['runs'] if r[2][:1] == ['@sh']}
    work = os.path.join(OUT, 'native')
    progs = [p for p in SIX if os.path.isdir(os.path.join(TREES, p))]
    cmd = [sys.executable, os.path.join(HARNESS, 'runtime_census.py'), census('ours'), work,
           '--programs', ','.join(progs), '--inputs', ','.join(sorted(inputs))]
    with open(os.path.join(OUT, 'native.log'), 'w') as f:
        subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT)
    with open(os.path.join(OUT, 'native-suites.txt'), 'w') as f:
        subprocess.run([sys.executable, os.path.join(HARNESS, 'six_suites.py'), work,
                        os.path.join(OUT, 'native-suites.tsv')], stdout=f, stderr=subprocess.STDOUT)
    log('native:', open(os.path.join(OUT, 'native-suites.txt')).readline().strip())


def third_party_trees(tool):
    """Their outputs flattened into one crate root per program, as ours are (lib/flatten.py, a declared harness
    edit: every `pub mod X;` is inlined, nothing else changes). -> {program: status text or None}"""
    d = os.path.join(census(tool), 'emitted-trees')
    os.makedirs(d, exist_ok=True)
    status = {}
    for p in FIVE:
        src = (os.path.join(THIRD_PARTY, 'trees', 'crown', p) if tool == 'crown' else
               os.path.join(THIRD_PARTY, 'comparison', LAERTES_SRC.get(p, 'laertes-crown'), 'after', p))
        dst = os.path.join(d, p)
        if not os.path.isdir(src):
            status[p] = 'absent'
            continue
        shutil.rmtree(dst, ignore_errors=True)
        q = subprocess.run([sys.executable, os.path.join(HERE, 'flatten.py'), src, dst], capture_output=True, text=True)
        status[p] = None if q.returncode == 0 and os.path.exists(os.path.join(dst, 'lib.rs')) else 'no crate root'
    return status


def miri_one(tool, p):
    work = os.path.join(OUT, 'miri', tool)
    os.makedirs(work, exist_ok=True)
    logf = os.path.join(work, f'{p}.log')
    env = dict(os.environ)
    with open(logf, 'w') as f:
        if p == 'libtree':
            env['JOBCRAT_MIRI_REPAIRS'] = REPAIRS
            cmd = [sys.executable, os.path.join(HARNESS, 'libtree_suite.py'), census(tool), work, 'D', 'emitted']
        else:
            cmd = [sys.executable, os.path.join(HARNESS, 'miri_census.py'), census(tool), work, '--programs', p,
                   '--discipline', 'TB', '--variant', 'emitted', '--timeout', str(CAP),
                   '--oracle', '--repair', REPAIRS]
            if p == 'genann':
                cmd[cmd.index('--programs') + 2:cmd.index('--programs') + 2] = ['--inputs', 'test']
        subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env)
    log(f'miri {tool} {p}: done')


def miri(tool):
    if tool == 'ours':
        link_trees()
        status = {p: (None if os.path.isdir(os.path.join(TREES, p)) else 'absent') for p in FIVE}
    else:
        status = third_party_trees(tool)
    todo = [p for p in FIVE if status[p] is None and not (SMALL and p in LONG and tool != 'laertes')]
    with open(os.path.join(OUT, f'miri-{tool}-status.tsv'), 'w') as f:
        for p in FIVE:
            f.write(f'{p}\t{status[p] or "run"}\n')
    with concurrent.futures.ThreadPoolExecutor(max_workers=JOBS) as ex:
        list(ex.map(lambda p: miri_one(tool, p), todo))


# ------------------------------------------------------------------------------------------------- keys

COMPILE = re.compile(r'rustc --explain E\d+|could not compile|error\[E\d+\]')


def runs_of(tool, p):
    """-> list of (input, first-report class, detail) for one program, or a status text."""
    work = os.path.join(OUT, 'miri', tool)
    if p == 'libtree':
        f = os.path.join(work, 'libtree-D-emitted.tsv')
        if not os.path.exists(f):
            return None
        rows = []
        for r in csv.DictReader(open(f), delimiter='\t'):
            rep = r['first_report']
            if r['make_exit'] == 'timeout':
                cls = 'timeout'
            elif rep == '-':
                cls = 'pass' if r['make_exit'] == '0' else 'error'   # a failed test with no Miri report
            else:
                cls = rep.split(':', 1)[0]
            rows.append((r['input'], cls, rep))
        return rows
    f = os.path.join(work, p, 'miri-runs-emitted-TB.tsv')
    if not os.path.exists(f):
        return None
    return [(r['input'], r['first_report'], r['detail']) for r in csv.DictReader(open(f), delimiter='\t')]


def cell(tool, p, status):
    """-> (runs, ub) as the table prints them."""
    if SMALL and p in LONG and tool != 'laertes':
        return SKIP_SMALL, SKIP_SMALL
    if status.get(p) == 'absent':
        why = 'skipped (no third-party outputs)' if tool != 'ours' else 'skipped (no tree)'
        return why, why
    if status.get(p) == 'no crate root':
        return '—', 'no crate root'
    rows = runs_of(tool, p)
    if rows is None:
        lf = os.path.join(OUT, 'miri', tool, f'{p}.log')
        if os.path.exists(lf) and 'no main_0 in' in open(lf, errors='replace').read():
            return '—', 'no main'      # the test's module has no main function (the harness cannot drive it)
        return '—', 'not run'
    if any(c == 'other' and COMPILE.search(d or '') for _, c, d in rows):
        return '—', 'does not compile'
    if any(c == 'error' or (c == 'other' and (d or '').startswith('exit ')) for _, c, d in rows):
        return 'error', 'error'    # Miri exited without a report: the run did not happen (e.g. no sysroot)
    ub = sum(1 for _, c, d in rows if (d or '').startswith('Undefined Behavior') or
             (c not in ('pass', 'timeout', 'other', 'unsupported') and not (d or '').startswith('abnormal')))
    aborts = sum(1 for _, c, d in rows if c == 'unsupported' or (d or '').startswith('abnormal termination'))
    if ub == 0 and aborts:
        return str(len(rows)), 'aborts'
    return str(len(rows)), str(ub)


def status_of(tool):
    f = os.path.join(OUT, f'miri-{tool}-status.tsv')
    if not os.path.exists(f):
        return {p: 'absent' for p in FIVE}
    return dict(l.rstrip('\n').split('\t') for l in open(f) if '\t' in l)


def native_verdicts():
    f = os.path.join(OUT, 'native-suites.tsv')
    if not os.path.exists(f):
        return {}
    return {r['program']: r['emitted_verdict'] for r in csv.DictReader(open(f), delimiter='\t')}


def tex_escape(s):
    return (s.replace('\\', r'\textbackslash{}').replace('%', r'\%').replace('&', r'\&').replace('#', r'\#')
            .replace('_', r'\_').replace('^', r'\^{}').replace('~', r'\textasciitilde{}').replace('{', r'\{')
            .replace('}', r'\}'))


def keys():
    v = {}
    nat = native_verdicts()
    ran = [p for p in SIX if nat.get(p, '').startswith(('pass', 'FAIL'))]
    v['rq1.tests.suites.programs'] = str(len(ran)) if nat else 'skipped (the native run has not been made)'
    for p in SIX:
        v[f'rq4.native.{p}.suite'] = nat.get(p, 'not run').split(' ')[0] if nat else 'not run'
    table = []
    for p in FIVE:
        row = [p]
        for tool in ('laertes', 'crown', 'ours'):
            runs, ub = cell(tool, p, status_of(tool))
            pre = 'rq4.suite' if tool == 'ours' else f'rq4.suite.{tool}'
            v[f'{pre}.{p}.runs'] = runs
            v[f'{pre}.{p}.ours' if tool == 'ours' else f'{pre}.{p}.ub'] = ub
            row += [runs, ub]
        table.append(row)
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(TABLES, exist_ok=True)
    with open(os.path.join(OUT, 'keys.txt'), 'w') as f:
        for k in sorted(v):
            f.write(f'{k} = {v[k]}\n')
    with open(os.path.join(TABLES, 'miri.csv'), 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['program', 'laertes_runs', 'laertes_ub', 'crown_runs', 'crown_ub', 'ours_runs', 'ours_ub'])
        w.writerows(table)
    with open(os.path.join(TABLES, 'miri.tex'), 'w') as f:
        f.write("% miri: the produced keys in the paper's numbers.tex form (skipped keys are absent)\n")
        for k in sorted(v):
            if k.startswith(('rq4.suite.', 'rq1.tests.')) and not v[k].startswith('skipped'):
                f.write(f'\\@namedef{{nr@{k}}}{{\\nrMeasured{{{tex_escape(v[k])}}}}}\n')
    log(f'keys: {len(v)} -> {os.path.join(OUT, "keys.txt")}')


if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'native':
        native()
    elif cmd == 'miri' and len(sys.argv) > 2 and sys.argv[2] in TOOLS:
        miri(sys.argv[2])
    elif cmd == 'keys':
        keys()
    else:
        sys.exit(__doc__)
