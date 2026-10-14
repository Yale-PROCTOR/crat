#!/usr/bin/env python3
"""analysis-fanout 017 (relays 022/023, R674-3): RQ3's crat side on host-a.

  rq3_trials.py pilot            the bst equivalence receipt: S2 on rs-crown-derived/bst under the L01^9
                                 identity env + launch digest bb6d8ed1 must reproduce the worker of record's
                                 entry (key / payload / exports); then the census child once on that entry
  rq3_trials.py prep PROG        substrate once (the input of S1/S2/census), S2 once (the entry), its digests,
                                 the manifest and exposure rows
  rq3_trials.py trial PROG N     one timed trial: substrate, S1, census child (each /usr/bin/time -v)
  rq3_trials.py run [PROG...]    prep + trials 1..5 (one stated trial when a stage exceeds 600 s), serially

The identity env is the worker of record's own job environment (jobs/bst.json, 42 variables), with the per-program
variables replaced; TMPDIR and the cache are this lane's. analysis-s = substrate + S1; emit-s = census child.
Every timed process is preceded by a window check (no corpus lock, no L01^11 solve process, MemAvailable >= 60 GiB,
no main/batch* table younger than 30 min); the state at each start goes into the row.
"""
import glob, hashlib, json, os, re, shutil, subprocess, sys, time

R = 'scratch/analysis-fanout/rq3'          # inputs (c2rust-out) and tools
# relay 026: the final-frame run takes its own output root, binaries, frame and solve by env; defaults = the 018 dry run
OUT = os.environ.get('RQ3_OUT', R)
BIN = os.environ.get('RQ3_BIN', f'{R}/bin/pointer_replacer-4feea9176-release')
CRAT = os.environ.get('RQ3_CRAT', f'{R}/bin/crat-4feea9176-release')
FRAME = os.environ.get('RQ3_FRAME', '4feea9176a932a28b212cd71554a8279a141199f')
SOLVE = os.environ.get('RQ3_SOLVE', 'worktrees/era5c-l01p9-night-solve')
IDLE = os.environ.get('RQ3_IDLE') == '1'   # the citable run: an idle hour (R690-6)
JOB = f'{SOLVE}/jobs/bst.json'
LOCK = 'worktrees/CORPUS-SLOT.lock'
SYSROOT = 'home/.rustup/toolchains/nightly-2025-06-23-x86_64-unknown-linux-gnu'
NINE = ['running-example', 'ulidgen', 'leftpad', 'amp', 'nandc', 'rbtree', 'carrays', 'jccc', 'tisp']
TSV = f'{OUT}/rq3-trials.tsv'
COLS = ['program', 'trial', 'stage', 'wall_s', 'wall_hr_s', 'max_rss_kb', 'exit', 'load1', 'load5', 'load15', 'mem_avail_gib',
        'beside', 'input_sha256', 'binary_sha256', 'code_frame', 'launch_digest', 'configuration', 'started_utc', 'note']
S1_TEST = 'analyses::borrow_ownership::null_paths_tests::e5c_inner_solve_named_source'
DIGEST_TEST = 'analyses::borrow_ownership::null_paths_tests::e5c_entry_digests'
WORKER = 'bo_c1::boc1_run_one'
TEST_ARGS = ['--exact', '--ignored', '--nocapture', '--test-threads=1']
os.makedirs(f'{OUT}/logs', exist_ok=True)


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def tree_sha(root):
    h = hashlib.sha256()
    for dp, dn, fn in sorted(os.walk(root)):
        dn[:] = sorted(d for d in dn if d != 'target')
        for n in sorted(fn):
            p = os.path.join(dp, n)
            h.update(os.path.relpath(p, root).encode() + b'\0' + sha(p).encode() + b'\n')
    return h.hexdigest()


def job_env():
    # relay 145 (host-a run of a host-b solve job): the host's z3 library path is outside the identity (era-5c 172b);
    # map host-b's z3 directory to host-a's, nothing else
    e = dict(json.load(open(JOB))['environment'])
    e['LD_LIBRARY_PATH'] = e.get('LD_LIBRARY_PATH', '').replace('dev/host-b/z3/z3-4.15.4-x64-glibc-2.39/bin',
                                                              'home/.local/opt/z3-solver-4.15.4.0/z3/lib')
    return e


def identity_env(prog, input_root, launch):
    e = {'HOME': os.environ['HOME'], 'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8'}
    e.update(job_env())
    os.makedirs(f'{OUT}/tmp', exist_ok=True)
    e.update({'CRAT_ERA5_PROGRAM': prog, 'CRAT_ERA5_INPUT_ROOT': input_root, 'CRAT_ERA5_LAUNCH_DIGEST': launch,
              'TMPDIR': f'{OUT}/tmp', 'DIR': 'crat'})
    return e


def launch_digest_nine():
    """016 STOP 2(b), recommended: a launch manifest of the nine with the frame's pins; its sha256 is the launch
    digest (identity only; the solver semantics are the frame's)."""
    p = f'{OUT}/rq3-launch-manifest.json'
    if not os.path.exists(p):
        j = json.load(open(JOB))
        doc = {'schema': 'analysis-fanout-rq3-launch-v1', 'frame': os.path.basename(SOLVE.rstrip('/')).replace('-night-solve', '') + '-v1', 'code_frame': FRAME,
               'semantic': j['semantic'], 'programs': NINE,
               'note': 'RQ3 comparison-only corpus (R667-1); the twenty\'s launch digest bb6d8ed1 is not claimed'}
        open(p, 'w').write(json.dumps(doc, indent=1, sort_keys=True) + '\n')
    return sha(p)


def meminfo_gib():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'):
            return int(l.split()[1]) / 1048576


def beside():
    """Other heavy processes at the moment (RSS > 1 GiB), by executable basename; read from /proc, never pgrep."""
    out = []
    for pid in os.listdir('/proc'):
        if not pid.isdigit() or int(pid) == os.getpid():
            continue
        try:
            st = open(f'/proc/{pid}/status').read()
            rss = int(re.search(r'VmRSS:\s+(\d+)', st).group(1))
            exe = open(f'/proc/{pid}/cmdline', 'rb').read().split(b'\0')[0].decode(errors='replace')
        except (OSError, AttributeError):
            continue
        if rss > 1048576 and 'assistant' not in exe:
            out.append(f'{os.path.basename(exe)}:{rss // 1048576}G')
    return ','.join(sorted(out)) or 'none'


def big_census_child():
    """A census child on lil or brotli (read from /proc/<pid>/environ, same user; never pgrep)."""
    for pid in os.listdir('/proc'):
        if not pid.isdigit():
            continue
        try:
            env = open(f'/proc/{pid}/environ', 'rb').read().split(b'\0')
        except OSError:
            continue
        if b'CRAT_BOC1_NAME=lil' in env or b'CRAT_BOC1_NAME=brotli' in env:
            return True
    return False


def window_ok():
    """Relay 024 (R682-1): no era-5c solve (lock or process); beside a census only on its small programs;
    MemAvailable >= 60 GiB after this lane's need (<= 5 GiB for these programs)."""
    if os.path.exists(LOCK) and '"lane":"era-5c"' in open(LOCK).read():
        return False, 'era-5c solve lock'
    if subprocess.run(['python3', f'{R}/solve_busy.py'], capture_output=True, text=True).stdout.strip() != '0':
        return False, 'solve process'
    if big_census_child():
        return False, 'a lil/brotli census child'
    if meminfo_gib() < (100 if IDLE else 65):
        return False, f'MemAvailable {meminfo_gib():.0f} GiB'
    if IDLE:
        # relay 109: never beside any corpus run (main's 56 census, a hold census): no slot lock, no open census line
        if glob.glob('worktrees/CORPUS-SLOT*.lock'):
            return False, 'a corpus lock'
        cl = [l for l in open('scratch/main/SLOT-FREE') if re.match(r'^main .*CENSUS (STARTED|ENDED)', l)]
        if cl and 'STARTED' in cl[-1]:
            return False, 'an open census line'
        l1, l5 = (float(x) for x in open('/proc/loadavg').read().split()[:2])
        if l1 > 2.0 or l5 > 2.5:
            return False, f'not idle (load {l1} / {l5})'
        if beside() != 'none':
            return False, f'not idle ({beside()})'
    return True, 'ok'


def wait_window(max_wait=(24 if IDLE else 6) * 3600):
    t0 = time.time()
    while True:
        ok, why = window_ok()
        if ok:
            return
        if time.time() - t0 > max_wait:
            sys.exit(f'window never opened ({why})')
        print(f'  waiting for the window: {why}', flush=True)
        time.sleep(60)


def timed(cmd, env, tag, cwd=None):
    """Run cmd under /usr/bin/time -v; return (row fields, stdout, stderr)."""
    wait_window()
    tf = f'{OUT}/logs/{tag}.time'
    os.makedirs(os.path.dirname(tf), exist_ok=True)
    l1, l5, l15 = open('/proc/loadavg').read().split()[:3]
    start = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    row = {'load1': l1, 'load5': l5, 'load15': l15, 'mem_avail_gib': f'{meminfo_gib():.0f}', 'beside': beside(),
           'started_utc': start}
    t0 = time.monotonic()
    proc = subprocess.Popen(['/usr/bin/time', '-v', '-o', tf] + cmd, env=env, cwd=cwd, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=3600)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, 9)
        out, err = proc.communicate()
        rc = 'timeout-3600s'
    hr = time.monotonic() - t0

    class P: pass
    p = P(); p.stdout, p.stderr, p.returncode = out, err, rc
    open(f'{OUT}/logs/{tag}.out', 'w').write(p.stdout)
    open(f'{OUT}/logs/{tag}.err', 'w').write(p.stderr)
    t = open(tf).read() if os.path.exists(tf) else ''
    m = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', t)
    wall = sum(v * 60 ** i for i, v in enumerate(reversed([float(x) for x in m.group(1).split(':')]))) if m else hr
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', t)
    row.update({'wall_s': f'{wall:.3f}', 'wall_hr_s': f'{hr:.3f}', 'max_rss_kb': rss.group(1) if rss else '-',
                'exit': str(p.returncode)})
    return row, p.stdout, p.stderr


def append(row):
    new = not os.path.exists(TSV)
    with open(TSV, 'a') as f:
        if new:
            f.write('\t'.join(COLS) + '\n')
        f.write('\t'.join(str(row.get(c, '-')) or '-' for c in COLS) + '\n')


def substrate(prog, out):
    """crat --pass expand,extern,preprocess (the 2026-08-06 substrate, default configs) on the c2rust crate."""
    if os.path.exists(out):
        shutil.rmtree(out)
    os.makedirs(out)
    env = {'HOME': os.environ['HOME'], 'PATH': '/usr/bin:/bin', 'DIR': 'crat',
           'RUSTUP_TOOLCHAIN': 'nightly-2025-06-23-x86_64-unknown-linux-gnu', 'SYSROOT': SYSROOT,
           'LD_LIBRARY_PATH': f'{SYSROOT}/lib:{SYSROOT}/lib/rustlib/x86_64-unknown-linux-gnu/lib:home/.local/opt/z3-solver-4.15.4.0/z3/lib'}
    return [CRAT, '--pass', 'expand,extern,preprocess', '-o', out, f'{R}/c2rust-out/{prog}'], env


def entry_digests(entry, env):
    e = dict(env, CRAT_E5C_ENTRY=entry)
    p = subprocess.run([BIN, DIGEST_TEST] + TEST_ARGS, env=e, capture_output=True, text=True)
    m = re.search(r'E5C_ENTRY_DIGESTS (\{.*\})', p.stdout + p.stderr)
    if not m:
        sys.exit(f'entry digests failed: {p.stderr[-2000:]}')
    return json.loads(m.group(1))


def s2(prog, lib_rs, input_root, launch, cache):
    """S2: boc1_run_one in m1-diag, role derive, reads off, writes the entry during decide (untimed)."""
    if os.path.exists(cache):
        shutil.rmtree(cache)
    os.makedirs(cache)
    env = identity_env(prog, input_root, launch)
    env.update({'CRAT_BO_CACHE_DIR': cache, 'CRAT_BOC1_INPUT': lib_rs, 'CRAT_BOC1_MODE': 'm1-diag',
                'CRAT_BOC1_NAME': prog})
    env.pop('CRAT_BO_CACHE', None)
    p = subprocess.run([BIN, WORKER] + TEST_ARGS, env=env, capture_output=True, text=True)
    open(f'{OUT}/logs/{prog}.s2.out', 'w').write(p.stdout)
    open(f'{OUT}/logs/{prog}.s2.err', 'w').write(p.stderr)
    entries = glob.glob(f'{cache}/era5b-model-cache-v1/*.json')
    if len(entries) != 1:
        sys.exit(f'{prog}: S2 wrote {len(entries)} entries (exit {p.returncode}); see logs/{prog}.s2.err')
    return entries[0], entry_digests(entries[0], env)


def census_env(prog, input_root, launch, cache, fp, art):
    d = f'{OUT}/prep/{prog}'
    man, exp = f'{d}/manifest.tsv', f'{d}/exposure.tsv'
    open(man, 'w').write(f'program\tfingerprint\n{prog}\t{fp}\n')
    open(exp, 'w').write('program\tinput_version\tsource_provenance\tconfigured_name_count\tcanonical_names\t'
                         'canonical_names_sha256\tstatus\n'
                         f'{prog}\t1\tinator-rq3:explicit-empty\t0\t-\t'
                         'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\texplicit-empty\n')
    if os.path.exists(art):
        shutil.rmtree(art)
    os.makedirs(f'{art}/emitted-trees')
    env = identity_env(prog, input_root, launch)
    env.update({'CRAT_BO_CACHE': '1', 'CRAT_BO_CACHE_DIR': cache, 'CRAT_ERA5_EXECUTION_ROLE': 'cache-only',
                'CRAT_BOC1_MODE': 'raw-boundary-census', 'CRAT_BOC1_NAME': prog,
                'CRAT_BOC1_INPUT': f'{input_root}/lib.rs',
                'CRAT_RAW_BOUNDARY_CACHE_MANIFEST': man, 'CRAT_RAW_BOUNDARY_EXPOSURE_INPUT': exp,
                'CRAT_RAW_BOUNDARY_EXPOSURE_INPUT_SHA256': sha(exp),
                'CRAT_RAW_BOUNDARY_ARTIFACT_DIR': art, 'CRAT_RAW_BOUNDARY_EMITTED_TREE_DIR': f'{art}/emitted-trees',
                'CRAT_RAW_BOUNDARY_CODE_FRAME': FRAME, 'CRAT_RAW_BOUNDARY_CARGO_PROFILE': 'release',
                'CRAT_BOC1_MEM_MB': '49152', 'CRAT_BOC1_EFFECTIVE_MEM_MB': '49152', 'CRAT_BOC1_EMIT_TIMEOUT_SECS': '900'})
    return env


def kv(stdout):
    """The child's BOC1 row (space-separated key=value)."""
    rows = [l for l in stdout.splitlines() if 'raw_boundary_status=' in l]
    if not rows:
        return {}
    return dict(x.split('=', 1) for x in rows[-1].split() if '=' in x)


def loan_renaming_only(ours, record):
    """R690-6: the entry equal up to a one-to-one renaming of loan ids. Loan ids are numbered per function, so the
    renaming is checked per function (the function read from each diagnostic's source_key): every section but the
    loans diagnostics' `loan` labels equal, and within each function those labels map by a consistent bijection."""
    a, b = json.load(open(ours)), json.load(open(record))
    da, db = a['exports'].pop('diagnostics'), b['exports'].pop('diagnostics')
    if a != b or len(da) != len(db):
        return False
    maps = {}
    for x, y in zip(da, db):
        if x.get('source_key') != y.get('source_key') or x.get('family') != y.get('family'):
            return False
        lx = x['labels'].get('labels') if isinstance(x.get('labels'), dict) else None
        ly = y['labels'].get('labels') if isinstance(y.get('labels'), dict) else None
        if isinstance(lx, dict) and isinstance(ly, dict) and ('loan' in lx or 'loan' in ly):
            if x.get('family') != 'loans' or {k: v for k, v in lx.items() if k != 'loan'} != {k: v for k, v in ly.items() if k != 'loan'}:
                return False
            try:
                fn = json.loads(x['source_key'].split('/', 1)[1]).get('function')
            except (ValueError, IndexError):
                return False
            if maps.setdefault(fn, {}).setdefault(lx.get('loan'), ly.get('loan')) != ly.get('loan'):
                return False
        elif x != y:
            return False
    return all(len(set(m.values())) == len(m) for m in maps.values())


def pilot():
    j = json.load(open(JOB))
    w = json.load(open(f'{SOLVE}/workers/bst.json'))['completed']
    root = j['environment']['CRAT_ERA5_INPUT_ROOT']
    launch = j['environment']['CRAT_ERA5_LAUNCH_DIGEST']
    wait_window()
    entry, dg = s2('bst', f'{root}/lib.rs', root, launch, f'{OUT}/prep/bst/cache')
    want = {'key': w['key'], 'payload': w['payload_sha256'], 'exports': w['export_sha256'], 'entry': w['entry_sha256']}
    kp = dg.get('key') == want['key'] and dg.get('payload') == want['payload']
    same = dg.get('exports') == want['exports'] or (kp and loan_renaming_only(entry, w['cache_entry']))
    ok = kp and same
    rec = {'program': 'bst', 'frame': FRAME, 'solve': SOLVE, 'ours': dg, 'worker_of_record': want,
           'entry_file_sha256': sha(entry), 'key_payload_equal': kp, 'entry_equal_up_to_loan_renaming': same,
           'receipt (R690-6)': 'key + payload equal; the entry equal up to a one-to-one renaming of loan IDs',
           'holds': ok}
    os.makedirs(f'{OUT}/prep/bst', exist_ok=True)
    json.dump(rec, open(f'{OUT}/bst-equivalence-receipt.json', 'w'), indent=1)
    print(json.dumps(rec, indent=1))
    fp = os.path.basename(entry)[:-5]
    env = census_env('bst', root, launch, f'{OUT}/prep/bst/cache', fp, f'{OUT}/prep/bst/census')
    row, out, err = timed([BIN, WORKER] + TEST_ARGS, env, 'bst.census-pilot')
    k = kv(out)
    print('census pilot:', row['wall_s'], 's; rb', k.get('raw_boundary_status'), 'cache', k.get('raw_boundary_cache_status'),
          'outcome', k.get('raw_boundary_outcome_kind'), 'verify_rounds', k.get('raw_boundary_verify_rounds'),
          'delivery', k.get('raw_boundary_delivery'))
    return ok


def prep(prog):
    d = f'{OUT}/prep/{prog}'
    os.makedirs(d, exist_ok=True)
    cmd, env = substrate(prog, f'{d}/substrate')
    p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    open(f'{d}/substrate.log', 'w').write(p.stdout + p.stderr)
    root = f'{d}/substrate/{prog}'
    if p.returncode or not os.path.exists(f'{root}/lib.rs'):
        sys.exit(f'{prog}: substrate failed (exit {p.returncode}); {d}/substrate.log')
    rs = [f for f in glob.glob(f'{root}/**/*.rs', recursive=True) if not f.endswith('/build.rs')]
    launch = launch_digest_nine()
    entry, dg = s2(prog, f'{root}/lib.rs', root, launch, f'{d}/cache')
    inputs = json.load(open(entry))['inputs']
    info = {'program': prog, 'configuration': inputs.get('configuration'), 'analysis': inputs.get('analysis'),
            'substrate_tree_sha256': tree_sha(root), 'substrate_rs_files': len(rs),
            'lib_rs_sha256': sha(f'{root}/lib.rs'), 'launch_digest': launch, 'entry': entry, 'digests': dg}
    json.dump(info, open(f'{d}/prep.json', 'w'), indent=1)
    print(json.dumps(info, indent=1))


def trial(prog, n):
    d = f'{OUT}/prep/{prog}'
    info = json.load(open(f'{d}/prep.json'))
    root = f'{d}/substrate/{prog}'
    base = {'program': prog, 'trial': n, 'binary_sha256': sha(BIN)[:16], 'code_frame': FRAME[:9],
            'launch_digest': info['launch_digest'][:16], 'input_sha256': info['lib_rs_sha256'][:16],
            'configuration': (info.get('configuration') or '-')[:16]}
    walls = {}
    # 1. substrate
    cmd, env = substrate(prog, f'{d}/trial-substrate')
    row, _, _ = timed(cmd, env, f'{prog}.t{n}.substrate')
    same = tree_sha(f'{d}/trial-substrate/{prog}') == info['substrate_tree_sha256']
    append(dict(base, stage='substrate', **row, input_sha256=sha(f'{R}/c2rust-out/{prog}/src/source.rs')[:16],
                note='crat --pass expand,extern,preprocess (release crat); output ' + ('= prep' if same else 'DIFFERS from prep')))
    walls['substrate'] = float(row['wall_s'])
    # 2. S1
    env = identity_env(prog, root, info['launch_digest'])
    env.update({'CRAT_E5C_SIDE_SOURCE': f'{root}/lib.rs', 'CRAT_E5C_SIDE_ROWS': f'{d}/s1-rows-t{n}.tsv'})
    row, out, err = timed([BIN, S1_TEST] + TEST_ARGS, env, f'{prog}.t{n}.s1')
    m = re.search(r'E5C_BISECT \S+ raw=(\d+) ref=(\d+) owning=(\d+) slots=(\d+)', err + out)
    append(dict(base, stage='solve', **row, note=('S1 e5c_inner_solve_named_source (compile+slots/origins+solve+entry '
                                                  'preparation); ' + (f'raw={m[1]} ref={m[2]} owning={m[3]} slots={m[4]}' if m else 'NO E5C_BISECT LINE'))))
    walls['solve'] = float(row['wall_s'])
    # 4. census child (needs the entry; a program whose entry could not be written gets a failed row)
    if not info.get('entry'):
        append(dict(base, stage='emit', exit='-', note=f"failed:{info.get('entry_failure', 'no entry')}"))
        return walls
    fp = os.path.basename(info['entry'])[:-5]
    env = census_env(prog, root, info['launch_digest'], f'{d}/cache', fp, f'{d}/census-t{n}')
    row, out, err = timed([BIN, WORKER] + TEST_ARGS, env, f'{prog}.t{n}.census')
    k = kv(out)
    oc = glob.glob(f'{d}/census-t{n}/{prog}.raw-boundary-outcome.tsv')
    append(dict(base, stage='emit', **row, note=(f"census child raw-boundary-census cache-only (rewrite + verify rounds "
                                                 f"+ the child's custody: 3 compiler sessions, 2 entry loads); rb={k.get('raw_boundary_status')} "
                                                 f"cache={k.get('raw_boundary_cache_status')} outcome={k.get('raw_boundary_outcome_kind')} "
                                                 f"verify_rounds={k.get('raw_boundary_verify_rounds')} delivery={k.get('raw_boundary_delivery')} "
                                                 f"outcome={'yes' if oc else 'no'}")))
    walls['emit'] = float(row['wall_s'])
    return walls


def run(progs):
    for prog in progs:
        try:
            if not os.path.exists(f'{OUT}/prep/{prog}/prep.json'):
                prep(prog)
            w = trial(prog, 1)
            n = 5 if max(w.values()) < 600 else 1
            for i in range(2, n + 1):
                trial(prog, i)
            print(prog, 'done,', n, 'trial(s)', flush=True)
        except SystemExit as e:
            append({'program': prog, 'trial': '-', 'stage': 'prep', 'note': f'failed:{e}'})
            print(prog, 'FAILED:', e, flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'pilot':
        sys.exit(0 if pilot() else 1)
    elif a[0] == 'prep':
        prep(a[1])
    elif a[0] == 'trial':
        print(trial(a[1], int(a[2])))
    elif a[0] == 'run':
        run(a[1:] or NINE)
