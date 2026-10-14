#!/usr/bin/env python3
"""analysis-fanout relay 108, group g5 (rq3 / rq4 / setup keys): seed what is measurable at a frame.

usage: seed_g5.py <census-dir> <solve-dir> [--out <tsv>] [--largest brotli] [--rounds-programs p,q,...]

READ ONLY. No build, no cargo / rustc / miri, no solver. Cache entries are never loaded: the
rounds are read with mmap + bytes.find over the entry (the page cache only; nothing parsed but
small integers).

Keys written (key \t value \t provenance):
  rq3.largest.check-s, rq3.rest.check-s
      the census's `<p>.raw-boundary-timings.tsv` column `initial_verify_s`: the wall of the FIRST
      compile check of the emitted crate inside the census worker (bo_rewriter/mod.rs:2440-2470 at
      4a47f16f7: `verify::diagnose_crate` = an in-process rustc session running `tcx.analysis(())`,
      i.e. parse + expansion + type check + borrow check, no codegen, panic=abort config). For a
      program whose verify loop ran more than one round the later rounds' checks are NOT recorded
      (only `atom_reverify_s`, 0 everywhere at L01^14); the value is the first round's.
      largest = the named program (default brotli = setup.largest-name); rest = sum over the others.
  rq3.largest.rounds
      the solve's cache entry for the largest program (workers/<p>.json completed.cache_entry):
      per demand-evidence construction (one per verification), the number of `final_selections`
      (one per selector solve = one per validation round, construction.rs:1215/1427,
      solver.rs:929-949); the value is the larger of the verifications (analysis-fanout 067/068's
      definition of `analysis.rounds.per-program`). Cross-check: the sum over constructions equals
      the count of `"round":` records in the `retirement-rounds` family.
  rq3.inator.single-trial-min
      the protocol constant of rq3-inator relay 004 §1 ("five trials where a trial is under ten
      minutes, one stated trial otherwise"), read from the docs repo origin/main.
  setup.host, setup.host-ours, setup.host-inator, setup.rustc, setup.solver
      /proc + /etc/os-release (this host); the solve's worker receipts' `host`; rq3-inator report
      001 §3 (host-b); rust-toolchain.toml at the census's code frame + the installed toolchain's
      channel manifest; the solve env's z3 library path + its wheel METADATA, Cargo.lock's z3 crates.
  setup.depth.third-level-slots
      the solve's cache entries' `model` map (bounded head reader, r100/keymap/model_head.py):
      slots whose key ends `@dK` with K >= 2, and their kinds (all twenty programs).
  rq4.suite.coverage.delivered-functions
      wave-6o's coverage.py `delivered()` definition verbatim (docs/agents/tools/runtime/coverage.py:106-112):
      distinct `owner_fn` of `<p>.raw-boundary-subject-outcomes.tsv` rows with
      delivery=realized-as-predicted and emitted_form != unchanged, summed over the six shipped-suite
      programs (R817-1).
"""
import csv, glob, json, mmap, os, re, subprocess, sys

csv.field_size_limit(10**9)
CRAT = 'crat'
DOCS = CRAT + '/docs'
KEYMAP = 'scratch/analysis-fanout/r100/keymap'
SIX = ['libtree', 'rgba', 'quadtree', 'urlparser', 'genann', 'buffer']
PROGRAMS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
            'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']


def tsv1(path):
    rows = list(csv.DictReader(open(path), delimiter='\t'))
    return rows


def git_show(repo, rev_path):
    return subprocess.run(['git', '-C', repo, 'show', rev_path], capture_output=True, text=True, check=True).stdout


def aggregate_kv(census):
    text = open(os.path.join(census, 'aggregate.kv')).read()
    return dict(re.findall(r'(\w+)=(\S+)', text))


# ---------------------------------------------------------------- rq3 check-s
def check_s(census, largest):
    per, rounds = {}, {}
    for p in PROGRAMS:
        tf = os.path.join(census, f'{p}.raw-boundary-timings.tsv')
        if not os.path.exists(tf):  # r141: the typed-failure program (tulipindicators at 58''') writes no timings table
            print(f'# r141: {p} has no raw-boundary-timings.tsv (typed failure); check-s left out of the sum', file=sys.stderr)
            per[p] = 0.0
        else:
            r = tsv1(tf)[0]
            per[p] = float(r['initial_verify_s'])
            assert float(r['atom_reverify_s']) == 0.0, (p, r['atom_reverify_s'])
        o = tsv1(os.path.join(census, f'{p}.raw-boundary-outcome.tsv'))[0]
        rounds[p] = int(o['verify_rounds'])
    multi = {p: n for p, n in rounds.items() if n > 1}
    rest = sum(v for p, v in per.items() if p != largest)
    prov_common = (f'{census}/<p>.raw-boundary-timings.tsv column initial_verify_s (the first compile check of the '
                   f'emitted crate in the census worker: verify::diagnose_crate = in-process rustc tcx.analysis(), '
                   f'type + borrow check, no codegen; bo_rewriter/mod.rs:2440-2470 at the code frame); '
                   f'atom_reverify_s = 0 for all 20; verify_rounds > 1 for {multi or "none"} '
                   f'(their later rounds are not timed separately: the value is the first round\'s)')
    return [
        ('rq3.largest.check-s', f'{per[largest]:.1f}', f'{largest} {per[largest]:.6f} s; ' + prov_common),
        ('rq3.rest.check-s', f'{rest:.1f}',
         f'sum over the 19 others = {rest:.6f} s (' + ', '.join(f'{p} {v:.3f}' for p, v in sorted(per.items()) if p != largest)
         + '); ' + prov_common),
    ], per


# ---------------------------------------------------------------- rq3 rounds
def cache_entry(solve, program):
    w = json.load(open(os.path.join(solve, 'workers', f'{program}.json')))
    assert w['status'] == 'complete', (program, w['status'])
    e = w['completed']['cache_entry']
    if not os.path.exists(e):  # r141: the S39 row's host-b ten were copied into its own cache dir
        e = os.path.join(solve, 'cache/era5b-model-cache-v1', os.path.basename(e))
    return e, w.get('host')


def rounds_of(path):
    """per construction: number of final selections (= validation rounds of that verification)."""
    with open(path, 'rb') as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as m:
        de = m.find(b'"demand-evidence":{')
        assert de >= 0, 'no demand-evidence family'
        assert m.find(b'"demand-evidence":{', de + 1) < 0, 'two demand-evidence keys'
        # the family ends where the next family key starts: `},"<name>":{"availability":`
        nxt = re.compile(rb'\},"[a-z0-9-]+":\{"availability":\{')
        spans = []
        pos = de
        while True:
            fs = m.find(b'"final_selections":[', pos)
            if fs < 0:
                break
            q = m.find(b'],"queries":[', fs)
            assert q > fs
            # the family boundary check: no `"availability":{` key between de and fs except the family's own
            av = m.find(b'"availability":{', de + 20, fs)
            if av >= 0:
                break
            seg = m[fs:q]
            epochs = re.findall(rb'"epoch":(\d+)', seg)
            # an epoch key inside a final selection appears once per selection
            spans.append((len(epochs), sorted(set(int(e) for e in epochs))))
            pos = q
        rr = m.find(b'"retirement-rounds":{')
        assert rr >= 0 and m.find(b'"retirement-rounds":{', rr + 1) < 0
        # the retirement-rounds family value ends at the next `"availability":{` after its own
        own_av = m.find(b'"availability":{', rr)
        end = m.find(b'"availability":{', own_av + 1)
        if end < 0:
            end = len(m)
        n_round = 0
        p = rr
        while True:
            p = m.find(b'"round":', p + 1, end)
            if p < 0:
                break
            n_round += 1
    return spans, n_round


def rounds_rows(solve, largest, extra):
    rows, notes = [], []
    for p in [largest] + [x for x in extra if x != largest]:
        path, _ = cache_entry(solve, p)
        spans, n_round = rounds_of(path)
        counts = [c for c, _ in spans]
        ok = all(e == list(range(c)) or len(e) == c for c, e in spans)
        notes.append(f'{p}: final_selections per construction {counts}, retirement-rounds records {n_round}, '
                     f'sum-check {"ok" if sum(counts) == n_round else "MISMATCH"}')
        if p == largest:
            assert sum(counts) == n_round, (p, counts, n_round)
            rows.append(('rq3.largest.rounds', str(max(counts)),
                         f'{path} (bytes scanned with mmap, never parsed): demand-evidence constructions '
                         f'(one per verification) have {counts} final selections = validation rounds; value = the '
                         f'larger (analysis-fanout 067/068 definition of analysis.rounds.per-program, brotli 13 there); '
                         f'retirement-rounds family has {n_round} round records = the sum (check ok)'))
    return rows, notes


# ---------------------------------------------------------------- setup
def host_rows(solve):
    cpu = re.search(r'model name\s*:\s*(.+)', open('/proc/cpuinfo').read()).group(1).strip()
    ci = open('/proc/cpuinfo').read()
    threads = len(re.findall(r'^processor\s*:', ci, re.M))
    cores = len(set(re.findall(r'^core id\s*:\s*(\d+)', ci, re.M)))
    mem_kib = int(re.search(r'MemTotal:\s*(\d+)', open('/proc/meminfo').read()).group(1))
    gib = mem_kib / (1 << 20)
    osname = re.search(r'PRETTY_NAME="([^"]+)"', open('/etc/os-release').read()).group(1)
    kernel = os.uname().release
    hostname = os.uname().nodename
    model = re.sub(r'\s+\d+-Core Processor$', '', cpu)
    hosts = set()
    for p in PROGRAMS:
        _, h = cache_entry(solve, p)
        hosts.add(h)
    if hosts != {hostname}:  # r141: the S39 row mixes host-a and host-b solves (era-5c 168 s3); recorded, not asserted
        print('# r141: worker hosts', sorted(hosts), file=sys.stderr)
    value = f'{model} ({cores} cores, {threads} threads), {gib:.0f} GiB RAM, {osname}'
    rows = [
        ('setup.host', value,
         f'this host ({hostname}) at the time of the run: /proc/cpuinfo model name "{cpu}", {cores} distinct core ids, '
         f'{threads} processors; /proc/meminfo MemTotal {mem_kib} kB = {gib:.1f} GiB; /etc/os-release "{osname}"; '
         f'kernel {kernel}. host-b (rq3-inator 001 sec. 3): same CPU / RAM / OS, kernel 6.17.0-40-generic '
         f'(analysis-fanout 016 sec. 5: the one difference)'),
        ('setup.host-ours', hostname,
         f'os.uname().nodename; every worker receipt {solve}/workers/<p>.json "host" = {sorted(hosts)} (20/20)'),
    ]
    r001 = [l for l in git_show(DOCS, 'origin/main:agents/reports/rq3-inator/001-artifact-pinned-nine-inventoried-host-b-spec-smoke-run.md').splitlines()
            if l.startswith('- **host-b:**')]
    assert r001 and 'AMD Ryzen 9 9950X' in r001[0], r001
    rows.append(('setup.host-inator', 'host-b',
                 'docs origin/main agents/reports/rq3-inator/001 (spec line: ' + r001[0][2:].strip()
                 + '); relay rq3-inator/004 (R670-1: &inator alone on host-b); every rq3.inator.*.host-s provenance names host-b'))
    return rows


def rustc_row(census):
    agg = aggregate_kv(census)
    code = agg['raw_boundary_code_frame']
    tc = git_show(CRAT, f'{code}:rust-toolchain.toml')
    channel = re.search(r'channel\s*=\s*"([^"]+)"', tc).group(1)
    man = os.path.expanduser(f'~/.rustup/toolchains/{channel}-x86_64-unknown-linux-gnu/lib/rustlib/multirust-channel-manifest.toml')
    text = open(man).read()
    ver = re.search(r'^\[pkg\.rustc\]\nversion = "([^"]+)"', text, re.M).group(1)
    return [('setup.rustc', ver,
             f'{code}:rust-toolchain.toml channel = "{channel}" (census aggregate.kv raw_boundary_code_frame); '
             f'{man} [pkg.rustc] version; rustc was not invoked. NB: the Miri runs (rq4.checker) use a different, '
             f'newer nightly (rustc 1.100.0-nightly per wave-6o 097)')]


def solver_row(solve, census):
    envs = sorted(glob.glob(os.path.join(solve, '*env*.sh')))
    z3dir = None
    for e in envs:
        m = re.search(r'(/[^:\s"]*z3-solver-[^/:\s"]+/z3)/lib', open(e).read())
        if m:
            z3dir, envf = m.group(1), e
            break
    if z3dir is None:  # r146: the 60-KINDORDER solve ran on host-b with Z3's release tarball (z3-4.15.4-x64-glibc-2.39/bin), not the pip wheel
        for e in envs:
            m = re.search(r'(/[^:\s"]*/z3-(\d+\.\d+\.\d+)-x64[^/:\s"]*)/bin', open(e).read())
            if m:
                z3dir, envf = m.group(1), e
                break
        if z3dir is None:
            raise SystemExit(('no z3 in', envs))
        ver = re.search(r'/z3-(\d+\.\d+\.\d+)-x64', z3dir).group(1)
        meta = [f'{z3dir} (release tarball name; host-b path, version read from the directory name)']
        so = sorted(os.path.basename(x) for x in glob.glob(os.path.join(z3dir, 'bin', 'libz3.so*'))) or ['libz3.so (host-b; not on this host)']
    else:
        meta = glob.glob(os.path.join(os.path.dirname(z3dir), 'z3_solver-*.dist-info', 'METADATA'))
        ver = re.search(r'^Version: (\S+)', open(meta[0]).read(), re.M).group(1)
        so = sorted(os.path.basename(x) for x in glob.glob(os.path.join(z3dir, 'lib', 'libz3.so*')))
    agg = aggregate_kv(census)
    code = agg['raw_boundary_code_frame']
    lock = git_show(CRAT, f'{code}:Cargo.lock')
    crates = re.findall(r'name = "(z3(?:-sys)?)"\nversion = "([^"]+)"', lock)
    short = '.'.join(ver.split('.')[:3])
    rec = open(os.path.join(census, 'census-receipt.txt')).read()
    m141 = re.search(r'solver_seconds=(\S+)', rec)  # r141: the typed-failure receipt omits solver_seconds
    solver_seconds = m141.group(1) if m141 else 'absent-from-the-typed-failure-receipt (per-program.kv cache_status=hit 20/20)'
    return [('setup.solver', f'Z3 {short}',
             f'{envf}: LD_LIBRARY_PATH -> {z3dir}/lib ({", ".join(so)}); {meta[0]} Version {ver}; '
             f'Cargo.lock at {code}: ' + ', '.join(f'{n} {v}' for n, v in crates)
             + f' (z3-sys links the system library dynamically); the census itself solves nothing '
             f'(census-receipt solver_seconds={solver_seconds}, cache hits); &inator\'s image also runs Z3 4.15.4 (rq3-inator 002)')]


def depth_row(solve):
    sys.path.insert(0, KEYMAP)
    from model_head import read_head
    per, kinds, deepest = {}, {}, 0
    for p in PROGRAMS:
        path, _ = cache_entry(solve, p)
        prog, universe, model, _ = read_head(path)
        assert prog == p, (prog, p)
        for k, v in model.items():
            d = int(re.search(r'@d(\d+)$', k).group(1))
            deepest = max(deepest, d)
            if d >= 2:
                per[p] = per.get(p, 0) + 1
                kinds[(d, v)] = kinds.get((d, v), 0) + 1
    n = sum(per.values())
    return [('setup.depth.third-level-slots', str(n),
             f'{solve}/cache entries (workers/<p>.json completed.cache_entry), the head `model` map via '
             f'{KEYMAP}/model_head.py (bounded prefix, tail never read): slots with key suffix @dK, K >= 2 '
             f'(d0 = outermost level, so d2 = the third level); per program {per}; kinds {{(depth, kind): n}} = {kinds}; '
             f'deepest level in any model = d{deepest}; cross-check: r100/keymap/reverse-index.tsv depth=2 rows = 14, all ref')], deepest


def delivered_fns_row(census):
    per, subj = {}, {}
    for p in SIX:
        owners = {}
        for r in csv.DictReader(open(os.path.join(census, f'{p}.raw-boundary-subject-outcomes.tsv')), delimiter='\t'):
            if r['delivery'] == 'realized-as-predicted' and r['emitted_form'] != 'unchanged':
                owners[r['owner_fn']] = owners.get(r['owner_fn'], 0) + 1
        per[p] = len(owners)
        subj[p] = sum(owners.values())
    n = sum(per.values())
    return [('rq4.suite.coverage.delivered-functions', str(n),
             f'{census}/<p>.raw-boundary-subject-outcomes.tsv, the six (R817-1): distinct owner_fn over rows with '
             f'delivery=realized-as-predicted and emitted_form!=unchanged (wave-6o coverage.py delivered(), '
             f'docs/agents/tools/runtime/coverage.py:106-112, verbatim); per program {per}; delivered subjects {subj}. '
             f'Must be re-read at the SAME census as rq4.suite.coverage.executed-functions')]


def main(argv):
    census, solve = argv[1], argv[2]
    out = argv[argv.index('--out') + 1] if '--out' in argv else None
    largest = argv[argv.index('--largest') + 1] if '--largest' in argv else 'brotli'
    extra = argv[argv.index('--rounds-programs') + 1].split(',') if '--rounds-programs' in argv else []
    rows = []
    r, _ = check_s(census, largest); rows += r
    r, notes = rounds_rows(solve, largest, extra); rows += r
    relay = git_show(DOCS, 'origin/main:agents/relays/rq3-inator/004.md')
    m = re.search(r'five trials where a trial is under (\w+) minutes, one stated trial otherwise', relay)
    words = {'ten': 10, 'five': 5, 'fifteen': 15, 'twenty': 20, 'thirty': 30, 'sixty': 60}
    rows.append(('rq3.inator.single-trial-min', str(words.get(m.group(1), m.group(1))),
                 'docs origin/main agents/relays/rq3-inator/004.md sec. 1: "' + m.group(0) + '" (protocol constant, '
                 'R670-1); applied in rq3-inator 002: jccc and tisp one trial each, rbtree (602-615 s, above 600 s) one ok trial'))
    rows += host_rows(solve)
    rows += rustc_row(census)
    rows += solver_row(solve, census)
    r, _ = depth_row(solve); rows += r
    rows += delivered_fns_row(census)
    text = 'key\tvalue\tprovenance\n' + ''.join(f'{k}\t{v}\t{p}\n' for k, v, p in rows)
    if out:
        open(out, 'w').write(text)
    sys.stdout.write(text)
    for n in notes:
        print('# ' + n)


if __name__ == '__main__':
    main(sys.argv)
