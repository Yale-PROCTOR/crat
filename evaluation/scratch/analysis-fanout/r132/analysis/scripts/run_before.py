#!/usr/bin/env python3
"""r132 runner (relay 132): the raw-to-safe conversion-site counter, built and run once a window opens.

  run.py build   [--beside-lock]        cargo build --release of counter/ into r132/target (crat-cargo.sh slot,
                                        nice 10, CARGO_INCREMENTAL=0, --offline); quotes the Compiling line
  run.py toy     [--beside-lock]        the counter on toy/lib.rs -> out/toy/; checks toy/expected.tsv (exit 1 on any
                                        mismatch, missing or unexpected row) -> out/toy/check.txt
  run.py run --side SIDE [PROG ...]     SIDE: input | crown | laertes | ours56 | ours58 -> out/<side>/<p>/sites.tsv
  run.py summarize                      out/summary.tsv (wide, per side x program + TOTAL), out/summary-long.tsv and
                                        out/spot.txt (the relay's three known examples)
  run.py all     [--beside-lock]        build, toy (stops on a toy failure), the five sides, summarize

Refuses to start while the corpus lock (worktrees/CORPUS-SLOT.lock) exists unless --beside-lock; ours58 waits
for nothing: it runs only when main/batch58-done exists. One program at a time, `nice -n 10`, a MemAvailable floor
(POS_MEM_FLOOR_GIB, default 40, as pos_census.py). Writes only under r132/.

The per-tree invocation is pos_census.py's (031/043) and run_t5.py's (r116, which adds relay 117's llvm_asm!
adaptation): the same driver configuration (edition 2021, rlib, deps_crate's rlibs, lints capped), SYSROOT /
LD_LIBRARY_PATH / DIR / RUSTUP_TOOLCHAIN, `pos_census.root_of` for the crate root, Laertes trees as the artifact
ships them (`seed_rq2.laertes_root`), the E0557 feature-gate shim (`pos_census.removed_features` / `shim_tree`, the
gates rustc reports removed deleted from `#![feature(..)]`, a bare `#[main]` dropped) and, for a tree holding
`llvm_asm!` (libzahl), r117/adapt_llvm_asm.py run unchanged before the shim. New: `--sites`; no --universe /
--strip-src (the site table does not use the T2 key universe).

r132 review fixes (10-10, DESIGN.md §11): the toy checks every column of toy/expected.tsv (`field_ok`); a program counts
only when status.txt AND sites-status.txt (the site pass runs under catch_unwind) say ok; a driver that dies without a
status gets `exit-<rc>` (run_t5.py's rule), a tree without a crate root `no-root`; null_dom's yes / yes-place /
yes-base / yes-base-place are separate summary columns; kind a splits into a_direct / a_via_safe; spot.txt checks the 4
null-dominated CROWN Box::from_raw (quadtree node.rs:123/126/129/132)."""
import argparse, csv, os, re, shutil, subprocess, sys, time
from collections import Counter, defaultdict

sys.dont_write_bytecode = True          # importing the docs tools must not write __pycache__ there
R = 'scratch/analysis-fanout/r132'
TOOLS = 'docs/agents/tools/rq2'
sys.path.insert(0, TOOLS)
import pos_census as P  # noqa: E402  (read-only: root_of, removed_features, shim_tree, sysroot, PROGRAMS, INPUT, CROWN)
import seed_rq2 as SR  # noqa: E402   (read-only: laertes_root)

CRAT = P.CRAT
TOOLCHAIN = P.TOOLCHAIN
TARGET = f'{R}/target'
EXE = f'{TARGET}/release/rq2_site_counter'
MANIFEST = f'{R}/counter/Cargo.toml'
OUT = f'{R}/analysis/out-before'   # r132 analysis: the Laertes BEFORE trees only
TOY = f'{R}/toy'
LOCK = 'worktrees/CORPUS-SLOT.lock'
MAIN = 'scratch/main'
CENSUS = {'ours56': f'{MAIN}/batch56', 'ours58': f'{MAIN}/batch58'}
DONE = {'ours56': f'{MAIN}/batch56-done', 'ours58': f'{MAIN}/batch58-done'}
ADAPT = 'scratch/analysis-fanout/r117/adapt_llvm_asm.py'
SIDES = ['laertes_before']
MEM_FLOOR_GIB = int(os.environ.get('POS_MEM_FLOOR_GIB', '40'))
csv.field_size_limit(10**9)


def log(msg):
    os.makedirs(OUT, exist_ok=True)
    line = f'{time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())} {msg}'
    print(line, flush=True)
    with open(f'{OUT}/run.log', 'a') as f:
        f.write(line + '\n')


def check_lock(beside):
    if os.path.exists(LOCK):
        held = open(LOCK).read().strip()
        if not beside:
            raise SystemExit(f'corpus lock held, not starting (pass --beside-lock to override): {held}')
        log(f'--beside-lock: starting beside the corpus lock: {held}')


def env():
    sr = P.sysroot()
    return dict(os.environ, SYSROOT=sr, LD_LIBRARY_PATH=f'{sr}/lib', DIR=CRAT, RUSTUP_TOOLCHAIN=TOOLCHAIN)


def mem_wait(what):
    while P.mem_avail_gib() < MEM_FLOOR_GIB:
        log(f'{what}: waiting for MemAvailable >= {MEM_FLOOR_GIB} GiB')
        time.sleep(60)


# ------------------------------------------------------------------------------------------------------ build

def build():
    e = dict(os.environ, RUSTUP_TOOLCHAIN=TOOLCHAIN, CARGO_TARGET_DIR=TARGET, CARGO_INCREMENTAL='0',
             CRAT_LANE='analysis-fanout')
    os.makedirs(OUT, exist_ok=True)
    cmd = ['bash', f'{CRAT}/docs/agents/tools/crat-cargo.sh', 'build', '--release', '--offline',
           '--manifest-path', MANIFEST]       # crat-cargo.sh = one build slot + nice -n 10 + ionice
    log('build: ' + ' '.join(cmd))
    pr = subprocess.run(cmd, env=e, capture_output=True, text=True)
    open(f'{OUT}/build.log', 'w').write(pr.stdout + pr.stderr)
    comp = [l.strip() for l in pr.stderr.splitlines() if 'Compiling rq2_site_counter' in l]
    log(f'build rc={pr.returncode}; ' + (comp[0] if comp else 'no Compiling line (up to date?)'))
    if comp and R not in comp[0]:
        raise SystemExit(f'build compiled a crate outside r132: {comp[0]}')
    if pr.returncode or not os.path.isfile(EXE):
        raise SystemExit(f'build failed, see {OUT}/build.log')
    return EXE


# ------------------------------------------------------------------------------------------------------ run

def counter(root, dest, note=()):
    """One counter run: (rc, stderr); cmd.txt / stderr.txt / note in dest."""
    os.makedirs(dest, exist_ok=True)
    for f in os.listdir(dest):
        if os.path.isfile(os.path.join(dest, f)):
            os.remove(os.path.join(dest, f))
    cmd = ['nice', '-n', '10', '/usr/bin/time', '-f', 'wall=%e maxrss_kb=%M', EXE, '--root', root, '--out', dest,
           '--sites']
    pr = subprocess.run(cmd, env=env(), capture_output=True, text=True)
    open(os.path.join(dest, 'cmd.txt'), 'w').write(' '.join(cmd) + '\n' + ''.join(f'{n}\n' for n in note))
    if pr.returncode:
        open(os.path.join(dest, 'stderr.txt'), 'w').write(pr.stderr[-20000:])
    return pr.returncode, pr.stderr


def has_llvm_asm(d):
    for dp, _, fs in os.walk(d):
        for f in fs:
            if f.endswith('.rs') and 'llvm_asm!' in open(os.path.join(dp, f), errors='replace').read():
                return True
    return False


def side_dir(side, p):
    if side == 'input':
        return f'{P.INPUT}/{p}'
    if side == 'crown':
        return f'{P.CROWN}/{p}'
    if side == 'laertes':
        return SR.laertes_root(p)[0]
    if side == 'laertes_before':   # the artifact's Laertes INPUT trees (r116 t4/t5's rule: /after/ -> /before/)
        d = SR.laertes_root(p)[0]
        if d is None:
            return None
        b = d.replace('/after/', '/before/')
        assert b != d, d
        return b
    if side in CENSUS:
        return os.path.join(CENSUS[side], 'emitted-trees', p)
    raise SystemExit(f'unknown side {side}')


def run_side(side, progs):
    assert os.path.isfile(EXE), f'{EXE} missing: run.py build first'
    if side in DONE and not os.path.exists(DONE[side]):
        log(f'{side}: {DONE[side]} absent (census not finished); skipped')
        return
    for p in progs:
        dest = os.path.join(OUT, side, p)
        d = side_dir(side, p)
        if not d or not os.path.isdir(d):
            os.makedirs(dest, exist_ok=True)
            open(os.path.join(dest, 'status.txt'), 'w').write(f'no-tree\t{d}\n')
            log(f'{side}\t{p}\tno-tree\t{d}')
            continue
        note = []
        if side.startswith('laertes') and has_llvm_asm(d):
            # R882-1 (relay 117): the mechanical llvm_asm! -> asm! adaptation, r117's script unchanged
            base = os.path.join(OUT, 'adapted', side, p)
            ad = os.path.join(base, 'tree')
            os.makedirs(base, exist_ok=True)
            subprocess.run(['python3', ADAPT, d, ad], check=True, capture_output=True, text=True)
            if os.path.exists(os.path.join(base, 'sites.tsv')):     # the script's own list of llvm_asm! sites
                os.replace(os.path.join(base, 'sites.tsv'), os.path.join(base, 'llvm-asm-sites.tsv'))
            note.append(f'llvm_asm adapted by {ADAPT} into {ad}')
            d = ad
        r = P.root_of(d)
        if not r:                                   # no crate root in the tree (pos_census.run's `no-tree` guard)
            os.makedirs(dest, exist_ok=True)
            open(os.path.join(dest, 'status.txt'), 'w').write(f'no-root\t{d}\n')
            log(f'{side}\t{p}\tno-root\t{d}')
            continue
        mem_wait(f'{side} {p}')
        t0 = time.time()
        rc, err = counter(r, dest, note)
        if rc and side.startswith('laertes'):
            removed = P.removed_features(err)
            if removed:
                r2, shim = P.shim_tree(os.path.join(OUT, 'shimroot'), p, d, r, removed)
                note.append(f'removed feature gates: {",".join(sorted(removed))}; shim tree: {shim}')
                rc, err = counter(r2, dest, note)
                r = r2
        st = open(os.path.join(dest, 'status.txt')).read().split('\t')[0].strip() \
            if os.path.exists(os.path.join(dest, 'status.txt')) else f'exit-{rc}'
        if st != 'ok' and not os.path.exists(os.path.join(dest, 'status.txt')):
            # the driver died before writing a status (a panic outside the site pass): record it (as run_t5.py does)
            open(os.path.join(dest, 'status.txt'), 'w').write(f'{st}\t{r}\n')
        sst = sites_status(dest)
        tail = err.strip().splitlines()
        log(f'{side}\t{p}\t{st}\tsites={sst}\trc={rc}\t{r}\t{time.time() - t0:.1f}s\t{tail[-1] if tail else "-"}\t'
            f'{"; ".join(note)}')


def sites_status(dest):
    """`ok` when the site pass wrote its table, `panic` when it panicked (sites-status.txt), `no-sites-status`."""
    f = os.path.join(dest, 'sites-status.txt')
    return open(f).read().split('\t')[0].strip() if os.path.exists(f) else 'no-sites-status'


def row_status(dest):
    """The status a program's rows are counted under: T1 / T2's status.txt, then the site pass's own."""
    stf = os.path.join(dest, 'status.txt')
    st = open(stf).read().split('\t')[0].strip() if os.path.exists(stf) else 'no-run'
    if st != 'ok':
        return st
    sst = sites_status(dest)
    return 'ok' if sst == 'ok' else f'sites-{sst}'


# ------------------------------------------------------------------------------------------------------ toy

FIELDS = ['fn', 'kind', 'call', 'dest', 'dest_detail', 'formal_ty', 'formal_safe', 'via', 'excluded', 'excl_reason',
          'null_dom', 'null_test', 'src_ty', 'raw_derefs', 'post_raw_derefs', 'in_wrapper', 'macro']
# expected.tsv matching: `*` = not checked; `re:<regex>` = re.search; `-` = exact; these columns as substrings (type
# strings and line-suffixed tests print with paths / lines the toy does not pin); dest_detail too for call-arg rows;
# every other column exact
SUBSTR = {'fn', 'call', 'formal_ty', 'via', 'null_test', 'src_ty'}


def field_ok(f, want, have, exp):
    if want == '*':
        return True
    if want.startswith('re:'):
        return re.search(want[3:], have) is not None
    sub = (f in SUBSTR or (f == 'dest_detail' and exp['dest'] == 'call-arg')) and want != '-'
    return want in have if sub else want == have


def toy():
    assert os.path.isfile(EXE), f'{EXE} missing: run.py build first'
    dest = os.path.join(OUT, 'toy')
    rc, err = counter(f'{TOY}/lib.rs', dest)
    if rc:
        raise SystemExit(f'toy: the counter failed (rc {rc}); see {dest}/stderr.txt')
    if sites_status(dest) != 'ok':
        raise SystemExit(f'toy: the site pass did not finish ({sites_status(dest)}); see {dest}/sites-status.txt')
    tag_line = {}
    for i, l in enumerate(open(f'{TOY}/lib.rs'), 1):
        for t in re.findall(r'// SITE:(\w+)', l):
            tag_line[t] = i
    exp = list(csv.DictReader(open(f'{TOY}/expected.tsv'), delimiter='\t'))
    got = list(csv.DictReader(open(os.path.join(dest, 'sites.tsv')), delimiter='\t'))
    used, lines = set(), []
    ok = True
    for e in exp:
        line = tag_line[e['tag']]
        cands = [i for i, g in enumerate(got) if i not in used and int(g['line']) == line and g['kind'] == e['kind']]
        if not cands:
            ok = False
            lines.append(f'MISSING\t{e["tag"]}\tline {line}\t{e["kind"]}')
            continue
        i = cands[0]
        used.add(i)
        g, bad = got[i], []
        for f in FIELDS:
            want, have = e[f], g[f]
            if not field_ok(f, want, have, e):
                bad.append(f'{f}: want {want!r} got {have!r}')
        if bad:
            ok = False
            lines.append(f'MISMATCH\t{e["tag"]}\tline {line}\t' + '; '.join(bad))
        else:
            lines.append(f'ok\t{e["tag"]}\tline {line}\t{g["kind"]}\t{g["dest"]}\t{g["dest_detail"]}\tvia={g["via"]}'
                         f'\tnull={g["null_dom"]}:{g["null_test"]}')
    for i, g in enumerate(got):
        if i not in used:
            ok = False
            lines.append(f'UNEXPECTED\tline {g["line"]}\t{g["fn"]}\t{g["kind"]}\t{g["dest"]}\t{g["dest_detail"]}')
    lines.append(f'TOY {"PASS" if ok else "FAIL"}: {len(exp)} expected rows, {len(got)} rows')
    open(os.path.join(dest, 'check.txt'), 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(lines))
    return ok


# ------------------------------------------------------------------------------------------------------ summarize

def boundary(g):
    """A call-arg into crat's exposure twin (`__crat_safe_<f>`, the safe body behind the C-named wrapper)."""
    return g['dest'] == 'call-arg' and g['dest_detail'].rsplit('::', 1)[-1].startswith('__crat_safe_')


# null_dom's four positive values are never merged: `yes` (the place AND its value: no write on any path from the test
# to the site), `yes-place` (the same place, value unproven), and the `-base` pair for an offset of the tested place
ND = ['yes', 'yes-place', 'yes-base', 'yes-base-place']
WIDE = (['status', 'rows', 'ab', 'ab_not_in_wrapper', 'a', 'a_direct', 'a_via_safe', 'a_decl_fresh', 'b', 'b_box']
        + [f'b_box_nd_{v.replace("-", "_")}' for v in ND] + ['b_asrefmut']
        + [f'b_asrefmut_nd_{v.replace("-", "_")}' for v in ND]
        + ['b_slice', 'b_nonnull', 'x', 'h', 'excluded', 'excluded.method-to-raw', 'ab.call-arg', 'ab.call-arg.safe',
           'ab.call-arg.raw', 'ab.call-arg.other', 'ab.call-arg.boundary', 'ab.decl', 'ab.assign', 'ab.return',
           'ab.field-store', 'ab.other'])


def summarize():
    wide, long_rows = [], Counter()
    for side in SIDES:
        tot = Counter()
        for p in P.PROGRAMS:
            dest = os.path.join(OUT, side, p)
            st = row_status(dest)
            c = Counter()
            sf = os.path.join(dest, 'sites.tsv')
            if st == 'ok' and os.path.exists(sf):
                for g in csv.DictReader(open(sf), delimiter='\t'):
                    k = g['kind']
                    fam = k.split(':')[0]
                    via_safe = fam == 'a' and g['post_raw_derefs'] != '0'
                    long_rows[(side, p, fam, k, g['excluded'], g['excl_reason'], g['dest'], g['formal_safe'],
                               g['null_dom'], g['in_wrapper'], 'boundary' if boundary(g) else '-',
                               'via-safe' if via_safe else '-')] += 1
                    c['rows'] += 1
                    if g['excluded'] == 'yes':
                        c['excluded'] += 1
                        c['excluded.method-to-raw'] += g['excl_reason'] == 'method-to-raw'
                        continue
                    c[fam] += 1
                    if fam in ('a', 'b'):
                        c['ab'] += 1
                        c['ab_not_in_wrapper'] += g['in_wrapper'] == 'no'
                        c[f'ab.{g["dest"]}'] += 1
                        if g['dest'] == 'call-arg':
                            c[f'ab.call-arg.{"safe" if g["formal_safe"] == "safe" else "raw" if g["formal_safe"] == "raw" else "other"}'] += 1
                            c['ab.call-arg.boundary'] += boundary(g)
                    if fam == 'a':
                        # a reference produced from the raw pointer itself, or a reborrow of a safe ref / Box that was
                        # only LOADED through a raw pointer (`&mut *(*p).r`, post_raw_derefs > 0)
                        c['a_via_safe' if via_safe else 'a_direct'] += 1
                    if fam == 'a' and g['dest'] == 'decl' and g['dest_detail'].startswith('fresh'):
                        c['a_decl_fresh'] += 1
                    nd = g['null_dom'].replace('-', '_')
                    if k.startswith('b:box-'):
                        c['b_box'] += 1
                        if g['null_dom'] in ND:
                            c[f'b_box_nd_{nd}'] += 1
                    if k in ('b:ptr-as_ref', 'b:ptr-as_mut'):
                        c['b_asrefmut'] += 1
                        if g['null_dom'] in ND:
                            c[f'b_asrefmut_nd_{nd}'] += 1
                    if k.startswith('b:slice-'):
                        c['b_slice'] += 1
                    if k.startswith('b:nonnull-'):
                        c['b_nonnull'] += 1
            row = {'side': side, 'program': p, 'status': st}
            for f in WIDE[1:]:
                row[f] = c[f]
                tot[f] += c[f]
            tot['ok'] += st == 'ok'
            wide.append(row)
        wide.append(dict({'side': side, 'program': 'TOTAL', 'status': f'{tot["ok"]} ok'},
                         **{f: tot[f] for f in WIDE[1:]}))
    with open(f'{OUT}/summary.tsv', 'w') as f:
        f.write('\t'.join(['side', 'program'] + WIDE) + '\n')
        for r in wide:
            f.write('\t'.join(str(r.get(c, '-')) for c in ['side', 'program'] + WIDE) + '\n')
    with open(f'{OUT}/summary-long.tsv', 'w') as f:
        f.write('side\tprogram\tfamily\tkind\texcluded\texcl_reason\tdest\tformal_safe\tnull_dom\tin_wrapper\tboundary\t'
                'post_raw\tcount\n')
        for k, n in sorted(long_rows.items()):
            f.write('\t'.join(map(str, k)) + f'\t{n}\n')
    for r in wide:
        if r['program'] == 'TOTAL':
            print('\t'.join(f'{c}={r.get(c)}' for c in ['side', 'status', 'ab', 'excluded', 'excluded.method-to-raw',
                                                        'b_box', 'b_box_nd_yes', 'b_box_nd_yes_place', 'b_asrefmut',
                                                        'b_asrefmut_nd_yes', 'b_asrefmut_nd_yes_place', 'x', 'h']))


def spot():
    """The relay's three known examples, checked on the corpus rows (-> out/spot.txt)."""
    def rows(side, p):
        f = os.path.join(OUT, side, p, 'sites.tsv')
        if row_status(os.path.join(OUT, side, p)) != 'ok' or not os.path.exists(f):
            return None
        return list(csv.DictReader(open(f), delimiter='\t'))
    out = []
    b = rows('crown', 'brotli')
    if b is None:
        out.append('SKIP\tcrown brotli: no sites.tsv')
    else:
        hit = [g for g in b if g['file'] == 'src/enc/histogram.rs' and g['line'] in ('150', '151')
               and g['kind'].startswith('a:')]
        good = [g for g in hit if g['excluded'] == 'no' and g['dest'] == 'call-arg'
                and 'HistogramAddCommand' in g['dest_detail']]
        out.append(f'{"ok" if good else "FAIL"}\tcrown brotli histogram.rs:150-151 Some(&mut *insert_and_copy_histograms'
                   f'.offset(..)) -> HistogramAddCommand: ' + ' | '.join(
                       f'{g["kind"]} {g["dest"]} {g["dest_detail"]} formal={g["formal_ty"]} via={g["via"]} '
                       f'excl={g["excluded"]}' for g in hit))
    n, seen, boxes = 0, True, []
    for p in ('quadtree', 'json.h'):
        rs = rows('crown', p)
        if rs is None:
            seen = False
            continue
        bx = [g for g in rs if g['kind'] == 'b:box-from_raw']
        n += len(bx)
        boxes += [(p, g) for g in bx]
    out.append(f'{"ok" if seen and n == 9 else "FAIL" if seen else "SKIP"}\tcrown Box::from_raw rows quadtree + json.h '
               f'= {n} (the source text holds 9)')
    # the four guarded ones (read from the source 10-10): quadtree src/src/node.rs:123/126/129/132, each under
    # `if !(*node.as_deref().unwrap()).<nw|ne|sw|se>.is_null()`; node.rs:77, :134, quadtree.rs:212 and json.rs:2273 /
    # 2286 have no dominating test
    guarded = {('quadtree', 'src/src/node.rs', l) for l in ('123', '126', '129', '132')}
    nd = [(p, g) for p, g in boxes if g['null_dom'] != 'no']
    nd_keys = {(p, g['file'], g['line']) for p, g in nd}
    split = Counter(g['null_dom'] for _, g in nd)
    out.append(f'{"ok" if seen and nd_keys == guarded else "FAIL" if seen else "SKIP"}\tcrown Box::from_raw '
               f'null-dominated = {len(nd)} of {n} (expected the 4 guarded quadtree node.rs:123/126/129/132), by value: '
               + ', '.join(f'{v}={split[v]}' for v in ND) + ' | '
               + ' '.join(f'{p}:{g["file"]}:{g["line"]}={g["null_dom"]}:{g["null_test"]}' for p, g in boxes))
    l = rows('laertes', 'libtree')
    if l is None:
        out.append('SKIP\tlaertes libtree: no sites.tsv')
    else:
        hit = [g for g in l if g['file'] == 'src/libtree.rs' and g['line'] == '1199' and g['kind'].startswith('a:')]
        good = [g for g in hit if g['excluded'] == 'yes' and g['dest'] == 'call-arg' and g['formal_safe'] == 'raw']
        out.append(f'{"ok" if good else "FAIL"}\tlaertes libtree src/libtree.rs:1199 &mut *(..).offset(..) to strncmp '
                   f'(an exclusion): ' + ' | '.join(
                       f'{g["kind"]} {g["dest"]} {g["dest_detail"]} excl={g["excluded"]}:{g["excl_reason"]}'
                       for g in hit))
    open(f'{OUT}/spot.txt', 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['build', 'toy', 'run', 'summarize', 'all'])
    ap.add_argument('--side', choices=SIDES)
    ap.add_argument('--beside-lock', action='store_true')
    ap.add_argument('programs', nargs='*')
    a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    if a.cmd in ('build', 'toy', 'run', 'all'):
        check_lock(a.beside_lock)
    if a.cmd == 'build':
        build()
    elif a.cmd == 'toy':
        sys.exit(0 if toy() else 1)
    elif a.cmd == 'run':
        if not a.side:
            raise SystemExit('--side required')
        run_side(a.side, a.programs or P.PROGRAMS)
    elif a.cmd == 'summarize':
        summarize()
        spot()
    else:
        build()
        if not toy():
            raise SystemExit('toy FAILED: the corpus is not run; see out/toy/check.txt')
        for s in SIDES:
            check_lock(a.beside_lock)
            run_side(s, P.PROGRAMS)
        summarize()
        spot()


if __name__ == '__main__':
    main()
