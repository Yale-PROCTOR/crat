#!/usr/bin/env python3
"""pos_census.py — analysis-fanout 031 (relay 043, R753-1): crat's typed pointer-position counter, two scopes.

  pos_census.py run --side {input,crown,laertes,ours} --out DIR [--census CENSUS] [PROG ...]
  pos_census.py calibrate --out DIR          # fail-closed: official on CROWN's outputs; the usage rule on the inputs
  pos_census.py summarize --out DIR          # T1 / T2 tables, both scopes, the joins (no key written)

The counter is `pos_counter/` (a rustc driver under crat's nightly-2025-06-23, one crate per call; its header defines
every column). This script runs it per (side, program) and reads its tables.

- `official` = CROWN's universe (`seed_numbers.crown_universe`: the artifact's `fn_data` d0 `Mut` ∩ `Ptr` keys). A key
  is SAFE when every binding of that name in its function has, at depth 0, a reference- or Box-family form (the
  families of CROWN's inventory walker, `crown_artifact_inventory/src/lib.rs:817-888`). On CROWN's twenty outputs it
  must reproduce `evaluation.tsv` 2,414 -> 1,711, 20 / 20; else nothing is summarized.
- `full` (§2.4): T1 = every pointer-like layer of every declaration (params, returns, locals typed or not, fields,
  statics; every depth; array elements and function-pointer signatures marked by `ctx`), RAW = `raw-*`, `opt-raw-*`,
  `nonnull`, `opt-nonnull`; `byref` bindings (c2rust's `let ref mut freshN`, a reference to an existing place whose
  layers are the place's own) are reported, not counted. T2 = `full_roots` (the counter's header).
- Joins across sides: a field is keyed by its struct's NAME (the distributed input re-declares each header struct in
  every module that includes it; CROWN's and our trees keep one; the duplicates are dropped and counted); every other
  position by its function path less a leading `src::` (Laertes's flat layouts).
- The twin: our trees keep each C-named function with the C signature and move its body to `__crat_safe_<f>`. The
  `twin` reading takes `__crat_safe_<f>`'s rows as `<f>`'s; both readings are reported."""
import argparse, csv, json, os, subprocess, sys, time
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'record'))
import seed_numbers as SN  # noqa: E402
sys.path.insert(0, HERE)
import seed_rq2 as SR  # noqa: E402

csv.field_size_limit(10**9)
CRAT = SN.CRAT
INPUT = f'{CRAT}/benchmarks/rs-crown'
CROWN = SN.CROWN
TOOLCHAIN = 'nightly-2025-06-23'
TARGET = os.environ.get('POS_TARGET', 'scratch/analysis-fanout/r043/target')
EXE = os.path.join(TARGET, 'release', 'rq2_pos_counter')
PROGRAMS = SN.PROGRAMS
SAFE = {'ref', 'mut-ref', 'slice-ref', 'slice-mut', 'str-ref', 'box', 'box-slice'}
SAFE |= {f'opt-{f}' for f in set(SAFE)}
RAW = {'raw-mut', 'raw-const', 'opt-raw-mut', 'opt-raw-const', 'nonnull', 'opt-nonnull'}
ARRAY_FORMS = {'slice-ref', 'slice-mut', 'box-slice', 'cursor', 'cursor-mut'}
ARRAY_FORMS |= {f'opt-{f}' for f in set(ARRAY_FORMS)}
USAGE_2025 = f'{CRAT}/docs/agents/tasks/2026-07-28-crown-usage-metric-candidates.csv'
TWIN = '__crat_safe_'


# --------------------------------------------------------------------------------------------------------------- run

def root_of(d):
    for f in ('lib.rs', 'c2rust-lib.rs', 'src/lib.rs', 'rust/src/lib.rs', 'test.rs'):
        if os.path.exists(os.path.join(d, f)):
            return os.path.join(d, f)
    return None


def side_dir(side, prog, census=None):
    if side == 'input':
        return f'{INPUT}/{prog}', False
    if side == 'crown':
        return f'{CROWN}/{prog}', False
    if side == 'laertes':
        return SR.laertes_root(prog)
    if side == 'ours':
        return os.path.join(census, 'emitted-trees', prog), False
    raise SystemExit(f'unknown side {side}')


def strip(k):
    return k[5:] if k.startswith('src::') else k


def universe(prog, flat=False):
    u = SN.crown_universe(prog)
    return {strip(k) for k in u} if flat else u


def sysroot():
    return subprocess.run(['rustc', f'+{TOOLCHAIN}', '--print', 'sysroot'], capture_output=True, text=True,
                          check=True).stdout.strip()


def build():
    # the build slots (R438-1): every cargo invocation through crat-cargo.sh
    env = dict(os.environ, RUSTUP_TOOLCHAIN=TOOLCHAIN, CARGO_TARGET_DIR=TARGET, CRAT_LANE='analysis-fanout')
    subprocess.run(['bash', f'{CRAT}/docs/agents/tools/crat-cargo.sh', 'build', '--release', '--offline', '--quiet',
                    '--manifest-path', os.path.join(HERE, 'pos_counter', 'Cargo.toml')], env=env, check=True)
    return EXE


def removed_features(stderr):
    """The gate names rustc's E0557 points at: the caret span under each `#![feature(..)]` source line."""
    names, lines = set(), stderr.splitlines()
    for i, l in enumerate(lines):
        if 'E0557' in l and 'feature has been removed' in l:
            for j in range(i + 1, min(i + 6, len(lines) - 1)):
                src, car = lines[j], lines[j + 1]
                if '#![feature(' in src and '^' in car:
                    bar = src.index('|')
                    code, mark = src[bar + 1:], car[car.index('|') + 1:]
                    a = mark.index('^')
                    b = len(mark.rstrip()) if mark.rstrip().endswith('^') else mark.rindex('^') + 1
                    b = a + len(mark[a:].split(' ')[0])
                    names.add(code[a:b].strip())
                    break
    return {n for n in names if n and n.replace('_', '').isalnum()}


def shim_tree(out, prog, d, root, removed):
    import shutil, re
    shim = os.path.join(out, 'shim', 'laertes', prog)
    if os.path.exists(shim):
        shutil.rmtree(shim)
    shutil.copytree(d, shim, ignore=shutil.ignore_patterns('target', '*.o', '*.a'))
    nroot = os.path.join(shim, os.path.relpath(root, d))
    text = open(nroot).read()

    def fix(m):
        keep = [f.strip() for f in m.group(1).split(',') if f.strip() and f.strip() not in removed]
        return f'#![feature({", ".join(keep)})]' if keep else ''
    open(nroot, 'w').write(re.sub(r'#!\[feature\(([^)]*)\)\]', fix, text))
    if 'main' in removed:
        # the removed `main` gate's attribute: a bare `#[main]` line on an entry fn (an attribute only)
        for dp, _, fs in os.walk(shim):
            for f in fs:
                if f.endswith('.rs'):
                    pth = os.path.join(dp, f)
                    t = open(pth).read()
                    t2 = re.sub(r'(?m)^[ \t]*#\[main\][ \t]*\n', '', t)
                    if t2 != t:
                        open(pth, 'w').write(t2)
    return nroot, shim


MEM_FLOOR_GIB = int(os.environ.get('POS_MEM_FLOOR_GIB', '40'))


def mem_avail_gib():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'):
            return int(l.split()[1]) / 1048576
    return 0


def run(side, out, census, programs):
    exe = build()
    sr = sysroot()
    env = dict(os.environ, SYSROOT=sr, LD_LIBRARY_PATH=f'{sr}/lib', DIR=CRAT, RUSTUP_TOOLCHAIN=TOOLCHAIN)
    log = open(os.path.join(out, f'run-{side}.log'), 'a')
    for p in programs:
        d, flat = side_dir(side, p, census)
        dest = os.path.join(out, side, p)
        os.makedirs(dest, exist_ok=True)
        for f in ('positions.tsv', 'uses.tsv', 'universe-unmapped.txt', 'status.txt', 'stderr.txt'):
            if os.path.exists(os.path.join(dest, f)):
                os.remove(os.path.join(dest, f))
        r = root_of(d) if d and os.path.isdir(d) else None
        if not r:
            open(os.path.join(dest, 'status.txt'), 'w').write(f'no-tree\t{d}\n')
            print(f'{side}\t{p}\tno-tree\t{d}', file=log, flush=True)
            continue
        uf = os.path.join(out, 'universe', f'{p}{"-flat" if flat else ""}.txt')
        os.makedirs(os.path.dirname(uf), exist_ok=True)
        open(uf, 'w').write('\n'.join(sorted(universe(p, flat))) + '\n')
        while mem_avail_gib() < MEM_FLOOR_GIB:          # the memory-gated runner: beside main's census, never below
            print(f'{side} {p}: waiting for MemAvailable >= {MEM_FLOOR_GIB} GiB', flush=True)
            time.sleep(60)
        t0 = time.time()
        pr = subprocess.run(['/usr/bin/time', '-f', 'wall=%e maxrss_kb=%M', exe, '--root', r, '--out', dest,
                             '--universe', uf] + (['--strip-src'] if flat else []),
                            env=env, capture_output=True, text=True)
        tail = pr.stderr.strip().splitlines()
        if pr.returncode and side == 'laertes':
            # the feature-gate shim (Laertes's outputs only): a copy of the tree with exactly the gates that
            # nightly-2025-06-23 reports removed (E0557) deleted from `#![feature(..)]`; nothing else is touched
            removed = removed_features(pr.stderr)
            if removed:
                r, shim = shim_tree(out, p, d, r, removed)
                pr = subprocess.run(['/usr/bin/time', '-f', 'wall=%e maxrss_kb=%M', exe, '--root', r, '--out', dest,
                                     '--universe', uf] + (['--strip-src'] if flat else []),
                                    env=env, capture_output=True, text=True)
                tail = pr.stderr.strip().splitlines()
                open(os.path.join(dest, 'shim.txt'), 'w').write(f'removed feature gates: {",".join(sorted(removed))}\n'
                                                                f'shim tree: {shim}\n')
        st = 'ok' if pr.returncode == 0 else f'exit-{pr.returncode}'
        if pr.returncode:
            open(os.path.join(dest, 'stderr.txt'), 'w').write(pr.stderr[-20000:])
        open(os.path.join(dest, 'flat.txt'), 'w').write('flat\n' if flat else 'tree\n')
        print(f'{side}\t{p}\t{st}\t{r}\t{time.time() - t0:.1f}s\t{tail[-1] if tail else "-"}', file=log, flush=True)
        print(side, p, st, f'{time.time() - t0:.1f}s', flush=True)


# --------------------------------------------------------------------------------------------------------------- read

def status(out, side, prog):
    f = os.path.join(out, side, prog, 'status.txt')
    return open(f).read().split('\t')[0].strip() if os.path.exists(f) else 'no-run'


def is_flat(out, side, prog):
    f = os.path.join(out, side, prog, 'flat.txt')
    return os.path.exists(f) and open(f).read().strip() == 'flat'


def table(out, side, prog, name):
    if status(out, side, prog) != 'ok':
        return None
    return list(csv.DictReader(open(os.path.join(out, side, prog, name)), delimiter='\t'))


def detwin(owner):
    head, _, last = owner.rpartition('::')
    if last.startswith(TWIN):
        return (head + '::' if head else '') + last[len(TWIN):], True
    return owner, False


def twin_rows(rs):
    """`__crat_safe_<f>`'s rows read as `<f>`'s, replacing the C-named wrapper's params / return / locals."""
    twinned = {detwin(r['owner'])[0] for r in rs if detwin(r['owner'])[1]}
    out = []
    for r in rs:
        o, is_twin = detwin(r['owner'])
        if r['kind'] in ('param', 'return', 'local') and o in twinned and not is_twin:
            continue
        out.append(dict(r, owner=o))
    return out


def struct_name(owner):
    return owner.rpartition('::')[2]


def counted(rs):
    """The T1 population: every layer except a `byref` binding's."""
    return [r for r in rs if r['binding'] != 'byref']


def dedupe_fields(rs):
    """One copy of each same-named struct's fields (the first module's, by path order); returns (rows, dropped)."""
    keep, seen_struct, dropped = [], {}, 0
    for r in sorted(rs, key=lambda r: (r['kind'] != 'field', r['owner'])):
        if r['kind'] == 'field':
            first = seen_struct.setdefault(struct_name(r['owner']), r['owner'])
            if first != r['owner']:
                dropped += 1
                continue
        keep.append(r)
    return keep, dropped


def key(r):
    owner = struct_name(r['owner']) if r['kind'] == 'field' else strip(r['owner'])
    return (r['kind'], owner, r['name'], r['idx'] if r['kind'] in ('param', 'local') else '-', r['depth'], r['layer'])


# --------------------------------------------------------------------------------------------------------------- scopes

def official(rs, U, flat=False, twin=False):
    if twin:
        rs = twin_rows(rs)
    forms = defaultdict(list)
    for r in rs:
        if r['kind'] in ('param', 'local') and r['depth'] == '0' and r['layer'] == '0':
            k = f"{r['owner']}::{r['name']}"
            forms[strip(k) if flat else k].append(r['form'])
    safe_all = {k for k in U if forms.get(k) and all(f in SAFE for f in forms[k])}
    safe_any = {k for k in U if any(f in SAFE for f in forms.get(k, []))}
    unmapped = {k for k in U if k not in forms}
    return safe_all, safe_any, unmapped


def evaluation():
    ev = {}
    for r in csv.reader(open(os.path.join(CROWN, 'evaluation.tsv'))):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]))
    return ev


def usage_2025():
    return {r['program']: int(r['observed_usage']) for r in csv.DictReader(open(USAGE_2025))
            if r['candidate'] == 'deref-debug-roots'}


def calibrate(out):
    ev, u25 = evaluation(), usage_2025()
    lines, ok_decl, ok_use = [], True, True
    tb = ta = ta_any = 0
    for p in PROGRAMS:
        U = universe(p)
        rs = table(out, 'crown', p, 'positions.tsv')
        if rs is None:
            lines.append(f'official\t{p}\t{status(out, "crown", p)}')
            ok_decl = False
            continue
        sa, sy, un = official(rs, U)
        after, after_any = len(U) - len(sa), len(U) - len(sy)
        exact = (len(U), after) == ev[p]
        ok_decl &= exact
        tb, ta, ta_any = tb + len(U), ta + after, ta_any + after_any
        lines.append(f'official\t{p}\tbefore={len(U)}\tafter={after}\t(any-binding: {after_any})\t'
                     f'evaluation={ev[p][0]}->{ev[p][1]}\tunmapped={len(un)}\t{"exact" if exact else "MISMATCH"}')
    lines.append(f'official\tTOTAL\t{tb}->{ta}\t(any-binding: {ta_any})\tevaluation 2414->1711\t'
                 f'{"20/20" if ok_decl else "FAILED"}')
    tu = 0
    for p in PROGRAMS:
        us = table(out, 'input', p, 'uses.tsv')
        if us is None:
            lines.append(f'usage\t{p}\t{status(out, "input", p)}')
            ok_use = False
            continue
        n = sum(int(r['official']) for r in us)
        un = [l for l in open(os.path.join(out, 'input', p, 'universe-unmapped.txt')).read().splitlines() if l]
        tu += n
        ok = n == u25[p] and not un
        ok_use &= ok
        lines.append(f'usage\t{p}\t{n}\t2025-record={u25[p]}\tunmapped={len(un)}\t{"exact" if ok else "MISMATCH"}')
    lines.append(f'usage\tTOTAL\t{tu}\t2025-record={sum(u25.values())}\tthe paper (2023 MIR)=12,448\t'
                 f'{"20/20" if ok_use else "FAILED"}\tthe 2025 compiler against 2023: {100.0 * (tu - 12448) / 12448:+.1f}%')
    open(os.path.join(out, 'calibration.log'), 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(lines))
    if not (ok_decl and ok_use):
        raise SystemExit('calibration FAILED; nothing is summarized')


# --------------------------------------------------------------------------------------------------------------- full

def crown_arr(prog):
    """CROWN's fatness reading per (key, depth): fn_data `fn::var` and struct_data `Struct::field` (struct by name)."""
    j = json.load(open(os.path.join(CROWN, prog, 'analysis_results', 'fatness.json')))
    m = {}
    for fn, vs in j.get('fn_data', {}).items():
        for v, labels in vs.items():
            for d, lab in enumerate(labels):
                m[('fn', strip(fn), v, d)] = lab
    for st, fs in j.get('struct_data', {}).items():
        for f, labels in fs.items():
            for d, lab in enumerate(labels):
                m[('field', struct_name(st), f, d)] = lab
    return m


def arr_of(r, arrmap):
    if arrmap is None:
        return 'slice-form' if r['form'] in ARRAY_FORMS else '-'
    if r['kind'] == 'field':
        return arrmap.get(('field', struct_name(r['owner']), r['name'], int(r['depth'])), '-')
    if r['kind'] in ('param', 'local'):
        return arrmap.get(('fn', strip(r['owner']), r['name'], int(r['depth'])), '-')
    return '-'


def t1_summary(rs, arrmap):
    c = Counter()
    for r in rs:
        raw = r['form'] in RAW
        mut = 'mut' if 'raw-mut' in r['form'] else ('const' if 'raw-const' in r['form'] else '-')
        c[(r['kind'], 'raw' if raw else r['form'], mut, arr_of(r, arrmap), r['ctx'], r['synthetic'],
           min(int(r['depth']), 3))] += 1
    return c


def key_last(r):
    """The fallback key: the function by its last path segment (Laertes's own translations lay modules out
    differently); used only when the exact key misses and the last-segment key is unique on the output side."""
    k = key(r)
    return (k[0], k[1].rpartition('::')[2]) + k[2:] if r['kind'] != 'field' else k


def delivered(before_rows, after_rows):
    """Input raw layers whose position in the output holds a non-raw form (else raw, or unmatched)."""
    after, last, last_n = {}, {}, Counter()
    for r in after_rows:
        after.setdefault(key(r), r['form'])
        if key_last(r) not in last:
            last[key_last(r)] = r['form']
        last_n[(key_last(r), r['owner'])] += 0
    owners_per_last = Counter(k for k, _ in last_n)
    d = Counter()
    for r in before_rows:
        if r['form'] not in RAW:
            continue
        f = after.get(key(r))
        if f is None and owners_per_last.get(key_last(r)) == 1:
            f = last.get(key_last(r))
            if f is not None:
                d['matched_by_last_segment'] += 1
        d['before'] += 1
        if f is None:
            d['unmatched'] += 1
        elif f in RAW:
            d['raw'] += 1
        else:
            d['delivered'] += 1
            d[f'form:{f}'] += 1
    return d


def summarize(out):
    sides = [s for s in ('input', 'crown', 'laertes', 'ours') if os.path.isdir(os.path.join(out, s))]
    per, t1rows, missing = [], [], []
    forms = defaultdict(Counter)
    for p in PROGRAMS:
        rin_all = table(out, 'input', p, 'positions.tsv')
        arr = crown_arr(p)
        row = {'program': p}
        rin = None
        if rin_all is not None:
            rin, dropped = dedupe_fields(counted(rin_all))
            row['input.dup_field_layers'] = dropped
            row['input.byref_layers'] = len(rin_all) - len(counted(rin_all))
        for s in sides:
            rs_all = table(out, s, p, 'positions.tsv')
            if rs_all is None:
                missing.append((s, p, status(out, s, p)))
                continue
            rs = rin if s == 'input' else counted(rs_all)
            readings = [('', rs)] + ([('.twin', twin_rows(rs))] if s == 'ours' else [])
            for tag, r2 in readings:
                for k, n in sorted(t1_summary(r2, arr if s in ('input', 'crown') else None).items()):
                    t1rows.append([s + tag, p, *k, n])
                row[f'{s}{tag}.t1.raw'] = sum(1 for r in r2 if r['form'] in RAW)
                row[f'{s}{tag}.t1.safe'] = sum(1 for r in r2 if r['form'] not in RAW)
            us = table(out, s, p, 'uses.tsv')
            if us:
                for c in ('official', 'official_raw', 'full_roots', 'full_deref'):
                    row[f'{s}.t2.{c}'] = sum(int(r[c]) for r in us)
                row[f'{s}.t2.full_roots_in_wrappers'] = sum(int(r['full_roots']) for r in us if r['twin'] == 'wrapper')
            flat = is_flat(out, s, p)
            U = universe(p, flat)
            row[f'{s}.official.safe'] = len(official(rs, U, flat)[0])
            if s == 'ours':
                row['ours.official.safe_twin'] = len(official(rs, U, twin=True)[0])
            if s != 'input' and rin is not None:
                after = twin_rows(rs) if s == 'ours' else rs
                d = delivered(rin, after)
                row[f'{s}.pos.before'] = d['before']
                row[f'{s}.pos.delivered'] = d['delivered']
                row[f'{s}.pos.raw'] = d['raw']
                row[f'{s}.pos.unmatched'] = d['unmatched']
                for k, v in d.items():
                    if k.startswith('form:'):
                        forms[s][k[5:]] += v
                if s == 'ours':
                    row['ours.pos.delivered_no_twin'] = delivered(rin, rs)['delivered']
        per.append(row)
    cols = sorted({k for r in per for k in r if k != 'program'})
    with open(os.path.join(out, 'per-program.tsv'), 'w') as f:
        f.write('\t'.join(['program'] + cols) + '\n')
        for r in per:
            f.write('\t'.join([r['program']] + [str(r.get(c, '-')) for c in cols]) + '\n')
    with open(os.path.join(out, 't1-summary.tsv'), 'w') as f:
        f.write('side\tprogram\tkind\tform\tmutability\tarray\tctx\tsynthetic\tdepth(3=3+)\tcount\n')
        for r in t1rows:
            f.write('\t'.join(map(str, r)) + '\n')
    tot = {c: sum(r.get(c, 0) for r in per if isinstance(r.get(c, 0), int)) for c in cols}
    summary = {'totals': tot, 'delivered_forms': {s: dict(c.most_common()) for s, c in forms.items()},
               'missing': missing}
    json.dump(summary, open(os.path.join(out, 'summary.json'), 'w'), indent=1)
    print(json.dumps(summary, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['run', 'calibrate', 'summarize'])
    ap.add_argument('--side')
    ap.add_argument('--out', required=True)
    ap.add_argument('--census')
    ap.add_argument('programs', nargs='*')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    if a.cmd == 'run':
        run(a.side, a.out, a.census, a.programs or PROGRAMS)
    elif a.cmd == 'calibrate':
        calibrate(a.out)
    else:
        summarize(a.out)


if __name__ == '__main__':
    main()
