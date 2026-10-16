#!/usr/bin/env python3
"""Runs the typed counter (T1 positions, T2 uses) on every tree rq1 reads, one crate per call, and CROWN's declaration
counter on CROWN's twenty as the control on CROWN's population.

Sides (results/rq1/counter/<side>/<p>/{status,positions,uses,universe-unmapped}.txt|tsv):
  input            benchmarks/crown/<p>, the twenty as C2Rust emitted them
  ours             the emitted trees ($TREES/<p>); under --small without lil and brotli
  crown            CROWN's output trees (third party)
  laertes          the Laertes trees CROWN's artifact distributes (comparison/laertes-crown/after/<p>, or the
                   laertes-laertes tree laertes-path names, laid out flat: keys read without `src::`)
  laertes_before   the tree Laertes transformed (the same path under before/)
  urlparser-roottest/{laertes,laertes_before}  urlparser's Laertes trees have test.rs as their crate root; CROWN's
                   universe keys are read there without the root file's `test::` segment
Every run passes CROWN's universe (fn_data, depth 0, Mut and Ptr) for the `official` columns when CROWN's analysis is
present; positions and `full_roots` do not read it. A Laertes tree is adapted two ways, both mechanical: `llvm_asm!`
sites become `asm!` (adapt_llvm_asm.py), and the feature gates nightly-2025-06-23 reports removed (E0557) are deleted
from `#![feature(..)]` in a copy of the tree.
usage: count.py            (environment: common.py)"""
import os, re, shutil, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402

ADAPT = os.path.join(C.HERE, 'adapt_llvm_asm.py')
JOBS = int(os.environ.get('RQ1_JOBS', '4'))


def sysroot():
    return subprocess.run(['rustc', f'+{C.TOOLCHAIN}', '--print', 'sysroot'], capture_output=True, text=True,
                          check=True).stdout.strip()


SR = sysroot()
ENV = dict(os.environ, SYSROOT=SR, LD_LIBRARY_PATH=f'{SR}/lib', DIR=C.SRC, RUSTUP_TOOLCHAIN=C.TOOLCHAIN)


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
                    b = a + len(mark[a:].split(' ')[0])
                    names.add(code[a:b].strip())
                    break
    return {n for n in names if n and n.replace('_', '').isalnum()}


def shim_tree(dest_root, d, root, removed):
    shim = os.path.join(dest_root, 'shim')
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
    return nroot


def has_llvm_asm(d):
    for dp, _, fs in os.walk(d):
        for f in fs:
            if f.endswith('.rs') and 'llvm_asm!' in open(os.path.join(dp, f), errors='replace').read():
                return True
    return False


def universe_file(p, flat, roottest=False):
    keys = C.universe(p)
    if flat:
        keys = {C.unsrc(k) for k in keys}
    if roottest:
        keys = {k[len('test::'):] if k.startswith('test::') else k for k in keys}
    uf = os.path.join(C.WORK, 'universe', f'{p}{"-flat" if flat else ""}{"-roottest" if roottest else ""}.txt')
    os.makedirs(os.path.dirname(uf), exist_ok=True)
    open(uf, 'w').write('\n'.join(sorted(keys)) + '\n')
    return uf


def tree_of(side, p):
    if side == 'input':
        return os.path.join(C.INPUT, p), False
    if side == 'ours':
        return os.path.join(C.TREES, p), False
    if side == 'crown':
        return os.path.join(C.CROWN, p), False
    d, flat = C.laertes_root(p)
    if d is not None and side == 'laertes_before':
        d = d.replace(os.sep + 'after' + os.sep, os.sep + 'before' + os.sep)
    return d, flat


def run_one(side, p, dest, roottest=False):
    d, flat = tree_of(side, p)
    os.makedirs(dest, exist_ok=True)
    for f in os.listdir(dest):
        q = os.path.join(dest, f)
        shutil.rmtree(q) if os.path.isdir(q) else os.remove(q)
    if not d or not os.path.isdir(d) or not C.root_of(d):
        open(os.path.join(dest, 'status.txt'), 'w').write('no-tree\n')
        return side, p, 'no-tree'
    note = []
    if side.startswith('laertes') and has_llvm_asm(d):
        ad = os.path.join(dest, 'adapted')
        subprocess.run(['python3', ADAPT, d, ad], check=True, capture_output=True, text=True)
        note.append('llvm_asm! adapted')
        d = ad
    r = C.root_of(d)
    uf = universe_file(p, flat, roottest)
    cmd = ['nice', '-n', '10', C.TYPED, '--root', r, '--out', dest, '--universe', uf] + (['--strip-src'] if flat else [])
    pr = subprocess.run(cmd, env=ENV, capture_output=True, text=True)
    if pr.returncode and side.startswith('laertes'):
        removed = removed_features(pr.stderr)
        if removed:
            r = shim_tree(dest, d, r, removed)
            cmd = cmd[:4] + ['--root', r] + cmd[6:]
            pr = subprocess.run(cmd, env=ENV, capture_output=True, text=True)
            note.append('removed feature gates: ' + ','.join(sorted(removed)))
    if pr.returncode:
        open(os.path.join(dest, 'stderr.txt'), 'w').write(pr.stderr[-20000:])
        if not os.path.exists(os.path.join(dest, 'status.txt')):
            open(os.path.join(dest, 'status.txt'), 'w').write(f'exit-{pr.returncode}\n')
    open(os.path.join(dest, 'flat.txt'), 'w').write('flat\n' if flat else 'tree\n')
    open(os.path.join(dest, 'note.txt'), 'w').write('; '.join(note) + '\n')
    return side, p, C.status(dest)


def control():
    """CROWN's declaration counter on CROWN's own twenty must reproduce CROWN's evaluation table (plain and with the
    inline-module reading) before any key on CROWN's population is written. Writes counter/crown-control.txt."""
    ev = C.evaluation()
    out = os.path.join(C.WORK, 'crown-control.txt')
    if not ev or not all(C.have_crown(p) for p in C.PROGS):
        open(out, 'w').write('absent\tCROWN\'s outputs or evaluation table not present\n')
        return
    bad = []
    for p in C.PROGS:
        for flags in ((), ('inline-mods',)):
            o = subprocess.run([C.DECL, os.path.join(C.CROWN, p), os.path.join(C.CROWN, p, 'analysis_results')]
                               + list(flags), capture_output=True, text=True)
            d = dict(x.split('=') for x in o.stdout.split()) if o.returncode == 0 else {}
            if (int(d.get('universe', -1)), int(d.get('after', -1))) != ev[p][:2] or d.get('parse_failures') != '0':
                bad.append(f'{p} {flags}: {d or o.stderr[-200:]} vs {ev[p][:2]}')
    open(out, 'w').write(('ok\t20 / 20, plain and inline-mods\n' if not bad else 'FAILED\n' + '\n'.join(bad) + '\n'))


def main():
    for exe in (C.TYPED, C.DECL):
        if not os.access(exe, os.X_OK):
            sys.exit(f'count.py: {exe} not built (run rq1/build.sh)')
    jobs = [(s, p, os.path.join(C.WORK, s, p), False) for s in ('input', 'crown', 'laertes', 'laertes_before')
            for p in C.PROGS]
    jobs += [('ours', p, os.path.join(C.WORK, 'ours', p), False) for p in C.ours_programs()]
    jobs += [(s, 'urlparser', os.path.join(C.WORK, 'urlparser-roottest', s, 'urlparser'), True)
             for s in ('laertes', 'laertes_before')]
    with ThreadPoolExecutor(JOBS) as ex:
        for side, p, st in ex.map(lambda j: run_one(*j), jobs):
            print(f'counter {side} {p}: {st}', flush=True)
    control()
    print('crown control:', open(os.path.join(C.WORK, 'crown-control.txt')).readline().strip())


if __name__ == '__main__':
    main()
