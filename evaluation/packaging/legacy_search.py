#!/usr/bin/env python3
"""Option 3A: which modules of the crates beside the pointer pass's own ship is decided by the compiler, not by hand.

usage: legacy_search.py search <list>   cut the legacy rewriter to the two items the pointer pass reads (item cuts below),
                                        then remove module subtrees one at a time, top-down, keeping a removal when
                                        `cargo check` of the derived tree reports no error; repeat until a whole round
                                        removes nothing; then drop the crate dependencies the compiler reports unused in
                                        the crates searched. Writes every removal to <list>.
       legacy_search.py apply <list>    the item cuts, then a list made by `search`, entry by entry; stops at an entry
                                        that does not apply (the head is not the one the list was made for)
       legacy_search.py deps                    drops the crate dependencies the compiler reports unused (below)
Environment: W (the derived worktree), CARGO (default cargo), CHECK_TARGET (cargo target of the checks),
  SEARCH_CRATES (default: pointer_replacer passes points_to utils),
  ITEM_CUTS (a script run instead of the built-in item cuts: the frozen source's legacy rewriter shares the pointer
    pass's crate, and option3.py cuts it there), SEARCH_SKIP (module files or directories, relative to W, never tried:
    the pointer pass's own modules), SEARCH_DEPS / SEARCH_ALLOW (default 1: `search` also lists the unused
    dependencies / the #![allow(warnings)] roots; 0 leaves them to later steps)"""
import os, re, shutil, subprocess, sys, tempfile
sys.dont_write_bytecode = True; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from modscan import decls
W = os.environ['W'].rstrip('/')
CARGO = os.environ.get('CARGO', 'cargo').split()
CRATES = os.environ.get('SEARCH_CRATES', 'pointer_replacer passes points_to utils').split()
SKIP = os.environ.get('SEARCH_SKIP', '').split()
MOD = re.compile(r'^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?mod[ \t]+([A-Za-z_]\w*)[ \t]*;[ \t]*\n', re.M)

def item_cuts():
    """The legacy rewriter keeps `collector::collect_fn_ptrs` and `diagnostics::DiagnosticsMode`, which the pointer pass
    reads; nothing else of it ships, and the crate root exports none of the legacy pass's entry points. ITEM_CUTS names
    a script that makes the cuts instead."""
    if os.environ.get('ITEM_CUTS'):
        r = subprocess.run([sys.executable, '-I', os.environ['ITEM_CUTS']])
        assert r.returncode == 0, 'option 3A: the item cuts failed: ' + os.environ['ITEM_CUTS']
        return
    R = W + '/crates/pointer_replacer/src/rewriter/'
    s = open(R + 'collector.rs').read()
    i = s.index('pub fn collect_fn_ptrs(')
    open(R + 'collector.rs', 'w').write('''use rustc_hash::FxHashSet;
use rustc_hir::{
    ExprKind, QPath, TyKind,
    def::{DefKind, Res},
    intravisit::{Visitor, walk_expr},
};
use rustc_span::def_id::LocalDefId;

use crate::utils::rustc::RustProgram;

''' + s[i:])
    s = open(R + 'diagnostics.rs').read()
    i = s.index('#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum DiagnosticsMode {')
    j = s.index('impl DiagnosticsMode {'); k = s.index('\n}\n', j) + 3
    open(R + 'diagnostics.rs', 'w').write(s[i:k])
    open(R + 'mod.rs', 'w').write('pub mod collector;\npub mod diagnostics;\n')
    p = W + '/crates/pointer_replacer/src/lib.rs'; s = open(p).read()
    s2 = re.sub(r'\npub use rewriter::\{[^}]*\};\n', '\n', s, flags=re.S)
    assert s2 != s, 'the legacy crate root exports no rewriter items: the head is not the one this cut was written for'
    open(p, 'w').write(s2)
    print('   item cuts: rewriter/ = collector::collect_fn_ptrs + diagnostics::DiagnosticsMode; lib.rs exports no rewriter item')

def is_root(f):
    b = os.path.basename(f); return b in ('lib.rs', 'main.rs', 'mod.rs')

def children(f):
    """(name, the declaring file, the module's .rs file or None, its directory or None) for every file module of f."""
    src = open(f).read(); d = os.path.dirname(f)
    out = []
    for n, inline, _ in decls(src):
        base = os.path.join(d if is_root(f) else os.path.join(d, os.path.splitext(os.path.basename(f))[0]), *inline)
        rs = f'{base}/{n}.rs'; dr = f'{base}/{n}'
        rs = rs if os.path.isfile(rs) else (f'{dr}/mod.rs' if os.path.isfile(f'{dr}/mod.rs') else None)
        if rs is None: continue
        out.append((n, f, rs, dr if os.path.isdir(dr) else None))
    return out

def rel(p): return p[len(W) + 1:]

def remove(n, decl, rs, dr):
    """Removes `mod n;` (with the attribute lines just above it) and `use` items of `n::` / `self::n::` from the declaring
    file, and the module's files. Returns an undo function."""
    src = open(decl).read()
    lines = src.split('\n'); out = []; i = 0; hit = 0
    use = re.compile(r'^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?use[ \t]+(?:self::)?' + n + r'(?:::|;)')
    decl_re = re.compile(r'^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?mod[ \t]+' + n + r'[ \t]*;[ \t]*$')
    while i < len(lines):
        l = lines[i]
        if decl_re.match(l):
            while out and re.match(r'^[ \t]*#\[[^\]]*\][ \t]*$', out[-1]): out.pop()
            hit += 1; i += 1; continue
        if use.match(l):
            while not lines[i].rstrip().endswith(';'): i += 1
            i += 1; continue
        out.append(l); i += 1
    assert hit == 1, f'mod {n}; not found once in {rel(decl)}'
    tmp = tempfile.mkdtemp(dir=os.environ.get('ZS') or None)
    shutil.copy2(decl, tmp + '/decl')
    moved = []
    paths = [dr] if dr and rs.startswith(dr + '/') else [x for x in (rs, dr) if x and os.path.exists(x)]
    for k, p in enumerate(paths):
        dst = f'{tmp}/{k}'; shutil.move(p, dst); moved.append((dst, p))
    open(decl, 'w').write('\n'.join(out))
    def undo():
        shutil.copy2(tmp + '/decl', decl)
        for dst, p in reversed(moved): shutil.move(dst, p)
        shutil.rmtree(tmp)
        # The restored files keep their old modification times, and the failed check's dep-info no longer lists the
        # restored module: without a fresh time on the declaring file cargo would take the crate as up to date and
        # reuse the metadata built without the module.
        os.utime(decl, None)
    def done(): shutil.rmtree(tmp)
    return undo, done

def check(log):
    r = subprocess.run(CARGO + ['check', '--manifest-path', W + '/Cargo.toml', '--message-format', 'short'],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    open(log, 'w').write(r.stdout)
    return r.returncode == 0

def modules():
    """Every file module of the searched crates: its .rs file -> (name, the declaring file, the .rs file, its directory)."""
    out = {}
    def walk(f):
        for c in children(f):
            out[c[2]] = c; walk(c[2])
    for c in CRATES:
        root = f'{W}/crates/{c}/src/lib.rs'
        if os.path.isfile(root): walk(root)
    return out

def repair(log, removed):
    """After the item cuts, the modules that read the cut part of the legacy rewriter fail to compile: each module the
    compiler reports an error in is removed, until the tree checks. An error outside the searched crates, or in a crate
    root, stops the search: the cut would take something the pointer pass reads."""
    n = 0
    while not check(log):
        n += 1; assert n <= 100, 'option 3A: the item cuts do not converge: ' + log
        files = sorted(set(re.findall(r'^(\S+\.rs):\d+:\d+: error', open(log).read(), re.M)))
        mods = modules(); hit = []
        for f in files:
            a = os.path.normpath(os.path.join(W, f))
            assert a in mods, f'option 3A: an error in {f}, which is not a module the search may remove: {log}'
            hit.append(mods[a])
        for name, decl, rs, dr in hit:
            if not os.path.exists(rs): continue
            _, done = remove(name, decl, rs, dr); done(); removed.append((rel(decl), name))
            print(f'   after the item cuts: removed {rel(decl)} mod {name} (it reads the cut rewriter)', flush=True)
    return n

def search(listfile):
    item_cuts()
    log = os.environ.get('CHECK_LOG', '/dev/null')
    removed = []; rnd = 0
    n_checks = repair(log, removed) + 1
    verdicts = open(listfile + '.verdicts.tsv', 'w')
    verdicts.write('round\tdeclared in\tmodule\tverdict\tthe first error when removed\n')
    while True:
        rnd += 1; before = len(removed)
        for c in CRATES:
            root = f'{W}/crates/{c}/src/lib.rs'
            if not os.path.isfile(root): continue
            todo = children(root)
            while todo:
                n, decl, rs, dr = todo.pop(0)
                if not os.path.exists(rs): continue
                if any(rel(x).startswith(k) for k in SKIP for x in (rs, dr) if x): continue
                undo, done = remove(n, decl, rs, dr); n_checks += 1
                if check(log):
                    done(); removed.append((rel(decl), n)); print(f'   round {rnd}: removed {rel(decl)} mod {n}', flush=True)
                    verdicts.write(f'{rnd}\t{rel(decl)}\t{n}\tremoved\t\n')
                else:
                    first = next((l for l in open(log) if ': error' in l or l.startswith('error')), '').strip()[:300]
                    verdicts.write(f'{rnd}\t{rel(decl)}\t{n}\tkept\t{first}\n')
                    undo(); todo = children(rs) + todo
                verdicts.flush()
        print(f'   round {rnd}: {len(removed) - before} removed ({n_checks} checks so far)', flush=True)
        if len(removed) == before: break
    deps = unused_deps() if os.environ.get('SEARCH_DEPS', '1') == '1' else []
    allows = allow_where_warned(log) if os.environ.get('SEARCH_ALLOW', '1') == '1' else []
    with open(listfile, 'w') as f:
        f.write('# option 3A, made by legacy_search.py search: the module removals (declaring file, module), the crate\n'
                '# dependencies the compiler then reports unused, and the trimmed crates whose roots then need\n'
                '# #![allow(warnings)] (the cut leaves unused extern crates and dead items behind), in the order applied\n')
        for d, n in removed: f.write(f'mod\t{d}\t{n}\n')
        for t, n in deps: f.write(f'dep\t{t}\t{n}\n')
        for r in allows: f.write(f'allow\t{r}\t#![allow(warnings)]\n')
    print(f'   option 3A: {len(removed)} module subtrees removed, {len(deps)} dependencies dropped, {len(allows)} crate roots '
          f'given #![allow(warnings)], {n_checks} checks; list {listfile}')

def allow_where_warned(log):
    """One more check; every searched crate that still warns gets #![allow(warnings)] at its root."""
    assert check(log), 'option 3A: the tree does not check after the dependencies were dropped: ' + log
    roots = []
    for m in re.finditer(r'^warning: `(\w+)` \(lib\) generated (\d+) warnings?', open(log).read(), re.M):
        if m.group(1) in CRATES:
            r = f'crates/{m.group(1)}/src/lib.rs'; add_allow(r); roots.append(r)
            print(f'   {m.group(1)}: {m.group(2)} warnings after the cut -> #![allow(warnings)] at {r}')
    return roots

def add_allow(r):
    p = f'{W}/{r}'; lines = open(p).read().split('\n'); last = -1
    for i, l in enumerate(lines):
        t = l.strip()
        if t.startswith('#!['): last = i
        elif t == '' or t.startswith('//'): continue
        else: break
    lines.insert(last + 1, '#![allow(warnings)]'); open(p, 'w').write('\n'.join(lines))

def unused_deps():
    """`-W unused_crate_dependencies` over the searched crates and the driver; drops what it reports there."""
    env = dict(os.environ, RUSTFLAGS=(os.environ.get('RUSTFLAGS', '') + ' -W unused_crate_dependencies').strip(),
               CARGO_TARGET_DIR=os.environ.get('CHECK_TARGET', W + '/target') + '-deps')
    r = subprocess.run(CARGO + ['check', '--manifest-path', W + '/Cargo.toml', '--message-format', 'short'],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
    found = []
    open(os.environ.get('CHECK_LOG', '/dev/null') + '-deps' if os.environ.get('CHECK_LOG') else '/dev/null', 'w').write(r.stdout)
    for m in re.finditer(r'extern crate `(\w+)` is unused in crate `(\w+)`', r.stdout):
        dep, crate = m.groups()
        toml = 'Cargo.toml' if crate == 'jobcrat' or crate == 'crat' else next((f'crates/{c}/Cargo.toml' for c in CRATES if c == crate), None)
        if toml and (toml, dep.replace('_', '[-_]')) not in found: found.append((toml, dep.replace('_', '[-_]')))
        elif toml: pass
        else: print(f'   unused dependency outside the searched crates (reported, not dropped): {dep} in {crate}')
    for t, d in found: drop_dep(t, d)
    return found

def drop_dep(toml, pat):
    """Drops a dependency from the manifest's [dependencies] table (never from [workspace.dependencies])."""
    p = f'{W}/{toml}'; s = open(p).read()
    m = re.search(r'^\[dependencies\][ \t]*\n(.*?)(?=^\[|\Z)', s, flags=re.M | re.S)
    assert m, f'no [dependencies] in {toml}'
    body, k = re.subn(r'^' + pat + r'(?:\.workspace)?[ \t]*=[^\n]*\n', '', m.group(1), count=1, flags=re.M)
    assert k == 1, f'dependency {pat} not found in the [dependencies] of {toml}'
    open(p, 'w').write(s[:m.start(1)] + body + s[m.end(1):]); print(f'   dependency dropped: {toml} {pat}')

def apply(listfile):
    item_cuts(); n = d = w = 0
    for line in open(listfile):
        if line.startswith('#') or not line.strip(): continue
        kind, a, b = line.rstrip('\n').split('\t')
        if kind == 'mod':
            decl = f'{W}/{a}'
            hit = next((c for c in children(decl) if c[0] == b), None)
            assert hit, f'option 3A list: mod {b} not declared in {a}; make the list again for this head (legacy_search.py search)'
            _, done = remove(*hit); done(); n += 1
        elif kind == 'dep':
            drop_dep(a, b); d += 1
        else:
            add_allow(a); w += 1
    print(f'   option 3A from {os.path.basename(listfile)}: {n} module subtrees removed, {d} dependencies dropped, '
          f'{w} crate roots given #![allow(warnings)]')

def deps(_=None):
    found = unused_deps()
    print(f'   unused crate dependencies dropped: {len(found)}' + ''.join(f'; {t} {d}' for t, d in found))

if __name__ == '__main__':
    {'search': search, 'apply': apply, 'deps': deps}[sys.argv[1]](*sys.argv[2:])
