#!/usr/bin/env python3
"""Step 6: the code the compiler reports dead leaves the derived tree, to a fixpoint. Each round:
  1. `cargo fix` applies the compiler's machine-applicable suggestions (unused imports and extern crates, `mut`,
     unused variables); cargo checks the result itself and keeps nothing that does not compile;
  2. `cargo check`: every item a `dead_code` warning names as never used (a function, constant, static, type alias,
     trait, macro, enum, union, or an inherent impl's associated item) is cut by `itemcut`, with its attributes. Fields
     never read, variants never constructed and types never constructed stay (counted, not cut);
  3. `cargo check` again: if the cuts do not compile, they are undone and made again file group by file group,
     halving a failing group, and an item whose cut alone fails stays (counted).
`--force-warn` makes the lints fire where an `allow` attribute would hide them. The round's state is committed in W.
Stops when a round changes nothing.
usage: deadcut.py   Environment: W, ZS (logs), CARGO (default cargo), TOOLS (the helper binaries), DEADCUT_TARGET
       (cargo target of its checks), DEADCUT_ROUNDS (default 20)"""
import collections, json, os, re, subprocess, sys
W = os.environ['W'].rstrip('/'); ZS = os.environ['ZS']
CARGO = os.environ.get('CARGO', 'cargo').split(); TOOLS = os.environ['TOOLS']
ROUNDS = int(os.environ.get('DEADCUT_ROUNDS', '20'))
LINTS = ['dead_code', 'unused_imports', 'unused_extern_crates', 'unused_mut', 'unused_variables', 'unused_macros']
ENV = dict(os.environ, CARGO_TARGET_DIR=os.environ.get('DEADCUT_TARGET', ZS + '/deadcut-target'),
           RUSTFLAGS=(os.environ.get('RUSTFLAGS', '') + ' ' + ' '.join('--force-warn ' + l for l in LINTS)).strip())
ENV.pop('RUSTC_WRAPPER', None)  # cargo fix drives rustc itself
NOT_CUT = re.compile(r'\b(field|fields|variant|variants)\b|never read|never constructed')
log = open(ZS + '/deadcut.log', 'a'); cuts_tsv = open(ZS + '/deadcut.tsv', 'a')

def cargo(args, tag):
    r = subprocess.run(CARGO + args + ['--manifest-path', W + '/Cargo.toml'], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, text=True, env=ENV)
    open(f'{ZS}/deadcut-{tag}.out', 'w').write(r.stdout); open(f'{ZS}/deadcut-{tag}.err', 'w').write(r.stderr)
    return r

def git(*a):
    return subprocess.run(['git', '-C', W] + list(a), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True).stdout

def commit(msg):
    git('add', '-A')
    subprocess.run(['git', '-C', W, '-c', 'user.name=submission', '-c', 'user.email=submission@localhost', 'commit',
                    '-q', '-m', msg], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def ours(path):
    a = os.path.normpath(path if os.path.isabs(path) else os.path.join(W, path))
    r = os.path.relpath(a, W)
    return r if re.match(r'^(crates|src|deps_crate)/', r) and r.endswith('.rs') else None

def diagnostics(tag):
    """(warnings by lint, the dead items to cut [(file, line, name)], the dead items that stay [(file, line, message)],
    errors) of one `cargo check`."""
    r = cargo(['check', '--message-format=json'], tag)
    by_lint = collections.Counter(); cut = []; stay = []; errors = 0
    for line in r.stdout.splitlines():
        try: m = json.loads(line)
        except ValueError: continue
        if m.get('reason') != 'compiler-message': continue
        d = m['message']; code = (d.get('code') or {}).get('code')
        prim = [s for s in d.get('spans', []) if s.get('is_primary')]
        if d.get('level') == 'error':
            errors += 1; continue
        if d.get('level') != 'warning' or not prim or not any(ours(s['file_name']) for s in prim): continue
        by_lint[code or d['message'][:40]] += 1
        if code not in ('dead_code', 'unused_macros'): continue
        for s in prim:
            f = ours(s['file_name'])
            if not f: continue
            t = s['text'][0]['text'] if s.get('text') else ''
            name = t[s['text'][0]['highlight_start'] - 1:s['text'][0]['highlight_end'] - 1] if t else ''
            if NOT_CUT.search(d['message']) or s.get('expansion') or not re.fullmatch(r'[A-Za-z_]\w*', name):
                stay.append((f, s['line_start'], d['message']))
            else:
                cut.append((f, s['line_start'], name))
    return by_lint, sorted(set(cut)), stay, errors

def itemcut(items):
    if not items: return []
    r = subprocess.run([TOOLS + '/itemcut', W], input=''.join(f'{f}\t{l}\t{n}\n' for f, l, n in items),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    log.write(r.stdout); log.flush()
    return [l.split('\t') for l in r.stdout.splitlines() if l.startswith('CUT\t')]

def checks():
    r = cargo(['check', '--message-format=short'], 'verify')
    return r.returncode == 0

def cut_groups(groups, rnd):
    """Cuts each group of files' items; keeps a group whose cuts check, halves one that does not."""
    kept, failed = [], []
    for g in groups:
        done = itemcut([i for f in g for i in f[1]])
        if checks():
            commit(f'deadcut round {rnd}'); kept += done
        else:
            git('checkout', '--', '.')
            if len(g) == 1 and len(g[0][1]) == 1: failed += g[0][1]
            elif len(g) == 1:
                items = g[0][1]; h = len(items) // 2
                k, fl = cut_groups([[(g[0][0], items[:h])], [(g[0][0], items[h:])]], rnd); kept += k; failed += fl
            else:
                h = len(g) // 2
                k, fl = cut_groups([g[:h], g[h:]], rnd); kept += k; failed += fl
    return kept, failed

def main():
    commit('deadcut: start')
    first = None; total_cut = 0; failed_all = []
    for rnd in range(1, ROUNDS + 1):
        before = git('rev-parse', 'HEAD').strip()
        cargo(['fix', '--allow-dirty', '--allow-staged', '--allow-no-vcs', '--workspace'], f'fix-{rnd}')
        fixed = git('diff', '--stat').strip().splitlines()
        commit(f'deadcut round {rnd}: cargo fix')
        by_lint, cut, stay, errors = diagnostics(f'check-{rnd}')
        if errors: print(f'   deadcut round {rnd}: the tree does not check ({errors} errors): {ZS}/deadcut-check-{rnd}.out'); sys.exit(1)
        first = first or by_lint
        cut = [i for i in cut if (i[0], i[2]) not in {(f, n) for f, _, n in failed_all}]
        files = collections.OrderedDict()
        for f, l, n in cut: files.setdefault(f, []).append((f, l, n))
        kept, failed = cut_groups([list(files.items())], rnd) if files else ([], [])
        failed_all += failed; total_cut += len(kept)
        for c in kept: cuts_tsv.write(f'{rnd}\t' + '\t'.join(c[1:]) + '\n')
        cuts_tsv.flush()
        print(f'   deadcut round {rnd}: cargo fix changed {max(len(fixed) - 1, 0)} files; warnings '
              + ', '.join(f'{k} {v}' for k, v in by_lint.most_common()) + f'; {len(kept)} items cut, {len(failed)} cuts do not check',
              flush=True)
        if git('rev-parse', 'HEAD').strip() == before or (not fixed and not kept): break
    by_lint, cut, stay, errors = diagnostics('final')
    assert errors == 0, 'deadcut: the final tree does not check'
    kinds = collections.Counter(re.sub(r'`[^`]*`', '`…`', m) for _, _, m in stay)
    open(ZS + '/deadcut-left.tsv', 'w').write(''.join(f'{f}\t{l}\t{m}\n' for f, l, m in stay))
    print(f'   deadcut: {total_cut} items cut in {rnd} rounds; warnings at the start (allow attributes overridden): '
          + (', '.join(f'{k} {v}' for k, v in first.most_common()) or '0') + '; at the end: '
          + (', '.join(f'{k} {v}' for k, v in by_lint.most_common()) or '0'))
    print(f'   deadcut: left (not cut by rule): {len(stay)} -- ' + '; '.join(f'{v} {k}' for k, v in kinds.most_common(8))
          + f'; cuts that do not check: {len(failed_all)}; lists {ZS}/deadcut.tsv, {ZS}/deadcut-left.tsv')

if __name__ == '__main__':
    main()
