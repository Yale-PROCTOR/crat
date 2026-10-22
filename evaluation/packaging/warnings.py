#!/usr/bin/env python3
"""The compiler's warnings over the derived tree as its sources stand (no allow attribute added, none overridden), by
crate and lint; then `#![allow(warnings)]` at the root of each crate that still warns, so that the zip builds without
warnings. Prints the counts and the roots given the attribute.
Environment: W, ZS (logs), CARGO (default cargo), CHECK_TARGET (cargo target of the check)."""
import collections, json, os, re, subprocess
W = os.environ['W'].rstrip('/'); ZS = os.environ['ZS']
CARGO = os.environ.get('CARGO', 'cargo').split()
env = dict(os.environ, CARGO_TARGET_DIR=os.environ.get('CHECK_TARGET', ZS + '/check-target'))
r = subprocess.run(CARGO + ['check', '--release', '--message-format=json', '--manifest-path', W + '/Cargo.toml'],
                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
open(ZS + '/warnings-check.json', 'w').write(r.stdout); open(ZS + '/warnings-check.err', 'w').write(r.stderr)
assert r.returncode == 0, 'the derived tree does not check: ' + ZS + '/warnings-check.err'
by = collections.Counter(); roots = {}; rows = []
for line in r.stdout.splitlines():
    try: m = json.loads(line)
    except ValueError: continue
    if m.get('reason') != 'compiler-message' or m['message'].get('level') != 'warning': continue
    if not m['manifest_path'].startswith(W + '/'): continue
    d = m['message']; code = (d.get('code') or {}).get('code') or d['message'][:40]
    prim = next((s for s in d.get('spans', []) if s.get('is_primary')), None)
    if prim is None: continue
    by[(m['target']['name'], code)] += 1; roots[m['target']['name']] = m['target']['src_path']
    rows.append(f"{prim['file_name']}\t{prim['line_start']}\t{code}\t{d['message']}")
open(ZS + '/hits/warnings.tsv', 'w').write(''.join(x + '\n' for x in rows))
crates = collections.Counter()
for (c, _), n in by.items(): crates[c] += n
print(f'   compiler warnings, the sources as they stand: {sum(by.values())}'
      + ''.join(f'; {c} {n} (' + ', '.join(f'{l} {k}' for (cc, l), k in by.most_common() if cc == c) + ')'
                for c, n in crates.most_common()))
for c in sorted(crates):
    p = roots[c]; lines = open(p).read().split('\n'); last = -1
    for i, l in enumerate(lines):
        t = l.strip()
        if t.startswith('#!['): last = i
        elif t == '' or t.startswith('//'): continue
        else: break
    lines.insert(last + 1, '#![allow(warnings)]'); open(p, 'w').write('\n'.join(lines))
    print(f'   #![allow(warnings)] -> {os.path.relpath(p, W)} ({crates[c]} warnings)')
print(f'#WARNINGS {sum(by.values())}')
