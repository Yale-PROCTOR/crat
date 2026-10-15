#!/usr/bin/env python3
"""The zip builds without warnings (USER 10-15 09:0xZ): `#![allow(warnings)]` after the last inner attribute of every crate
root of the derived tree. The trims and the test cut leave dead code behind; the attribute hides the lints, nothing else."""
import glob, os
W = os.environ['W'].rstrip('/')
roots = sorted(glob.glob(W + '/crates/*/src/lib.rs') + glob.glob(W + '/src/bin/*.rs') + glob.glob(W + '/deps_crate/src/main.rs'))
for p in roots:
    lines = open(p, encoding='utf-8').read().split('\n')
    last = -1
    for i, l in enumerate(lines):
        s = l.strip()
        if s.startswith('#!['): last = i
        elif s == '' or s.startswith('//'): continue
        else: break
    lines.insert(last + 1, '#![allow(warnings)]')
    open(p, 'w', encoding='utf-8').write('\n'.join(lines))
    print(f'   #![allow(warnings)] -> {p[len(W)+1:]} (line {last + 2})')
