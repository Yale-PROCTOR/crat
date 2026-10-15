#!/usr/bin/env python3
import os, re, sys
W = os.environ['W'].rstrip('/')
roots = []
for c in sorted(os.listdir(f'{W}/crates')):
    for r in ('lib.rs', 'main.rs'):
        p = f'{W}/crates/{c}/src/{r}'
        if os.path.exists(p): roots.append(p)
roots += sorted(f'{W}/src/bin/{f}' for f in os.listdir(f'{W}/src/bin'))
roots += [r for r in (f'{W}/deps_crate/src/main.rs', f'{W}/examples/fnptr/lib.rs') if os.path.exists(r)]
mod_re = re.compile(r'^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z_]\w*)\s*;', re.M)
path_re = re.compile(r'#\[path\s*=\s*"([^"]+)"\]')
reach = set(); unresolved = []
def visit(p):
    if p in reach: return
    reach.add(p)
    src = open(p, encoding='utf-8').read()
    d = os.path.dirname(p); stem = os.path.splitext(os.path.basename(p))[0]
    is_root = os.path.basename(p) in ('lib.rs', 'main.rs', 'mod.rs') or '/src/bin/' in p or p.endswith('/examples/fnptr/lib.rs')
    for m in mod_re.finditer(src):
        name = m.group(1)
        before = src[max(0, m.start()-300):m.start()]
        pm = path_re.findall(before.split('\n')[-4:][0] + '\n' + '\n'.join(before.split('\n')[-4:]))
        cands = []
        if pm:
            cands.append(os.path.normpath(os.path.join(d if is_root else os.path.join(d, stem), pm[-1])))
            cands.append(os.path.normpath(os.path.join(d, pm[-1])))
        base = d if is_root else os.path.join(d, stem)
        cands += [f'{base}/{name}.rs', f'{base}/{name}/mod.rs']
        hit = next((c for c in cands if os.path.exists(c)), None)
        if hit: visit(hit)
        else: unresolved.append((p.replace(W+'/', ''), name, m.start()))
for r in roots:
    if os.path.exists(r): visit(r)
kept = set(l.strip() for l in open(os.environ['KEPT']))
kept = set(l for l in kept if os.path.exists(l))
orphans = sorted(kept - reach)
print(f'roots={len(roots)} reachable={len(reach)} kept={len(kept)} orphans={len(orphans)} unresolved={len(unresolved)}')
for u in unresolved: print('UNRESOLVED', *u)
open(os.environ['ORPHANS'],'w').write('\n'.join(o.replace(W+'/', '') for o in orphans) + '\n')
