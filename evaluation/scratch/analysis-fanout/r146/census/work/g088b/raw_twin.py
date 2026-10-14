#!/usr/bin/env python3
"""r110/p5: codegen.raw-twin (079 S13's count): in each census's emitted-trees/<p>/**/*.rs, twin
functions = `fn __crat_raw_<name>` definitions; twin calls = occurrences of `__crat_raw_<name>(` that are
not the definition (comments // excluded)."""
import re, os, sys, collections
DEF = re.compile(r'\bfn\s+(__crat_raw_\w+)')
USE = re.compile(r'\b(__crat_raw_\w+)\s*(?:::<[^>]*>)?\s*\(')
def count(root):
    res = collections.OrderedDict()
    for p in sorted(os.listdir(root)):
        d = c = 0; names = []
        for dp, _, fs in os.walk(os.path.join(root, p)):
            for f in fs:
                if not f.endswith('.rs'): continue
                for line in open(os.path.join(dp, f), encoding='utf-8', errors='replace'):
                    code = line.split('//', 1)[0]
                    defs = DEF.findall(code); d += len(defs); names += defs
                    c += len(USE.findall(code)) - len(defs)
        if d or c: res[p] = (d, c, sorted(names))
    return res
for fr in sys.argv[1:]:
    r = count(f'scratch/main/{fr}/emitted-trees')
    print(fr, 'functions', sum(v[0] for v in r.values()), 'calls', sum(v[1] for v in r.values()))
    for p, v in r.items(): print('  ', p, v[0], v[1], ' '.join(v[2]))
