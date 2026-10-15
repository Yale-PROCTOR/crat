#!/usr/bin/env python3
"""crat -> jobcrat rename, rules R1-R6 (relays 002 and 003), over every text file of the worktree W. mode: map | apply | untouched"""
import os, re, sys, collections
W = os.environ['W'].rstrip('/')
mode = sys.argv[1]
TEXT_EXT = {'.rs', '.toml', '.sh', '.py', '.tsv', '.csv', '.json', '.md', '.c', '.h', '.txt', '.snap', '.hex', ''}
SKIP = {'Cargo.lock', '.git'}
def files():
    for root, dirs, fs in os.walk(W):
        dirs[:] = [d for d in dirs if d not in ('.git', 'target')]
        for f in fs:
            p = os.path.join(root, f)
            if os.path.islink(p): continue
            if f in SKIP: continue
            ext = os.path.splitext(f)[1]
            if ext in TEXT_EXT or f in ('Makefile',):
                yield p
RULES = [
    ('R1 CRAT_ -> JOBCRAT_', re.compile(r'\bCRAT_'), 'JOBCRAT_'),
    ('R2 whole word crat -> jobcrat', re.compile(r'\bcrat\b'), 'jobcrat'),
    ('R3 prefix crat_ -> jobcrat_', re.compile(r'\bcrat_'), 'jobcrat_'),
    ('R4 suffix _crat -> _jobcrat', re.compile(r'_crat\b'), '_jobcrat'),
    ('R5 whole word Crat -> Jobcrat', re.compile(r'\bCrat\b'), 'Jobcrat'),
    ('R6a __crat_ -> __jobcrat_', re.compile(r'__crat_'), '__jobcrat_'),
    ('R6b __CRAT_ -> __JOBCRAT_', re.compile(r'__CRAT_'), '__JOBCRAT_'),
]
counts = collections.Counter(); per_file = collections.Counter()
rows = []
for p in sorted(files()):
    try: src = open(p, encoding='utf-8').read()
    except UnicodeDecodeError: continue
    rel = p[len(W)+1:]
    new = src
    for name, rx, rep in RULES:
        if mode != 'untouched':
            for m in rx.finditer(new):
                line = new.count('\n', 0, m.start()) + 1
                rows.append((rel, line, name, m.group(0)))
                counts[name] += 1; per_file[rel] += 1
        new = rx.sub(rep, new)
    if mode == 'apply' and new != src:
        open(p, 'w', encoding='utf-8').write(new)
    if mode == 'untouched':
        for m in re.finditer(r'[A-Za-z0-9_]*[cC][rR][aA][tT][A-Za-z0-9_]*', new):
            w = m.group(0)
            if 'crat' not in re.sub('(?i)jobcrat', '', w).lower(): continue
            rows.append((rel, new.count('\n', 0, m.start()) + 1, 'UNTOUCHED', w))
if mode in ('map', 'apply'):
    for r in rows: print('\t'.join(map(str, r)))
    print('#COUNTS', dict(counts), file=sys.stderr)
    print('#FILES', len(per_file), file=sys.stderr)
    # file names carrying the word
    for p in sorted(files()):
        rel = p[len(W)+1:]
        b = os.path.basename(rel)
        if re.search(r'\bcrat\b|\bcrat_|_crat\b|\bCrat\b|\bCRAT_', b):
            print('#FILENAME', rel, file=sys.stderr)
else:
    agg = collections.Counter(r[3] for r in rows)
    for w, n in agg.most_common(): print(f'{n}\t{w}')
    print('#ROWS', len(rows), file=sys.stderr)
    for r in rows:
        if agg[r[3]] <= 30: print('\t'.join(map(str, r)), file=sys.stderr)
