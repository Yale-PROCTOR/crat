#!/usr/bin/env python3
"""Strip comments from TOML (state machine) and Python (tokenize) files, verifying the result."""
import ast, io, sys, tokenize, tomllib

def strip_toml(src):
    out = []; i = 0; n = len(src); touched = set(); line = 0; removed = 0
    state = None  # None | 'basic' | 'literal' | 'mlbasic' | 'mlliteral'
    while i < n:
        c = src[i]
        if state is None:
            if c == '#':
                j = src.find('\n', i)
                if j == -1: j = n
                touched.add(line); removed += 1; i = j; continue
            if src.startswith('"""', i): state = 'mlbasic'; out.append('"""'); i += 3; continue
            if src.startswith("'''", i): state = 'mlliteral'; out.append("'''"); i += 3; continue
            if c == '"': state = 'basic'
            elif c == "'": state = 'literal'
        elif state == 'basic':
            if c == '\\': out.append(src[i:i+2]); i += 2; continue
            if c == '"': state = None
        elif state == 'literal':
            if c == "'": state = None
        elif state == 'mlbasic':
            if c == '\\': out.append(src[i:i+2]); i += 2; continue
            if src.startswith('"""', i): state = None; out.append('"""'); i += 3; continue
        elif state == 'mlliteral':
            if src.startswith("'''", i): state = None; out.append("'''"); i += 3; continue
        if c == '\n': line += 1
        out.append(c); i += 1
    text = ''.join(out)
    res = []
    for k, l in enumerate(text.split('\n')):
        if k in touched:
            l = l.rstrip()
            if l == '': 
                continue
        res.append(l)
    result = '\n'.join(res)
    assert tomllib.loads(result) == tomllib.loads(src), "TOML value changed"
    return result, removed

def strip_py(src):
    lines = src.split('\n')
    cuts = {}  # line index -> list of (startcol, endcol)
    removed = 0
    for tok in tokenize.generate_tokens(io.StringIO(src).readline):
        if tok.type == tokenize.COMMENT:
            (r, c0), (_, c1) = tok.start, tok.end
            if r == 1 and tok.string.startswith('#!'):
                continue
            cuts.setdefault(r - 1, []).append((c0, c1)); removed += 1
    res = []
    for k, l in enumerate(lines):
        if k in cuts:
            for c0, c1 in sorted(cuts[k], reverse=True):
                l = l[:c0] + l[c1:]
            l = l.rstrip()
            if l == '':
                continue
        res.append(l)
    result = '\n'.join(res)
    assert ast.dump(ast.parse(result)) == ast.dump(ast.parse(src)), "Python AST changed"
    return result, removed

mode, paths = sys.argv[1], sys.argv[2:]
for p in paths:
    src = open(p, encoding='utf-8').read()
    out, removed = (strip_toml if mode == 'toml' else strip_py)(src)
    again, r2 = (strip_toml if mode == 'toml' else strip_py)(out)
    assert r2 == 0 and again == out, p
    open(p, 'w', encoding='utf-8').write(out)
    print(f"{p}\t{removed}\t{len(src)}\t{len(out)}")
