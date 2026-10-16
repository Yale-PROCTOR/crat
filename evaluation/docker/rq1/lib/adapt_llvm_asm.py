#!/usr/bin/env python3
"""Adapts a Laertes tree's `llvm_asm!` sites to the counter's toolchain (nightly-2025-06-23), mechanically:
llvm_asm!(TPL : outs : ins : clobbers : opts) -> ::core::arch::asm!(TPL', operands, options(att_syntax)),
"=r"(x) -> out(reg) x, "+r"(x) -> inout(reg) x, "r"(x) -> in(reg) x; in the template $N -> {N}, $$ -> $, {/} doubled;
"volatile" is asm!'s default. Every operand place stays an operand (a use) -- nothing is dropped. Fails on any other
constraint, clobber or option. `#![feature(llvm_asm)]` in the crate root is removed (the feature no longer exists).
Usage: adapt_llvm_asm.py SRC_TREE DST_TREE  (writes DST, a copy, plus sites.tsv)"""
import os, re, shutil, sys
src, dst = sys.argv[1], sys.argv[2]
if os.path.exists(dst): shutil.rmtree(dst)
shutil.copytree(src, dst)

def close(s, i):
    d = 0; j = i; inq = False
    while j < len(s):
        c = s[j]
        if inq:
            if c == '\\': j += 2; continue
            if c == '"': inq = False
        elif c == '"': inq = True
        elif c == '(': d += 1
        elif c == ')':
            d -= 1
            if d == 0: return j
        j += 1
    raise SystemExit('unbalanced')

def split_colons(body):
    parts, cur, d, inq, i = [], '', 0, False, 0
    while i < len(body):
        ch = body[i]
        if inq:
            cur += ch
            if ch == '\\': cur += body[i + 1]; i += 2; continue
            if ch == '"': inq = False
        elif ch == '"': inq = True; cur += ch
        elif ch in '([': d += 1; cur += ch
        elif ch in ')]': d -= 1; cur += ch
        elif ch == ':' and d == 0 and body[i + 1:i + 2] != ':' and body[i - 1:i] != ':':
            parts.append(cur); cur = ''
        else: cur += ch
        i += 1
    parts.append(cur)
    return parts

def tpl(t):
    t = t.replace('{', '{{').replace('}', '}}')
    t = re.sub(r'\$\$', '\x00', t)
    t = re.sub(r'\$(\d+)', r'{\1}', t)
    return t.replace('\x00', '$')

rows = []
for root, _, files in os.walk(dst):
    for fn in files:
        if not fn.endswith('.rs'): continue
        p = os.path.join(root, fn); s = open(p).read(); out = []; last = 0; k = 0
        s2 = re.sub(r'#!\[feature\(llvm_asm\)\]\n?', '', s)
        if s2 != s: rows.append((os.path.relpath(p, dst), 0, 'removed #![feature(llvm_asm)]', '-', '-')); s = s2
        for m in re.finditer(r'llvm_asm!\(', s):
            o = m.end() - 1; c = close(s, o)
            parts = split_colons(s[o + 1:c])
            assert len(parts) == 5 and parts[3].strip() == '' and parts[4].strip() == '"volatile"', parts[3:]
            ops = []
            for kind, lst in (('out', parts[1]), ('in', parts[2])):
                for cm in re.finditer(r'"([^"]*)"\s*\(([^)]*)\)', lst):
                    cons, place = cm.group(1), cm.group(2).strip()
                    spec = {'=r': 'out(reg)', '+r': 'inout(reg)', 'r': 'in(reg)'}[cons]
                    ops.append(f'{spec} {place}')
            t = parts[0].strip()
            new = f'::core::arch::asm!({tpl(t)}, {", ".join(ops)}, options(att_syntax))'
            line = s.count('\n', 0, m.start()) + 1
            rows.append((os.path.relpath(p, dst), line, 'llvm_asm! -> asm!', len(ops), ' '.join(o.split()[-1] for o in ops)))
            out.append(s[last:m.start()]); out.append(new); last = c + 1; k += 1
        out.append(s[last:])
        if k or s2 != open(p).read(): open(p, 'w').write(''.join(out))
with open(os.path.join(os.path.dirname(dst.rstrip('/')), 'sites.tsv'), 'w') as f:
    f.write('file\tline\tchange\toperands\tplaces\n')
    for r in rows: f.write('\t'.join(map(str, r)) + '\n')
print('sites', sum(1 for r in rows if r[2].startswith('llvm')), 'operands', sum(r[3] for r in rows if r[2].startswith('llvm')))
