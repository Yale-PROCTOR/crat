"""SLOC of the twenty inputs (`setup.<p>.sloc`, `setup.sloc`): non-blank lines that are not wholly comment, over the
program's .rs files except build.rs, in the C2Rust output as distributed (benchmarks/crown/<p>). A data table is left
out: a file at least 99.9 % of whose physical lines lie inside static or const initializers."""
import glob, os, re

import common as C

HEAD = re.compile(r'^\s*(pub(\([^)]*\))?\s+)?(static\s+(mut\s+)?|const\s+)[A-Za-z_][A-Za-z0-9_]*\s*:', re.M)


def sloc_of_text(text):
    n, block = 0, 0
    for line in text.splitlines():
        s, code, i = line, False, 0
        while i < len(s):
            if block:
                j, k = s.find('*/', i), s.find('/*', i)
                if k != -1 and (j == -1 or k < j):
                    block, i = block + 1, k + 2
                elif j != -1:
                    block, i = block - 1, j + 2
                else:
                    break
            elif s.startswith('//', i):
                break
            elif s.startswith('/*', i):
                block, i = 1, i + 2
            elif s[i].isspace():
                i += 1
            else:
                code = True
                # skip a string literal whole, so `"//"` is not read as a comment
                if s[i] == '"':
                    j = i + 1
                    while j < len(s) and s[j] != '"':
                        j += 2 if s[j] == '\\' else 1
                    i = j + 1
                else:
                    i += 1
        n += code
    return n


def data_lines(text):
    """Physical lines inside a static / const initializer (from `static|const NAME: T =` to its ';' at depth 0)."""
    covered = set()
    for m in HEAD.finditer(text):
        i = text.find('=', m.end())
        if i < 0:
            continue
        depth, j = 0, i
        while j < len(text):
            c = text[j]
            if c in '([{':
                depth += 1
            elif c in ')]}':
                depth -= 1
            elif c == ';' and depth == 0:
                break
            j += 1
        covered.update(range(text.count('\n', 0, m.start()), text.count('\n', 0, j) + 1))
    return len(covered)


def sloc():
    """{key: value} for setup.<p>.sloc and setup.sloc; per-program rows (sloc, files, excluded data tables)."""
    v, rows = {}, {}
    for p in C.PROGS:
        files = sorted(f for f in glob.glob(os.path.join(C.INPUT, p, '**', '*.rs'), recursive=True)
                       if os.path.basename(f) != 'build.rs')
        n, excluded = 0, []
        for f in files:
            t = open(f, errors='replace').read()
            lines = t.count('\n')
            if lines and data_lines(t) / lines >= 0.999:
                excluded.append(os.path.relpath(f, os.path.join(C.INPUT, p)))
                continue
            n += sloc_of_text(t)
        v[f'setup.{C.K(p)}.sloc'] = str(n)
        rows[p] = dict(sloc=n, files=len(files), data_tables=' '.join(excluded))
    v['setup.sloc'] = str(sum(r['sloc'] for r in rows.values()))
    return v, rows
