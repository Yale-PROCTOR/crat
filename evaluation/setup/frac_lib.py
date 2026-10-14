#!/usr/bin/env python3
"""per .rs file: physical lines, and lines that lie inside a static/const initializer (from `static|const NAME: T =` to its ';' at depth 0)."""
import os, re, sys
HEAD = re.compile(r'^\s*(pub(\([^)]*\))?\s+)?(static\s+(mut\s+)?|const\s+)[A-Za-z_][A-Za-z0-9_]*\s*:', re.M)
def data_lines(text):
    covered = set(); n = 0
    for m in HEAD.finditer(text):
        i = text.find('=', m.end()); 
        if i < 0: continue
        depth = 0; j = i
        while j < len(text):
            c = text[j]
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            elif c == ';' and depth == 0: break
            j += 1
        a = text.count('\n', 0, m.start()); b = text.count('\n', 0, j)
        covered.update(range(a, b + 1))
    return len(covered)
