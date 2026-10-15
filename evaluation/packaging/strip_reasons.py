#!/usr/bin/env python3
import os
"""Delete the `reason = "..."` argument of #[allow]/#[expect] attributes (relay 003 item 4b). Prints file, line, the deleted text."""
import re, sys
W = os.environ['W'].rstrip('/')
files = [l.strip() for l in open(sys.argv[1])]
n = 0
for rel in files:
    p = f'{W}/{rel}'; s = open(p, encoding='utf-8').read(); orig = s
    pos = 0
    while True:
        m = re.search(r'#!?\[(allow|expect)\(', s[pos:])
        if not m: break
        start = pos + m.start(); open_paren = pos + m.end() - 1
        # find the matching ')' of the attribute, skipping string literals
        i = open_paren + 1; depth = 1
        while depth:
            c = s[i]
            if c == '"':
                i += 1
                while s[i] != '"':
                    i += 2 if s[i] == '\\' else 1
            elif c == '(': depth += 1
            elif c == ')': depth -= 1
            i += 1
        close_paren = i - 1
        body = s[open_paren + 1:close_paren]
        rm = re.search(r'\s*,\s*reason\s*=\s*"', body)
        if rm:
            j = rm.end()
            while body[j] != '"':
                j += 2 if body[j] == '\\' else 1
            j += 1
            deleted = body[rm.start():j]
            new_body = body[:rm.start()] + body[j:]
            if '\n' not in new_body.strip():
                new_body = new_body.strip()
            s = s[:open_paren + 1] + new_body + s[close_paren:]
            line = s.count('\n', 0, start) + 1
            print(f'{rel}:{line}\t{deleted.strip()[:160]!r}')
            n += 1
            pos = open_paren + 1 + len(new_body) + 1
        else:
            pos = close_paren + 1
    if s != orig:
        open(p, 'w', encoding='utf-8').write(s)
print(f'#DELETED {n}', file=sys.stderr)
