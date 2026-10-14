#!/usr/bin/env python3
"""Light scanner of a c2rust-derived single-file crate: every `struct`/`union`
definition with its crate-relative def path (the module nesting, as
tcx.def_path_str spells it: `src::avl::Node`) and its fields in declaration
order (= AdtDef::all_fields order, the `field{index}` of slot_key.rs).
Skips comments, string/char literals; tracks braces."""
import re

HEAD_RE = re.compile(r'(?:^|[\s;}{])(?:pub(?:\([^)]*\))?\s+)?(mod|struct|union)\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^{;]*>)?\s*(?:where[^{;]*)?$', re.S)
CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'])'", re.S)


def _blank(text):
    """Return text with comments and string/char literal CONTENTS replaced by spaces (offsets kept)."""
    out = list(text)
    i, n = 0, len(text)
    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '
    while i < n:
        c = text[i]
        if c == '/' and text.startswith('//', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            blank(i, j); i = j
        elif c == '/' and text.startswith('/*', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/*', j): depth += 1; j += 2
                elif text.startswith('*/', j): depth -= 1; j += 2
                else: j += 1
            blank(i, j); i = j
        elif c == 'r' and re.match(r'r#*"', text[i:i + 10]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')) or \
                (c == 'b' and re.match(r'br#*"', text[i:i + 10]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_'))):
            m = re.match(r'b?r(#*)"', text[i:i + 12])
            end = '"' + m.group(1)
            j = text.find(end, i + len(m.group(0)))
            j = n if j < 0 else j + len(end)
            blank(i + 1, j - 1); i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            blank(i + 1, j); i = j + 1
        elif c == "'":
            m = CHAR_RE.match(text, i)
            if m:
                blank(i + 1, m.end() - 1); i = m.end()
            else:
                i += 1  # lifetime
        else:
            i += 1
    return ''.join(out)


def _split_fields(body):
    fields, cur, depth, i = [], [], 0, 0
    while i < len(body):
        c = body[i]
        if c == '-' and body.startswith('->', i):
            cur.append('->'); i += 2; continue
        if c in '([<{': depth += 1
        elif c in ')]>}': depth -= 1
        if c == ',' and depth == 0:
            fields.append(''.join(cur)); cur = []
        else:
            cur.append(c)
        i += 1
    if ''.join(cur).strip():
        fields.append(''.join(cur))
    res = []
    for f in fields:
        f = re.sub(r'#\s*\[[^\]]*\]', ' ', f).strip()
        if not f:
            continue
        m = re.match(r'(?:pub(?:\([^)]*\))?\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$', f, re.S)
        if not m:
            raise ValueError(f'unparsed field: {f[:120]!r}')
        res.append((m.group(1), ' '.join(m.group(2).split())))
    return res


def scan(path):
    raw = open(path, encoding='utf-8').read()
    text = _blank(raw)
    stack = []  # (kind, name)
    out = []    # (def_path, kind, [(field, type)])
    last_stmt = 0
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '{':
            head = text[last_stmt:i]
            m = HEAD_RE.search(head)
            kind, name = (m.group(1), m.group(2)) if m else ('anon', None)
            if kind in ('struct', 'union'):
                depth, j = 1, i + 1
                while depth:
                    if text[j] == '{': depth += 1
                    elif text[j] == '}': depth -= 1
                    j += 1
                path = '::'.join([s for k, s in stack if k in ('mod', 'anonfn')] + [name])
                in_anon = any(k == 'anon' for k, _ in stack)
                out.append((path, kind, _split_fields(raw[i + 1:j - 1] if False else text[i + 1:j - 1]), in_anon))
                i = j; last_stmt = j; continue
            stack.append((kind, name))
            i += 1; last_stmt = i; continue
        if c == '}':
            if stack: stack.pop()
            i += 1; last_stmt = i; continue
        if c == ';':
            last_stmt = i + 1
        i += 1
    return out


if __name__ == '__main__':
    import sys
    for path, kind, fields, anon in scan(sys.argv[1]):
        print(path, kind, anon, [f for f, _ in fields])
