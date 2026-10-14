"""Module-aware function-body extraction (for the removed / no-longer-a-pointer split only; the counts come from
the typed counter). Skips strings, byte strings, raw strings, char literals and comments while matching braces."""
import os, re

IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')


def _skip(s, i):
    """If s[i:] starts a comment / string / char literal, return the index after it, else None."""
    c = s[i]
    if s.startswith('//', i):
        j = s.find('\n', i)
        return len(s) if j < 0 else j
    if s.startswith('/*', i):
        depth, j = 1, i + 2
        while j < len(s) and depth:
            if s.startswith('/*', j):
                depth, j = depth + 1, j + 2
            elif s.startswith('*/', j):
                depth, j = depth - 1, j + 2
            else:
                j += 1
        return j
    m = re.match(r'b?r(#*)"', s[i:i + 40])
    if m and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] == '_')):
        close = '"' + m.group(1)
        j = s.find(close, i + m.end())
        return len(s) if j < 0 else j + len(close)
    if c == '"' or (c == 'b' and s.startswith('b"', i) and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] == '_'))):
        j = i + (2 if c == 'b' else 1)
        while j < len(s):
            if s[j] == '\\':
                j += 2
            elif s[j] == '"':
                return j + 1
            else:
                j += 1
        return j
    if c == "'" or (c == 'b' and s.startswith("b'", i)):
        j = i + (2 if c == 'b' else 1)
        m = re.match(r"(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'", s[j:j + 14])
        if m:
            return j + m.end()
        return None  # a lifetime
    return None


def functions(text, base=()):
    """{(module path tuple, fn name): [body text, ...]} for every fn item, nested inline modules tracked."""
    out = {}
    stack = []  # (kind, name, depth at open)
    depth, i, n = 0, 0, len(text)
    pending = None  # ('mod', name) or ('fn', name, start)
    while i < n:
        j = _skip(text, i)
        if j is not None:
            i = j
            continue
        c = text[i]
        if c.isalpha() or c == '_':
            m = IDENT.match(text, i)
            w = m.group(0)
            if w in ('mod', 'fn') and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')):
                m2 = re.compile(r'\s+(r#)?([A-Za-z_][A-Za-z0-9_]*)').match(text, m.end())
                if m2:
                    pending = (w, m2.group(2), i)
                    i = m2.end()
                    continue
            i = m.end()
            continue
        if c == ';' and pending and depth_ok(pending):
            pending = None
        elif c == '{':
            if pending:
                stack.append((pending[0], pending[1], depth, i))
                pending = None
            depth += 1
        elif c == '}':
            depth -= 1
            if stack and stack[-1][2] == depth:
                kind, name, _, start = stack.pop()
                if kind == 'fn':
                    mods = tuple(base) + tuple(nm for k, nm, _, _ in stack if k == 'mod')
                    out.setdefault((mods, name), []).append(text[start:i + 1])
        i += 1
    return out


def depth_ok(p):
    return True


def tree_functions(root_dir):
    """Every .rs file under root_dir (no target/), its module path from the file path (lib.rs / main.rs /
    c2rust-lib.rs / mod.rs at their directory)."""
    out = {}
    for dp, dns, fs in os.walk(root_dir):
        dns[:] = [d for d in dns if d not in ('target', 'analysis_results')]
        for f in fs:
            if not f.endswith('.rs') or f == 'build.rs':
                continue
            rel = os.path.relpath(os.path.join(dp, f), root_dir)[:-3].split(os.sep)
            if rel[-1] in ('lib', 'main', 'c2rust-lib', 'mod'):
                rel = rel[:-1]
            rel = tuple(x.replace('-', '_') for x in rel)
            for k, v in functions(open(os.path.join(dp, f), errors='replace').read(), rel).items():
                out.setdefault(k, []).extend(v)
    return out


def find(fns, owner, flat=False):
    """The bodies of owner (a def path), matched by fn name and the longest module-path suffix agreement."""
    parts = owner.split('::')
    name, mods = parts[-1], parts[:-1]
    cands = [(m, b) for (m, nm), bs in fns.items() if nm == name for b in bs]
    if not cands:
        return []

    def score(m):
        a, b = list(m), list(mods)
        s = 0
        while a and b and a[-1] == b[-1]:
            s, a, b = s + 1, a[:-1], b[:-1]
        return s
    best = max(score(m) for m, _ in cands)
    return [b for m, b in cands if score(m) == best]


def has_binding(bodies, var):
    pat = re.compile(r'(\blet\s+(?:ref\s+)?(?:mut\s+)?' + re.escape(var) + r'\b)|([(,]\s*(?:mut\s+)?' + re.escape(var) + r'\s*:)')
    return any(pat.search(b) for b in bodies)
