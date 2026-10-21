"""The `mod name;` declarations of a Rust source with the inline modules (`mod a { ... }`) that enclose each, so that a
file module declared inside an inline one resolves under that module's directory, as the compiler resolves it."""
import re
TOKEN = re.compile(r'//[^\n]*|/\*|r(#*)"|b?"(?:\\.|[^"\\])*"|\'(?:\\u\{[0-9a-fA-F]+\}|\\.|[^\\\'\n])\'|'
                   r'(?<![\w])(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z_]\w*)\s*([;{])|[{}]', re.S)

def decls(src):
    """[(name, [enclosing inline module names], offset)] for every `mod name;`."""
    out, stack, depth, i = [], [], 0, 0
    while True:
        m = TOKEN.search(src, i)
        if not m: return out
        t = m.group(0); i = m.end()
        if t == '/*':
            level = 1
            while level and i < len(src):
                if src.startswith('/*', i): level += 1; i += 2
                elif src.startswith('*/', i): level -= 1; i += 2
                else: i += 1
        elif m.group(1) is not None:
            end = src.find('"' + m.group(1), i); i = len(src) if end < 0 else end + 1 + len(m.group(1))
        elif m.group(2):
            if m.group(3) == ';': out.append((m.group(2), [s for s, _ in stack], m.start()))
            else: depth += 1; stack.append((m.group(2), depth))
        elif t == '{': depth += 1
        elif t == '}':
            if stack and stack[-1][1] == depth: stack.pop()
            depth -= 1
