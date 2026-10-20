#!/usr/bin/env python3
"""A small Rust lexer.

`tokens(text)` yields (kind, value, offset) with comments removed and string,
byte-string, raw-string and char literals folded into one `lit` token each, so
braces and identifiers inside literals never count. Lifetimes (`'a`) are kept
as `lifetime` tokens, not char literals.

`functions(toks)` returns (name, body_start, body_end) for every `fn` item that
has a body, in text order; nested functions are included, and `owner_of`
attributes a position to the innermost function containing it.
"""
import re

_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_NUM = re.compile(r"[0-9][0-9A-Za-z_.]*")
_PUNCT3 = ("..=", "...", "<<=", ">>=")
_PUNCT2 = ("::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=",
           "/=", "%=", "^=", "&=", "|=", "<<", ">>", "..")


def _skip_block_comment(text, i):
    depth, n = 1, len(text)
    i += 2
    while i < n and depth:
        if text.startswith("/*", i):
            depth += 1
            i += 2
        elif text.startswith("*/", i):
            depth -= 1
            i += 2
        else:
            i += 1
    return i


def _string_end(text, i):
    """i points at the opening quote of a normal string; return index past it."""
    i += 1
    n = len(text)
    while i < n:
        c = text[i]
        if c == "\\":
            i += 2
        elif c == '"':
            return i + 1
        else:
            i += 1
    return n


def _raw_string_end(text, i):
    """i points at `r`; returns index past `r#*"...\"#*`."""
    j = i + 1
    hashes = 0
    while j < len(text) and text[j] == "#":
        hashes += 1
        j += 1
    close = '"' + "#" * hashes
    end = text.find(close, j + 1)
    return len(text) if end < 0 else end + len(close)


def tokens(text):
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/*", i):
            i = _skip_block_comment(text, i)
            continue
        # raw strings r"..", r#".."#, br"..", br#".."#
        m = re.match(r"b?r#*\"", text[i:i + 12])
        if m:
            start = i + (1 if text[i] == "b" else 0)
            end = _raw_string_end(text, start)
            yield ("lit", "str", i)
            i = end
            continue
        if c == '"' or (c == "b" and i + 1 < n and text[i + 1] == '"'):
            q = i if c == '"' else i + 1
            end = _string_end(text, q)
            yield ("lit", "str", i)
            i = end
            continue
        if c == "'" or (c == "b" and i + 1 < n and text[i + 1] == "'"):
            q = i if c == "'" else i + 1
            # char literal: 'x', '\n', '\u{..}', '\''; else a lifetime 'a
            m = re.match(r"'(?:\\u\{[0-9A-Fa-f]+\}|\\x[0-9A-Fa-f]{2}|\\.|[^\\'])'", text[q:q + 14])
            if m:
                yield ("lit", "char", i)
                i = q + m.end()
                continue
            m = _IDENT.match(text, q + 1)
            if m and c == "'":
                yield ("lifetime", m.group(0), i)
                i = m.end()
                continue
        m = _IDENT.match(text, i)
        if m:
            yield ("ident", m.group(0), i)
            i = m.end()
            continue
        m = _NUM.match(text, i)
        if m:
            yield ("num", m.group(0), i)
            i = m.end()
            continue
        for p in _PUNCT3:
            if text.startswith(p, i):
                yield ("punct", p, i)
                i += 3
                break
        else:
            for p in _PUNCT2:
                if text.startswith(p, i):
                    yield ("punct", p, i)
                    i += 2
                    break
            else:
                yield ("punct", c, i)
                i += 1


def functions(toks):
    """(name, body_start_index, body_end_index) over the token list."""
    out = []
    n = len(toks)
    for k in range(n - 1):
        if toks[k][:2] == ("ident", "fn") and toks[k + 1][0] == "ident":
            name = toks[k + 1][1]
            # find the body's `{` at paren depth 0, or a `;` (no body)
            j, paren, angle = k + 2, 0, 0
            while j < n:
                v = toks[j][1] if toks[j][0] == "punct" else None
                if v == "(":
                    paren += 1
                elif v == ")":
                    paren -= 1
                elif v == ";" and paren == 0:
                    j = -1
                    break
                elif v == "{" and paren == 0:
                    break
                j += 1
            if j < 0 or j >= n:
                continue
            depth, e = 0, j
            while e < n:
                v = toks[e][1] if toks[e][0] == "punct" else None
                if v == "{":
                    depth += 1
                elif v == "}":
                    depth -= 1
                    if depth == 0:
                        break
                e += 1
            out.append((name, j, e))
    return out


def owner_of(funcs, index):
    """Innermost function whose body contains token index."""
    best = None
    for name, s, e in funcs:
        if s <= index <= e and (best is None or s >= best[1]):
            best = (name, s, e)
    return best


def calls(toks, names):
    """Token indices where an identifier in `names` is called: `name (`, not a
    declaration (`fn name`), not a method (`.name(`) and not a path segment
    followed by `::`."""
    out = []
    for k in range(len(toks) - 1):
        kind, value, _ = toks[k]
        if kind != "ident" or value not in names:
            continue
        if toks[k + 1][:2] != ("punct", "("):
            continue
        if k > 0 and toks[k - 1][:2] in (("ident", "fn"), ("punct", ".")):
            continue
        out.append(k)
    return out
