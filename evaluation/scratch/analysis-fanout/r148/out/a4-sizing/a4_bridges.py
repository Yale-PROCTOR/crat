#!/usr/bin/env python3
"""a4_bridges.py -- analysis-fanout relay 148, task A4 (sizing only; nothing is built).

Counts, in the twenty emitted trees of the landed 60s' census (main/batch60sp/emitted-trees/<p>/), the BRIDGE sites:
a reference taken through a raw pointer, `&*E` / `&mut *E` (also `&*(E)`), whose raw operand E is syntactically one of
    L.as_mut_ptr()  L.as_ptr()  &mut L as *mut T  &L as *const T  &raw mut L  &raw const L
    [::](core|std)::ptr::addr_of_mut!(L) / addr_of!(L)  (also ptr::addr_of*! / bare addr_of*!)
for L a LOCAL of the enclosing function (a `let` binding of that function that textually precedes the site; not a
parameter, not a static, not a field/index path).

Source-level only: comments and string/char literals are blanked (offsets and line numbers preserved), functions are
delimited by brace matching, the operand is parsed as the postfix expression following the `*`.

Every `&*`/`&mut *` site is classified; the primary count is
    form in the list above  AND  root = bare local  AND  context in {call-arg, let-bound, assigned}
Secondary columns (reported, NOT in the primary count):
    form+offset   the listed form followed by a pointer-arithmetic chain (`L.as_mut_ptr().offset(k)`, `.add(k)`, ...)
    root static / param / projected (field or index path) for the listed forms.

usage: a4_bridges.py            (writes a4-sites.tsv, a4-all-bridges.tsv, a4-per-program.tsv next to this script)
       a4_bridges.py --validate (libzahl cross-check against r148/sites/ours-libzahl.tsv + the MIR dumps)
"""
import collections, csv, os, re, sys

TREES = "scratch/main/batch60sp/emitted-trees"
INPUT = "crat/benchmarks/rs-crown"
OUT = os.path.dirname(os.path.abspath(__file__))
R148 = "scratch/analysis-fanout/r148"
PROGRAMS = ["avl", "binn", "brotli", "bst", "buffer", "bzip2", "genann", "heman", "ht", "json.h", "libcsv",
            "libtree", "libzahl", "lil", "lodepng", "quadtree", "rgba", "robotfindskitten", "tulipindicators",
            "urlparser"]
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
KEYWORDS = {"mut", "ref", "let", "if", "else", "match", "while", "loop", "for", "in", "return", "as", "fn", "pub",
            "unsafe", "extern", "static", "const", "move", "break", "continue", "true", "false", "Some", "None",
            "Ok", "Err", "self", "Self", "crate", "super", "where", "impl", "struct", "enum", "mod", "use", "type",
            "dyn", "box", "raw"}


# ---------------------------------------------------------------- lexing
def blank(src):
    """comments, string and char literals -> spaces (newlines kept), so offsets and line numbers survive."""
    out = list(src)
    n = len(src)
    i = 0

    def wipe(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            j = n if j < 0 else j
            wipe(i, j)
            i = j
        elif c == "/" and i + 1 < n and src[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth += 1
                    j += 2
                elif src.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            wipe(i, j)
            i = j
        elif c in "rb" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")) and \
                re.match(r'(br|r|b)?#*"', src[i:i + 8]) and re.match(r'(br|r)#*"', src[i:i + 8]):
            m = re.match(r'(br|r)(#*)"', src[i:])
            close = '"' + m.group(2)
            j = src.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            wipe(i + m.end() - 1, j)
            i = j
        elif c == '"' or (c == "b" and i + 1 < n and src[i + 1] == '"' and
                          (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_"))):
            j = i + (2 if c == "b" else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            wipe(i, j + 1)
            i = j + 1
        elif c == "'":
            # char literal vs lifetime / label
            m = re.match(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'])'", src[i:i + 14])
            if m:
                wipe(i, i + m.end())
                i += m.end()
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


def match_close(s, i):
    """s[i] in '([{' -> index of its matching closer (bracket kinds counted together; literals already blanked)."""
    depth = 0
    for j in range(i, len(s)):
        c = s[j]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0:
                return j
    return -1


def skip_ws(s, i):
    while i < len(s) and s[i].isspace():
        i += 1
    return i


def prev_nonws(s, i):
    j = i - 1
    while j >= 0 and s[j].isspace():
        j -= 1
    return j


# ---------------------------------------------------------------- items
def functions(s):
    """[(qualified name, body_open, body_close, params set, param_end)] incl. nested fns; module path tracked."""
    mods = []      # (name, close)
    fns = []
    for m in re.finditer(r"\b(mod\s+([A-Za-z_]\w*)\s*\{|fn\s+([A-Za-z_]\w*))", s):
        pos = m.start()
        while mods and mods[-1][1] < pos:
            mods.pop()
        if m.group(2):
            o = m.end() - 1
            mods.append((m.group(2), match_close(s, o)))
            continue
        name = m.group(3)
        j = skip_ws(s, m.end())
        if j < len(s) and s[j] == "<":           # generics
            depth = 0
            while j < len(s):
                if s[j] == "<":
                    depth += 1
                elif s[j] == ">" and s[j - 1] != "-":
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
            j = skip_ws(s, j)
        if j >= len(s) or s[j] != "(":
            continue
        pc = match_close(s, j)
        params = set()
        # params: `[mut] name: Type` at depth 1 of the parameter list
        depth, seg_start = 0, j + 1
        segs = []
        for k in range(j, pc + 1):
            c = s[k]
            if c in "([{<" and not (c == "<" and s[k - 1] == "-"):
                depth += 1
            elif c in ")]}" or (c == ">" and s[k - 1] != "-"):
                depth -= 1
            if (c == "," and depth == 1) or k == pc:
                segs.append(s[seg_start:k])
                seg_start = k + 1
        for seg in segs:
            pm = re.match(r"\s*(?:mut\s+)?([A-Za-z_]\w*)\s*:", seg)
            if pm:
                params.add(pm.group(1))
        # body: first '{' or ';' after the signature at bracket depth 0
        k = pc + 1
        while k < len(s) and s[k] not in "{;":
            if s[k] in "([":
                k = match_close(s, k)
            k += 1
        if k >= len(s) or s[k] == ";":
            continue
        bc = match_close(s, k)
        qual = "::".join([md[0] for md in mods] + [name])
        fns.append((qual, k, bc, params, pc))
    return fns


def statics(s):
    return set(re.findall(r"\bstatic\s+(?:mut\s+)?([A-Za-z_]\w*)\s*:", s))


def let_bindings(s, a, b):
    """[(name, pos)] for every `let` pattern identifier in s[a:b]."""
    out = []
    for m in re.finditer(r"\blet\s+", s[a:b]):
        p = a + m.end()
        # pattern runs to the first top-level ':' or '=' (not '==')
        depth, k = 0, p
        while k < b:
            c = s[k]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and (c == ";" or (c == "=" and s[k + 1] != "=") or (c == ":" and s[k + 1] != ":")):
                break
            k += 1
        pat = s[p:k]
        for im in IDENT.finditer(pat):
            nm = im.group(0)
            if nm in KEYWORDS or nm[0].isupper():
                continue
            after = pat[im.end():].lstrip()
            before = pat[:im.start()].rstrip()
            if after.startswith(("(", "{", "::")) or before.endswith("::"):
                continue
            out.append((nm, a + m.start()))
    return out


# ---------------------------------------------------------------- the operand
def postfix_end(s, i):
    """s[i] starts a primary expression (after optional ws); return end index (exclusive) of the postfix expression."""
    i = skip_ws(s, i)
    if i >= len(s):
        return i
    c = s[i]
    if c in "([":
        j = match_close(s, i) + 1
    elif c == "*" or c == "&" or c == "!" or c == "-":
        # unary inside the operand (`&**pp`, `&*&raw mut x`): operand of the unary is itself a unary expr
        j = i + 1
        if c == "&":
            j = skip_ws(s, j)
            mm = re.match(r"(raw\s+(mut|const)\s+|mut\s+)", s[j:])
            if mm:
                j += mm.end()
        return postfix_end(s, j)
    else:
        m = re.match(r"(::)?[A-Za-z_]\w*(\s*::\s*(<[^;{}]*?>|[A-Za-z_]\w*))*", s[i:])
        if not m:
            return i
        j = i + m.end()
        k = skip_ws(s, j)
        if k < len(s) and s[k] == "!":                    # macro call
            k2 = skip_ws(s, k + 1)
            if k2 < len(s) and s[k2] in "([{":
                j = match_close(s, k2) + 1
        elif k < len(s) and s[k] == "{" and m.group(0)[0].isupper():   # struct literal
            j = match_close(s, k) + 1
    while True:
        k = skip_ws(s, j)
        if k < len(s) and s[k] in "([":
            j = match_close(s, k) + 1
        elif k < len(s) and s[k] == "?":
            j = k + 1
        elif k < len(s) and s[k] == "." and not s.startswith("..", k):
            m = re.match(r"\.\s*([A-Za-z_]\w*|\d+)(\s*::\s*<[^;{}]*?>)?", s[k:])
            if not m:
                return j
            j = k + m.end()
        else:
            return j


def strip_parens(e):
    e = e.strip()
    while e.startswith("(") and match_close(e, 0) == len(e) - 1:
        e = e[1:-1].strip()
    return e


ROOT = r"(?P<root>[A-Za-z_]\w*(?:\s*(?:\.\s*[A-Za-z_]\w*|\.\s*\d+|\[[^\[\]]*\]))*)"
CAST = r"(?:\s+as\s+\*\s*(?:mut|const)\s+[^,;]+?)+"
OFFS = r"(?P<offs>(?:\s*\.\s*(?:offset|add|sub|wrapping_offset|wrapping_add|wrapping_sub|byte_offset|byte_add)\s*\((?:[^()]|\([^()]*(?:\([^()]*\)[^()]*)*\))*\))+)"
FORMS = [
    ("as_mut_ptr", re.compile(r"^\(?\s*" + ROOT + r"\s*\)?\s*\.\s*as_mut_ptr\s*\(\s*\)$")),
    ("as_ptr", re.compile(r"^\(?\s*" + ROOT + r"\s*\)?\s*\.\s*as_ptr\s*\(\s*\)$")),
    ("cast_mut", re.compile(r"^&\s*mut\s+\(?\s*" + ROOT + r"\s*\)?" + CAST + r"$")),
    ("cast_const", re.compile(r"^&\s*\(?\s*" + ROOT + r"\s*\)?" + CAST + r"$")),
    ("raw_mut", re.compile(r"^&\s*raw\s+mut\s+\(?\s*" + ROOT + r"\s*\)?$")),
    ("raw_const", re.compile(r"^&\s*raw\s+const\s+\(?\s*" + ROOT + r"\s*\)?$")),
    ("addr_of_mut", re.compile(r"^(?:(?:::)?(?:core|std)\s*::\s*)?(?:ptr\s*::\s*)?addr_of_mut\s*!\s*\(\s*" + ROOT + r"\s*\)$")),
    ("addr_of", re.compile(r"^(?:(?:::)?(?:core|std)\s*::\s*)?(?:ptr\s*::\s*)?addr_of\s*!\s*\(\s*" + ROOT + r"\s*\)$")),
    # ADJACENT (reported, never in the primary count): ptr::from_mut(&mut L)[.cast::<..>()] / from_ref(&L)
    ("adj_from_mut", re.compile(r"^(?:(?:::)?(?:core|std)\s*::\s*)?(?:ptr\s*::\s*)?from_(?:mut|ref)\s*\(\s*&\s*(?:mut\s+)?" + ROOT + r"\s*\)(?:\s*\.\s*cast(?:_mut|_const)?\s*(?:::\s*<[^;{}]*>)?\s*\(\s*\))?$")),
]
LISTED = {"as_mut_ptr", "as_ptr", "cast_mut", "cast_const", "raw_mut", "raw_const", "addr_of_mut", "addr_of"}


def classify_operand(e):
    """-> (form, root text, offset suffix or '') ; form 'other' when no listed form matches."""
    e = strip_parens(e)
    for name, rx in FORMS:
        m = rx.match(e)
        if m:
            return name, re.sub(r"\s+", "", m.group("root")), ""
    # listed form + pointer arithmetic chain
    m = re.match(r"^(?P<base>.*?)" + OFFS + r"$", e, re.S)
    if m:
        base = strip_parens(m.group("base"))
        for name, rx in FORMS:
            mm = rx.match(base)
            if mm:
                return name, re.sub(r"\s+", "", mm.group("root")), re.sub(r"\s+", " ", m.group("offs").strip())
    return "other", "", ""


# ---------------------------------------------------------------- context
def context_of(s, amp, end, fn_open):
    """(context, callee) of the reference expression s[amp:end]."""
    j = skip_ws(s, end)
    nxt = s[j] if j < len(s) else ""
    if s.startswith("as", j) and not (s[j + 2:j + 3].isalnum() or s[j + 2:j + 3] == "_"):
        return "cast", ""
    if nxt == "." and not s.startswith("..", j):
        return "method-receiver", ""
    p = prev_nonws(s, amp)
    pc = s[p] if p >= 0 else ""
    if pc in "(," and nxt in ",)":
        # find the enclosing open paren
        depth, k = 0, amp - 1
        while k > fn_open:
            c = s[k]
            if c in ")]}":
                depth += 1
            elif c in "([{":
                if depth == 0:
                    break
                depth -= 1
            k -= 1
        if s[k] != "(":
            return "other", ""
        q = prev_nonws(s, k)
        # callee text before '('
        if q >= 0 and s[q] == "!":
            mm = re.search(r"([A-Za-z_][\w:]*)\s*!$", s[max(0, q - 200):q + 1])
            return "macro-arg", (mm.group(1) + "!") if mm else "?!"
        if q >= 0 and s[q] == ">":                     # turbofish f::<T>(..)
            d, r = 0, q
            while r > 0:
                if s[r] == ">":
                    d += 1
                elif s[r] == "<":
                    d -= 1
                    if d == 0:
                        break
                r -= 1
            q = prev_nonws(s, r)
            if q >= 1 and s[q - 1:q + 1] == "::":
                q = prev_nonws(s, q - 1)
        if q >= 0 and (s[q].isalnum() or s[q] == "_"):
            mm = re.search(r"(\.\s*)?((?:[A-Za-z_]\w*\s*::\s*)*[A-Za-z_]\w*)$", s[max(0, q - 200):q + 1])
            name = re.sub(r"\s+", "", mm.group(2))
            if name in ("if", "while", "match", "return", "in"):
                return "other", ""
            return "call-arg", ("." + name if mm.group(1) else name)
        if q >= 0 and s[q] == ")":
            return "call-arg", "(expr)"
        return "paren", ""
    if pc == "=" and p >= 1 and s[p - 1] not in "=!<>":
        if nxt in ";":
            # statement start
            k = p
            while k > fn_open and s[k] not in ";{}":
                k -= 1
            stmt = s[k + 1:p].strip()
            if re.match(r"let\b", stmt):
                return "let-bound", ""
            return "assigned", ""
        return "other", ""
    return "other", ""


# ---------------------------------------------------------------- driver
def scan_program(p, root=None):
    rows = []
    d = os.path.join(root or TREES, p)
    for fname in sorted(os.listdir(d)):
        if not fname.endswith(".rs"):
            continue
        path = os.path.join(d, fname)
        raw = open(path, encoding="utf-8", errors="replace").read()
        s = blank(raw)
        line_starts = [0]
        for m in re.finditer("\n", s):
            line_starts.append(m.end())
        import bisect

        def lc(off):
            ln = bisect.bisect_right(line_starts, off)
            return ln, off - line_starts[ln - 1] + 1

        fns = functions(s)
        stats = statics(s)
        lets_cache = {}
        for m in re.finditer(r"&\s*(?:mut\s+)?\*", s):
            amp = m.start()
            if amp > 0 and s[amp - 1] == "&":
                continue                                   # `&&` (logical and / double ref) -- see unary test
            p_ = prev_nonws(s, amp)
            if p_ >= 0 and (s[p_].isalnum() or s[p_] in "_)]'\""):
                # binary `&`; but keywords before a unary & are fine
                wm = re.search(r"([A-Za-z_]\w*)$", s[max(0, p_ - 80):p_ + 1])
                if not (wm and wm.group(1) in ("return", "in", "else", "break", "match", "if", "while")):
                    continue
            star = m.end() - 1
            e_end = postfix_end(s, star + 1)
            operand = s[star + 1:e_end]
            enc = [f for f in fns if f[1] < amp < f[2]]
            if not enc:
                continue
            fq, fo, fc, params, pend = max(enc, key=lambda f: f[1])
            # nested fns: exclude bodies of inner fns from the let scan by construction (innermost chosen)
            form, root, offs = classify_operand(operand)
            ctx, callee = context_of(s, amp, e_end, fo)
            root_kind, root_shape, local = "", "", ""
            if form != "other":
                base = re.match(r"[A-Za-z_]\w*", root).group(0)
                root_shape = "bare" if base == root else ("index" if root[len(base):].startswith("[") else "field")
                key = (fq, fo)
                if key not in lets_cache:
                    inner = [f for f in fns if fo < f[1] and f[2] < fc]
                    ls = []
                    for nm, pos in let_bindings(s, fo, fc):
                        if not any(f[1] < pos < f[2] for f in inner):
                            ls.append((nm, pos))
                    lets_cache[key] = ls
                if any(nm == base and pos < amp for nm, pos in lets_cache[key]):
                    root_kind = "local"
                elif base in params:
                    root_kind = "param"
                elif base in stats:
                    root_kind = "static"
                else:
                    root_kind = "other"
                local = base
            ln, col = lc(amp)
            text = re.sub(r"\s+", " ", raw[amp:e_end])
            rows.append(dict(program=p, file=fname, line=ln, col=col, function=fq,
                             ref="&mut" if "mut" in m.group(0) else "&", form=form, offset=offs,
                             root_kind=root_kind, root_shape=root_shape, local=local, context=ctx, callee=callee,
                             text=text))
    return rows


def primary(r):
    return (r["form"] in LISTED and not r["offset"] and r["root_kind"] == "local" and r["root_shape"] == "bare"
            and r["context"] in ("call-arg", "let-bound", "assigned"))


def main():
    allrows = []
    for p in PROGRAMS:
        allrows += scan_program(p)
    formnames = [n for n, _ in FORMS if n in LISTED]
    # input counterparts: the same function (last path segment), local and callee bridged in the input tree
    inp = collections.Counter()
    import glob
    for p in PROGRAMS:
        base = os.path.join(INPUT, p)
        for d in sorted({os.path.dirname(f) for f in glob.glob(base + "/**/*.rs", recursive=True)}):
            if "/target/" in d:
                continue
            for r in scan_program(os.path.basename(d), os.path.dirname(d)):
                if r["form"] in LISTED and r["root_kind"] == "local":
                    inp[(p, r["function"].split("::")[-1], r["local"], r["callee"].split("::")[-1],
                         re.sub(r"\s+", "", r["offset"]))] += 1
    for r in allrows:
        r["input_counterpart"] = ""
        if not primary(r):
            continue
        k0 = (r["program"], r["function"].split("::")[-1], r["local"], r["callee"].split("::")[-1])
        for off in ("", ".offset(0aslibc::c_intasisize)", ".offset(0asstd::os::raw::c_intasisize)"):
            if inp[k0 + (off,)] > 0:
                inp[k0 + (off,)] -= 1
                r["input_counterpart"] = "input-bridged" + (" (as " + off + ")" if off else "")
                break
        else:
            r["input_counterpart"] = "new (input passed the raw pointer itself)" \
                if r["context"] == "call-arg" else "new"
    cols = ["program", "file", "line", "col", "function", "ref", "form", "offset", "root_kind", "root_shape", "local",
            "context", "callee", "input_counterpart", "text"]
    with open(os.path.join(OUT, "a4-all-bridges.tsv"), "w", newline="") as f:
        w = csv.DictWriter(f, cols, delimiter="\t", lineterminator="\n")
        w.writeheader()
        w.writerows(allrows)
    with open(os.path.join(OUT, "a4-sites.tsv"), "w", newline="") as f:
        w = csv.DictWriter(f, cols, delimiter="\t", lineterminator="\n")
        w.writeheader()
        w.writerows([r for r in allrows if primary(r)])
    with open(os.path.join(OUT, "a4-per-program.tsv"), "w", newline="") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        hdr = (["program", "bridges_all", "PRIMARY", "PRIMARY_new", "PRIMARY_input_bridged"] + ["p_" + n for n in formnames] +
               ["p_call_arg", "p_let_bound", "p_assigned",
                "x_local_offset", "x_local_projected", "x_local_other_ctx", "x_static", "x_static_offset", "x_param",
                "x_other_root", "x_adjacent_from_mut_local", "x_other_form"])
        w.writerow(hdr)
        tot = collections.Counter()
        for p in PROGRAMS + ["TOTAL"]:
            rs = allrows if p == "TOTAL" else [r for r in allrows if r["program"] == p]
            listed = [r for r in rs if r["form"] in LISTED]
            c = collections.OrderedDict()
            c["bridges_all"] = len(rs)
            c["PRIMARY"] = sum(primary(r) for r in rs)
            c["PRIMARY_new"] = sum(primary(r) and r["input_counterpart"].startswith("new") for r in rs)
            c["PRIMARY_input_bridged"] = sum(primary(r) and r["input_counterpart"].startswith("input") for r in rs)
            for n in formnames:
                c["p_" + n] = sum(primary(r) and r["form"] == n for r in rs)
            for cx, k in (("call-arg", "p_call_arg"), ("let-bound", "p_let_bound"), ("assigned", "p_assigned")):
                c[k] = sum(primary(r) and r["context"] == cx for r in rs)
            loc = [r for r in listed if r["root_kind"] == "local"]
            c["x_local_offset"] = sum(1 for r in loc if r["offset"] and r["root_shape"] == "bare")
            c["x_local_projected"] = sum(1 for r in loc if r["root_shape"] != "bare")
            c["x_local_other_ctx"] = sum(1 for r in loc if not r["offset"] and r["root_shape"] == "bare"
                                         and r["context"] not in ("call-arg", "let-bound", "assigned"))
            c["x_static"] = sum(1 for r in listed if r["root_kind"] == "static" and not r["offset"])
            c["x_static_offset"] = sum(1 for r in listed if r["root_kind"] == "static" and r["offset"])
            c["x_param"] = sum(1 for r in listed if r["root_kind"] == "param")
            c["x_other_root"] = sum(1 for r in listed if r["root_kind"] == "other")
            c["x_adjacent_from_mut_local"] = sum(1 for r in rs if r["form"] == "adj_from_mut" and r["root_kind"] == "local")
            c["x_other_form"] = sum(1 for r in rs if r["form"] not in LISTED)
            w.writerow([p] + list(c.values()))
    print("rows", len(allrows), "primary", sum(primary(r) for r in allrows),
          "new", sum(primary(r) and r["input_counterpart"].startswith("new") for r in allrows))


# ---------------------------------------------------------------- libzahl validation against the MIR
def validate():
    rows = [r for r in scan_program("libzahl") if r["file"] == "lib.rs"]
    src = {}
    for r in rows:
        src[(r["line"], r["col"])] = r
    sites = list(csv.DictReader(open(os.path.join(R148, "sites/ours-libzahl.tsv")), delimiter="\t"))
    dumpdir = os.path.join(R148, "mir/ours/libzahl/dump")
    files = {}
    for fn in os.listdir(dumpdir):
        if fn.endswith(".SimplifyCfg-promote-consts.after.mir"):
            files[fn[len("lib."):-len(".SimplifyCfg-promote-consts.after.mir")]] = os.path.join(dumpdir, fn)
    cache = {}

    def mir(fq):
        if fq in cache:
            return cache[fq]
        key = fq.replace("::", "-")
        text = open(files[key]).read() if key in files else ""
        defs, debug, argc = collections.defaultdict(list), {}, 0
        for ln in text.splitlines():
            code = ln.split("//")[0].strip()
            dm = re.match(r"debug (\w+) => _(\d+);", code)
            if dm:
                debug[int(dm.group(2))] = dm.group(1)
            am = re.match(r"fn [^(]*\((.*)\)\s*->", code) or re.match(r"fn [^(]*\((.*)\)", code)
            if am and argc == 0:
                argc = len(re.findall(r"_\d+:", am.group(1)))
            sm = re.match(r"_(\d+) = (.*?);?$", code)
            if sm:
                defs[int(sm.group(1))].append(sm.group(2))
        cache[fq] = (defs, debug, argc)
        return cache[fq]

    def trace_root(fq, t, depth=0):
        """root of the pointer temp _t: ('local', name) / ('param', name) / ('static', ...) / ('other', expr)."""
        defs, debug, argc = mir(fq)
        if depth > 12:
            return ("other", "deep"), ""
        if t in debug and depth > 0:
            return (("param" if 1 <= t <= argc else "local"), debug[t]), ""
        for d in defs.get(t, []):
            m = re.match(r"(?:core::slice::<impl \[.*\]>|core::ptr::.*|std::.*)?::?(as_mut_ptr|as_ptr)\((?:move |copy )?_(\d+)\)", d)
            if m:
                r, _ = trace_root(fq, int(m.group(2)), depth + 1)
                return r, m.group(1)
            m = re.match(r"&raw (?:mut|const) _(\d+)$", d)
            if m:
                r, _ = trace_root(fq, int(m.group(1)), depth + 1)
                return r, "raw"
            m = re.match(r"&(?:mut )?_(\d+)$", d)
            if m:
                r, _ = trace_root(fq, int(m.group(1)), depth + 1)
                return r, "ref"
            m = re.match(r"&raw (?:mut|const) \(\*_(\d+)\)$|&(?:mut )?\(\*_(\d+)\)$", d)
            if m:
                inner = int(m.group(1) or m.group(2))
                r, _ = trace_root(fq, inner, depth + 1)
                return r, "reborrow"
            m = re.match(r"(?:move|copy) _(\d+)(?: as .*)?$", d)
            if m:
                r, k = trace_root(fq, int(m.group(1)), depth + 1)
                return r, k
            m = re.match(r"const \{alloc|const \w", d)
            if m:
                return ("static", d[:40]), ""
            m = re.match(r".*::(offset|add|sub)\((?:move |copy )?_(\d+)", d)
            if m:
                r, k = trace_root(fq, int(m.group(2)), depth + 1)
                return r, "offset:" + k
            return ("other", d[:60]), ""
        return ("other", "nodef"), ""

    mir_sites = {}
    for r in sites:
        if r["phase"] != "promoted" or r["full_deref"] != "1" or r["name"] != "-":
            continue
        st = r["stmt"]
        m = re.match(r"_\d+ = &(?:mut )?\(\*_(\d+)\);$", st)
        if not m or r["place"] != "(*_%s)" % m.group(1):
            continue
        t = int(m.group(1))
        root, kind = trace_root(r["function"], t)
        sm = re.search(r":(\d+):(\d+): ", r["span"])
        mir_sites[(int(sm.group(1)), int(sm.group(2)))] = (r["function"], root, kind, st)
    # agreement on the primary definition (sources: as_mut_ptr / as_ptr / raw / cast of a bare local)
    src_primary = {k for k, r in src.items() if primary(r)}
    src_local_any = {k for k, r in src.items() if r["form"] != "other" and r["root_kind"] == "local"}
    mir_local = {k for k, v in mir_sites.items() if v[1][0] == "local" and not v[2].startswith("offset")}
    mir_local_bridges = {k for k in mir_local}
    out = []
    out.append("libzahl validation (ours = batch60sp emitted tree; promoted full_deref rows of an unnamed temp whose statement")
    out.append("is `_a = &[mut] (*_t)` -- the reference taken through the raw temp -- with _t traced back in the MIR dump)")
    out.append("source primary sites:                 %d" % len(src_primary))
    out.append("MIR bridge rows rooted at a fn local (no ptr arithmetic): %d" % len(mir_local))
    out.append("  in both (joined on line:col of the `&`): %d" % len(src_primary & mir_local))
    out.append("  source-only: %s" % sorted(src_primary - mir_local))
    out.append("  MIR-only:    %s" % sorted((mir_local - src_primary)))
    for k in sorted(mir_local - src_primary):
        out.append("    MIR-only %s -> %s ; source row: %s" % (k, mir_sites[k][:3], src.get(k, {}).get("text", "-")))
    kinds = collections.Counter()
    for k, v in mir_sites.items():
        kinds[(v[1][0], v[2].split(":")[0] if v[2] else "")] += 1
    out.append("all MIR `&[mut] (*temp)` full_deref rows by traced root kind / producer: %s" % dict(kinds))
    # zsetup / zmul / zsqr context
    for fq in ("src::zsetup::zsetup", "src::zmul::zmul", "src::zsqr::zsqr"):
        rs = [v for k, v in mir_sites.items() if v[0] == fq]
        out.append("%s: bridge rows %d, by root kind %s" % (fq, len(rs), dict(collections.Counter(v[1][0] for v in rs))))
    print("\n".join(out))
    with open(os.path.join(OUT, "a4-libzahl-validation.txt"), "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    if "--validate" in sys.argv:
        validate()
    else:
        main()

