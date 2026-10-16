#!/usr/bin/env python3
"""Interface positions (parameters, returns, struct fields of pointer C type, of functions DEFINED in the program /
structs defined in the program) on both sides.
  inator  <results dir>  -> rows from stypes.txt (C side, ptr(...) outermost) + rtypes.txt (&inator's type, same label)
  c2rust  <crate dir>    -> rows from a C2Rust translation (src/*.rs): pointer / fnptr / non-pointer by the Rust type
Output rows: side, kind (param|return|field), owner (function or struct), index, name, ctype/raw type, bucket.
Fails closed through SystemExit."""
import glob, os, re, sys

SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")


def die(m):
    raise SystemExit("positions: FAIL: " + m)


def strip_labels(t):
    """[ptr([i8]²⁴²)]²⁴¹ -> ptr(i8) ; [&'703 mut [struct(x)<'618, >]²⁸⁸]²⁸⁷ -> &'703 mut struct(x)<'618, >"""
    t = re.sub(r"[⁰¹²³⁴⁵⁶⁷⁸⁹]+", "", t)
    return t.replace("[", "").replace("]", "")


def outer(t):
    """the outermost constructor of a de-labelled type"""
    return t.strip()


def inator_bucket(rt):
    t = outer(rt)
    if re.match(r"^&'\d+ mut ", t):
        return "mut", t
    if re.match(r"^&'\d+ ", t):
        return "ref", t
    for k, b in (("Box<", "box"), ("Rc<", "rc"), ("RefCell<", "refcell"), ("Cell<", "cell"), ("ghost<", "ghost")):
        if t.startswith(k):
            return b, t
    return "other", t


def split_type_name(line):
    """'    [T]label name, ' -> (typetext, name)"""
    s = line.strip().rstrip(",").strip()
    m = re.match(r"^(.*[⁰¹²³⁴⁵⁶⁷⁸⁹\]])\s+(\S+)$", s)
    if not m:
        die("cannot split: %r" % line)
    return m.group(1), m.group(2)


def parse_inator_file(path):
    """{('param'|'return'|'field', owner, index): (name, typetext)} plus the set of defined functions"""
    lines = open(path, encoding="utf-8").read().split("\n")
    out, defined, declared = {}, set(), set()
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r"^struct (\S+?)<.*?>\s+\{$", l) or re.match(r"^struct (\S+)\s+\{$", l)
        if m:
            sname = m.group(1)
            i += 1
            while not lines[i].startswith("};"):
                fm = re.match(r"^\s+(.*?)\s+(\d+);$", lines[i])
                if not fm:
                    die("struct field: %r" % lines[i])
                out[("field", sname, int(fm.group(2)))] = (fm.group(2), fm.group(1))
                i += 1
            i += 1
            continue
        m0 = re.match(r"^(\[.*[⁰¹²³⁴⁵⁶⁷⁸⁹])\s+(\S+)\(\)( \{|;)$", l)
        if m0:   # a function with no parameters on one line
            if m0.group(3) == " {":
                defined.add(m0.group(2))
                out[("return", m0.group(2), -1)] = ("return", m0.group(1))
            else:
                declared.add(m0.group(2))
            i += 1
            continue
        m = re.match(r"^(\[.*[⁰¹²³⁴⁵⁶⁷⁸⁹])\s+(\S+)\($", l)
        if m:
            ret, fname = m.group(1), m.group(2)
            params = []
            i += 1
            while not lines[i].startswith(")"):
                params.append(split_type_name(lines[i]))
                i += 1
            body = lines[i].strip() == ") {"
            if body:
                defined.add(fname)
                out[("return", fname, -1)] = ("return", ret)
                for k, (t, n) in enumerate(params):
                    out[("param", fname, k)] = (n, t)
            else:
                declared.add(fname)
            i += 1
            continue
        i += 1
    return out, defined, declared


def inator_rows(results_dir):
    st, defs, decl = parse_inator_file(os.path.join(results_dir, "stypes.txt"))
    rt, defs2, decl2 = parse_inator_file(os.path.join(results_dir, "rtypes.txt"))
    if set(st) != set(rt) or defs != defs2:
        die("stypes/rtypes position sets differ in " + results_dir)
    rows = []
    for key in sorted(st, key=lambda k: (k[1], k[0], k[2])):
        name, stt = st[key]
        c = strip_labels(stt)
        if key[0] == "field":
            # a struct field prints as its PLACE: stypes ptr(<field type>), rtypes <place type>(<field type>)
            if not c.startswith("ptr(") or not c.endswith(")"):
                die("field not printed as a place: %r %r" % (key, c))
            c = c[4:-1]
        sptr = c.startswith("ptr(")
        b, t = inator_bucket(strip_labels(rt[key][1]))
        inner = ""
        if b == "ghost":
            inner = re.sub(r"^ghost<", "", t)
            inner = re.split(r"[<>\[ ]", inner)[0] or inner[:20]
        rows.append({"kind": key[0], "owner": key[1], "index": key[2], "name": name, "ctype": c, "rtype": t,
                     "bucket": b, "ghost_inner": inner, "sptr": sptr, "stype": c})
    return rows, defs, decl


# ---------------------------------------------------------------- c2rust side
def split_top(s, sep=","):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "(<[":
            depth += 1
        elif ch in ")>]":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out if x.strip()]


def rust_kind(t):
    t = t.strip()
    if re.match(r"^Option<\s*unsafe extern \"C\" fn", t) or t.startswith("unsafe extern \"C\" fn"):
        return "fnptr"
    if t.startswith("*mut") or t.startswith("*const"):
        return "pointer"
    return "non-pointer"


def c2rust_rows(crate):
    text = ""
    for f in sorted(glob.glob(os.path.join(crate, "src", "**", "*.rs"), recursive=True)):
        text += open(f, encoding="utf-8").read() + "\n"
    # drop extern blocks
    body = re.sub(r"extern \"C\" \{.*?\n\s*\}", "", text, flags=re.S)
    aliases = {m.group(1): m.group(2).strip() for m in re.finditer(r"^pub type (\w+) = (.*?);$", text, flags=re.M)}

    def resolve(t):
        t = t.strip()
        for _ in range(20):
            if t in aliases:
                t = aliases[t]
            else:
                break
        return t
    rows = []
    for m in re.finditer(r"^\s*(?:pub )?(?:unsafe )?(?:extern \"C\" )?fn (\w+)\(", body, flags=re.M):
        name = m.group(1)
        j = m.end()
        depth = 1
        while depth:
            ch = body[j]
            depth += ch == "("
            depth -= ch == ")"
            j += 1
        args = body[m.end():j - 1]
        rest = body[j:j + 400]
        rm = re.match(r"\s*(?:->\s*(.*?))?\s*\{", rest, flags=re.S)
        if not rm:
            continue  # a declaration without a body
        ret = (rm.group(1) or "()").strip()
        for k, a in enumerate(split_top(args)):
            if ":" not in a:
                continue
            n, t = a.split(":", 1)
            n = n.replace("mut ", "").strip()
            rows.append({"kind": "param", "owner": name, "orig_owner": name, "index": k, "name": n, "rtype": t.strip(), "ck": rust_kind(resolve(t))})
        rows.append({"kind": "return", "owner": name, "orig_owner": name, "index": -1, "name": "return", "rtype": ret, "ck": rust_kind(resolve(ret))})
    for m in re.finditer(r"^\s*pub (struct|union) (\w+) \{(.*?)\n\s*\}", body, flags=re.M | re.S):
        fields = [x for x in split_top(m.group(3).replace("\n", " ")) if x.startswith("pub ")]
        for k, fld in enumerate(fields):
            n, t = fld[4:].split(":", 1)
            rows.append({"kind": "field", "owner": m.group(2), "orig_owner": m.group(2), "index": k, "name": n.strip(), "rtype": t.strip(),
                         "ck": rust_kind(resolve(t))})
    return rows


if __name__ == "__main__":
    side, path = sys.argv[1], sys.argv[2]
    rows = inator_rows(path)[0] if side == "inator" else c2rust_rows(path)
    for r in rows:
        print("\t".join(str(r.get(k, "")) for k in ("kind", "owner", "index", "name", "bucket" if side == "inator" else "ck", "rtype")))
