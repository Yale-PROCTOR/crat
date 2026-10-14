#!/usr/bin/env python3
"""analysis-fanout relay 148, task A3 (libzahl caller side).
Every call-site bridge in ours (the landed 60s' tree, mir_promoted dump): a reference temporary built from a deref
of a raw pointer (`_r = &(*p)` / `&mut (*p)` / `&mut (*p)[i]`, p raw-typed), followed through reborrows/copies to
a Call argument whose callee formal type is a reference. For each bridge: the deref base's root (formal / named
local / temporary traced to a field load, a call result, a cast, ...), and for formal / named-local roots the census
row of the landed head (main/batch60sp) that holds it raw. Read-only; writes only into this directory.
usage: a3_callers.py"""
import collections, csv, glob, os, re, sys

R = "scratch/analysis-fanout/r148"
DUMP = R + "/mir/ours/libzahl/dump"
SITES = R + "/sites/ours-libzahl.tsv"
CEN = "scratch/main/batch60sp/libzahl.raw-boundary-%s.tsv"
DERIVED = "crat/benchmarks/rs-crown-derived/libzahl/lib.rs"
OUT = os.path.dirname(os.path.abspath(__file__))
SUF = ".SimplifyCfg-promote-consts.after.mir"


def code(line):
    i = line.find("//")
    return (line if i < 0 else line[:i]).strip()


def split_top(s):
    out, d, cur = [], 0, ""
    for i, c in enumerate(s):
        if c in "([{<":
            d += 1
        elif c in ")]}" or (c == ">" and (i == 0 or s[i - 1] != "-")):
            d -= 1
        if c == "," and d == 0:
            out.append(cur.strip()); cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


def fn_sig_args(ty):
    """'for<'a> unsafe extern "C" fn(&'a T, *mut U) -> i32 {zadd::zzero}' -> ([formal types], callee path)"""
    m = re.search(r"\{([^{}]*)\}\s*$", ty)
    path = m.group(1) if m else "?"
    i = ty.find("fn(")
    if i < 0:
        return None, path
    j, d = i + 3, 1
    while j < len(ty) and d:
        if ty[j] == "(":
            d += 1
        elif ty[j] == ")":
            d -= 1
        j += 1
    return split_top(ty[i + 3:j - 1]), path


def parse(path):
    txt = open(path).read().splitlines()
    fn = {"argc": 0, "ty": {}, "name": {}, "bbs": collections.OrderedDict(), "span": {}}
    hdr = next((l for l in txt if l.startswith("fn ")), "")
    if hdr:
        a = hdr[hdr.find("(") + 1:]
        a = a[:a.rfind(") ->")] if ") ->" in a else a[:a.rfind(")")]
        for p in split_top(a):
            m = re.match(r"_(\d+): (.*)$", p)
            if m:
                fn["ty"][int(m.group(1))] = m.group(2); fn["argc"] += 1
    cur = None
    for k, line in enumerate(txt):
        c = code(line)
        m = re.match(r"debug (\S+) => _(\d+);", c)
        if m:
            fn["name"].setdefault(int(m.group(2)), m.group(1)); continue
        m = re.match(r"let (?:mut )?_(\d+): (.*);$", c)
        if m:
            fn["ty"][int(m.group(1))] = m.group(2); continue
        m = re.match(r"(bb\d+)(?: \(cleanup\))?: \{", c)
        if m:
            cur = m.group(1); fn["bbs"][cur] = {"stmts": [], "cleanup": "(cleanup)" in c}; continue
        if cur and c == "}":
            cur = None; continue
        if cur and c:
            sp = re.search(r"at (\S+:\d+:\d+: \d+:\d+)", line)
            st = {"text": c, "span": sp.group(1) if sp else "", "const": None}
            if "->" in c and "(" in c:
                # the callee's const type follows on the comment lines
                for l2 in txt[k + 1:k + 6]:
                    m2 = re.search(r"\+ const_: Const \{ ty: (.*), val: ", l2)
                    if m2:
                        st["const"] = m2.group(1); break
                    if code(l2):
                        break
            fn["bbs"][cur]["stmts"].append(st)
    return fn


def is_raw(t):
    return t is not None and (t.startswith("*mut ") or t.startswith("*const "))


def is_ref(t):
    return t is not None and t.startswith("&")


def main():
    files = sorted(glob.glob(DUMP + "/lib.*" + SUF))
    fns = {}
    for f in files:
        name = os.path.basename(f)[4:-len(SUF)].replace("-", "::")
        fns[name] = parse(f)
    local_fns = set(fns)

    def resolve_callee(p):
        if p in local_fns:
            return p
        c = [n for n in local_fns if n.endswith("::" + p)]
        return c[0] if len(c) == 1 else None

    # counted deref sites (ours, promoted): (function, bb, stmt) -> full_deref count; official per (function, span, stmt)
    fd, off = collections.Counter(), collections.Counter()
    for r in csv.DictReader(open(SITES), delimiter="\t"):
        if r["phase"] == "promoted":
            fd[(r["function"], r["bb"], r["stmt"])] += int(r["full_deref"])
        else:
            off[(r["function"], r["span"], r["stmt"])] += int(r["official"])

    # census
    def rd(n):
        return list(csv.DictReader(open(CEN % n), delimiter="\t"))
    subj = {(r["owner_fn"], r["subject_key"].split("::")[-1].split("#")[0]): r for r in rd("subjects")
            if "#" in r["subject_key"]}
    outc = {r["subject_key"]: r for r in rd("subject-outcomes")}
    sidx = {r["subject_identity"]: r for r in rd("subject-index")}
    held = collections.defaultdict(list)
    for r in rd("settled-holds"):
        held[r["subject"]].append(r["predicate"])
    entry = {}
    for r in rd("exported-entry-pairs"):
        for fm in r["formals"].split(","):
            entry[(r["entry"], fm)] = r["receipt"]
    ewin = {(r["owner_fn"], r["parameter"]): r["receipt"] for r in rd("entry-window-receipt")}
    ppre = rd("pair-premise")
    # the static-vs-entry waiver (StaticVsEntryWaived): sibling proofs in the replay's sibling audit, keyed on the
    # site's SOURCE subject (the caller-side operand)
    import json
    sva = collections.Counter()
    rp = json.load(open("scratch/main/batch60sp/libzahl.raw-boundary-bridge-replay.json"))
    for a in rp["replay"]["export"]["sibling_audit"]["rows"]:
        for sb in a.get("siblings", []):
            if "static-vs-entry" in json.dumps(sb.get("proof", {})):
                sva[a["source"].get("identity")] += 1
    src = open(DERIVED).read().splitlines()

    def span_text(sp):
        m = re.match(r"<program>/lib\.rs:(\d+):(\d+): (\d+):(\d+)", sp)
        if not m:
            return None
        l1, c1, l2, c2 = map(int, m.groups())
        if l1 != l2:
            return None
        return src[l1 - 1][c1 - 1:c2 - 1]

    # pairs rows per (caller, argument text in the derived tree)
    pairs_by = collections.defaultdict(list)
    for r in rd("pairs"):
        t = span_text(r["site"])
        if t:
            t = re.sub(r"^&(mut )?\*", "", t.strip())
            pairs_by[(r["caller"], t)].append(r)

    rows, nonlocal_calls, unused = [], collections.Counter(), []
    acct = collections.Counter()
    for fname, fn in fns.items():
        defs = collections.defaultdict(list)      # local -> [(rvalue text, stmt)]
        uses = []                                  # (bb, idx, stmt)
        for bb, b in fn["bbs"].items():
            for i, st in enumerate(b["stmts"]):
                m = re.match(r"_(\d+) = (.*?);?$", st["text"])
                if m:
                    defs[int(m.group(1))].append((m.group(2), st))
                uses.append((bb, i, st))
        for bb, b in fn["bbs"].items():
            if b["cleanup"]:
                continue
            for i, st in enumerate(b["stmts"]):
                m = re.match(r"_(\d+) = &(mut )?\(\*_(\d+)\)(\[_\d+\])?;$", st["text"])
                if not m:
                    continue
                dst, base = int(m.group(1)), int(m.group(3))
                if not is_raw(fn["ty"].get(base)):
                    acct["ref-from-deref-of-a-reference (not counted by full_deref)"] += 1
                    continue
                acct["ref-from-raw-deref statements"] += 1
                # forward: reborrow / copy / move chain to a Call argument
                frontier, seen, hits = [dst], set(), []
                while frontier:
                    x = frontier.pop()
                    if x in seen:
                        continue
                    seen.add(x)
                    for (bb2, i2, s2) in uses:
                        t = s2["text"]
                        mc = re.match(r"(?:_(\d+) = )?(.+?)\((.*)\) -> ", t)
                        if mc:
                            args = split_top(mc.group(3))
                            for ai, a in enumerate(args):
                                if re.fullmatch(r"(move|copy) _%d" % x, a):
                                    hits.append((ai, s2, bb2))
                            continue
                        md = re.match(r"_(\d+) = (?:&(?:mut )?\(\*_%d\)|(?:move|copy) _%d)(?: as [^;]*)?;?$" % (x, x), t)
                        if md and is_ref(fn["ty"].get(int(md.group(1)))):
                            frontier.append(int(md.group(1)))
                if not hits:
                    unused.append((fname, bb, st["text"], st["span"]))
                    continue
                # root of the deref base
                root_kind, root_name, via = root_of(fn, defs, base)
                for (ai, cst, cbb) in hits:
                    formals, cpath = fn_sig_args(cst["const"] or "")
                    callee = resolve_callee(cpath) if cpath != "?" else None
                    fty = formals[ai] if formals and ai < len(formals) else "?"
                    if callee is None:
                        nonlocal_calls[(cpath, fty.split(" ")[0][:2])] += 1
                        acct["-> library/unresolved callee"] += 1
                        continue
                    if not is_ref(fty):
                        acct["-> local callee, non-reference formal"] += 1
                        continue
                    acct["-> local callee, reference formal (BRIDGE)"] += 1
                    if root_kind == "call-result":
                        ct = call_text(fn, defs, base)
                        recv = re.sub(r"\.as_mut_ptr\(\)$", "", ct).strip("()")
                        recv = re.sub(r"\[.*$", "[..]", recv)
                        rk = "local-array" if recv in fn["name"].values() else "static"
                        root_name = "%s:%s" % (rk, recv)
                        via = via + " of " + ct
                    rows.append(dict(caller=fname, root_kind=root_kind, root=root_name, via=via, base_local="_%d" % base,
                                     callee=callee, arg=ai, formal_ty=fty, bb=bb, stmt=st["text"], span=st["span"],
                                     full_deref=fd.get((fname, bb[2:], st["text"]), 0),
                                     official=off.get((fname, st["span"], st["text"]), 0)))

    # census join per row
    for r in rows:
        r.update(census="-", reason_class="not-a-census-subject", delivery="-", holds="-", entry="-", pairs="-", sve=0)
        if r["root_kind"] in ("formal", "local"):
            c = subj.get((r["caller"], r["root"]))
            if c is None:
                r["reason_class"] = "named-local-not-a-subject" if r["root_kind"] == "local" else "formal-not-a-subject"
                continue
            o = outc.get(c["subject_key"], {})
            ix = sidx.get(c["subject_key"], {})
            cls = c["reason"] if c["decision"] == "degraded" else ("excluded:" + c["exclusion"] if c["decision"] == "excluded" else "decided-" + c["decision"])
            r["reason_class"] = cls
            r["delivery"] = o.get("delivery", "-")
            r["census"] = "%s|decision=%s|reason=%s|detail=%s|class_block=%s|node_block=%s" % (
                c["subject_key"], c["decision"], c["reason"], c["reason_detail"][:160], ix.get("class_block", "-"), ix.get("node_block", "-"))
            r["holds"] = ";".join(sorted(set(held.get(c["subject_key"], [])))) or "-"
            r["sve"] = sva.get(c["subject_key"], 0)
            r["entry"] = entry.get((r["caller"], r["root"]), ewin.get((r["caller"], r["root"]), "-"))
            pr = pairs_by.get((r["caller"], r["root"]), [])
            if pr:
                cnt = collections.Counter()
                for p in pr:
                    cnt[p["reason"]] += 1
                    if "static-vs-entry" in p["peer_receipts"]:
                        cnt["static-vs-entry-receipt"] += 1
                r["pairs"] = ";".join("%s=%d" % kv for kv in sorted(cnt.items()))
    print(dict(acct))
    return rows, nonlocal_calls, unused, ppre


OURS = "scratch/main/batch60sp/emitted-trees/libzahl/lib.rs"
_ours = None


def call_text(fn, defs, l):
    """the source text of the call defining l (ours tree), e.g. 'libzahl_tmp_divmod_b.as_mut_ptr()'."""
    global _ours
    if _ours is None:
        _ours = open(OURS).read().splitlines()
    sp = defs[l][0][1]["span"]
    m = re.search(r":(\d+):(\d+): (\d+):(\d+)$", sp)
    l1, c1, l2, c2 = map(int, m.groups())
    if l1 != l2:
        return "?"
    return _ours[l1 - 1][c1 - 1:c2 - 1]


def root_of(fn, defs, l, depth=0):
    """(kind, name, via) of local l."""
    if 1 <= l <= fn["argc"]:
        return "formal", fn["name"].get(l, "_%d" % l), ""
    if l in fn["name"]:
        return "local", fn["name"][l], ""
    d = defs.get(l, [])
    if not d:
        return "temp-undefined", "_%d" % l, ""
    if len(d) > 1:
        return "temp-multi-def", "_%d" % l, ""
    rv = d[0][0]
    if depth > 8:
        return "temp", "_%d" % l, rv
    m = re.fullmatch(r"(?:copy|move) _(\d+)(?: as .*)?", rv)
    if m:
        k, n, v = root_of(fn, defs, int(m.group(1)), depth + 1)
        return k, n, ("cast:" if " as " in rv else "") + v
    m = re.fullmatch(r"(?:copy|move) \(+\*?_(\d+)\)?\.(\d+): ([^)]*)\)(?: as .*)?", rv)
    m = m or re.fullmatch(r"(?:copy|move) \(\(\*_(\d+)\)\.(\d+): (.*)\)(?: as .*)?", rv)
    if m:
        k, n, v = root_of(fn, defs, int(m.group(1)), depth + 1)
        return "field", "%s.%s" % (n, m.group(2)), "field-load-of-%s:%s" % (k, n)
    if "->" in rv:
        mc = re.match(r"(.+?)\(", rv)
        return "call-result", "_%d" % l, (mc.group(1) if mc else rv)[:80]
    if rv.startswith("&raw"):
        return "raw-address", "_%d" % l, rv[:80]
    return "temp-other", "_%d" % l, rv[:80]


if __name__ == "__main__":
    rows, nonlocal_calls, unused, ppre = main()
    cols = ["caller", "root_kind", "root", "via", "callee", "arg", "formal_ty", "reason_class", "delivery", "holds",
            "entry", "sve", "pairs", "census", "full_deref", "official", "bb", "stmt", "span"]
    with open(os.path.join(OUT, "a3-sites.tsv"), "w") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(cols)
        for r in sorted(rows, key=lambda r: (r["caller"], r["span"])):
            w.writerow([r[c] for c in cols])
    g = collections.OrderedDict()
    for r in sorted(rows, key=lambda r: (r["caller"], r["root"], r["callee"])):
        k = (r["caller"], r["root_kind"], r["root"], r["via"], r["callee"])
        e = g.setdefault(k, dict(bridges=0, fd=0, off=0, r=r))
        e["bridges"] += 1; e["fd"] += r["full_deref"]; e["off"] += r["official"]
    with open(os.path.join(OUT, "a3-callers.tsv"), "w") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(["caller", "operand_root_kind", "operand_root", "via", "callee", "bridges", "full_deref", "official",
                    "reason_class", "delivery", "settled_holds", "exported_entry", "static_vs_entry_waived", "pairs_at_caller", "census_row"])
        for (c, k, n, v, ce), e in g.items():
            r = e["r"]
            w.writerow([c, k, n, v or "-", ce, e["bridges"], e["fd"], e["off"], r["reason_class"], r["delivery"],
                        r["holds"], r["entry"], r["sve"], r["pairs"], r["census"]])
    print("bridges", len(rows), "groups", len(g), "callers", len({r["caller"] for r in rows}))
    print("ref temps from raw deref not reaching a call:", len(unused))
    print("non-local / unresolved callees:", sum(nonlocal_calls.values()), nonlocal_calls.most_common(12))
    print("pair-premise rows:", len(ppre))
    print(collections.Counter(r["root_kind"] for r in rows))
    print(collections.Counter(r["reason_class"] for r in rows).most_common())
