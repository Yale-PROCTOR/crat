#!/usr/bin/env python3
"""b.py -- analysis-fanout relay 148, task B: the two-step attribution, measured.
  STEP P = preprocessing: input (rs-crown) -> substrate (the rewriter's exact input)
  STEP W = rewriter:      substrate        -> ours (batch60sp emitted tree, head 32d966b9f)
on T2 (full_deref) and on the official unit, for libzahl, json.h, urlparser.  Read-only outside this directory.
usage: python3 -B b.py            (prints totals)
       python3 -B b.py --write    (writes b-sites.tsv, b-per-function.tsv, b-corrections.tsv here)"""
import collections, csv, os, re, sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bcore as B  # noqa: E402

R = B.R
CEN = "scratch/main/batch60sp/%s.raw-boundary-%s.tsv"
UNITS = ("T2", "official")
MEASURED = {  # the relay's measured totals: unit -> prog -> (input, substrate, ours)
    "T2": {"libzahl": (1015, 1015, 1094), "json.h": (1098, 1116, 1066), "urlparser": (73, 62, 53)},
    "official": {"libzahl": (279, 294, 375), "json.h": (646, 668, 654), "urlparser": (40, 40, 41)},
}


# ---------------------------------------------------------------- site kind and refined within-key pairing
def kind(r):
    st, pl = r["stmt"], r["place"]
    if st.startswith("PlaceMention("):
        return "mention"
    if st.startswith(pl + " = "):
        return "write"
    if re.search(r"&(mut |raw (const|mut) )?" + re.escape(pl), st):
        return "borrow"
    if ("copy " + pl) in st or ("move " + pl) in st:
        return "read"
    return "other"


def stext(r):
    return re.sub(r"\s+", "", B.span_text(r["span"]))


def match(a, b):
    """B.match's multiset rule (same counts), but within one (function, key) the rows paired first by (kind, span
    text), then by kind, then in order -- so the site rows reported as added / removed are the dissimilar ones."""
    by = collections.defaultdict(lambda: (collections.defaultdict(list), collections.defaultdict(list)))
    for r in a:
        r["kind"] = kind(r)
        by[r["function"]][0][r["key"]].append(r)
    for r in b:
        r["kind"] = kind(r)
        by[r["function"]][1][r["key"]].append(r)
    added, removed, matched = [], [], 0
    for fn, (X, Y) in by.items():
        for key in set(X) | set(Y):
            xs, ys = list(X.get(key, [])), list(Y.get(key, []))
            for f in (lambda r: (r["kind"], stext(r)), lambda r: r["kind"], lambda r: 0):
                pool = collections.defaultdict(list)
                for r in ys:
                    pool[f(r)].append(r)
                keep = []
                for r in xs:
                    if pool.get(f(r)):
                        y = pool[f(r)].pop(0)
                        ys.remove(y)
                        matched += 1
                    else:
                        keep.append(r)
                xs = keep
            removed += xs
            added += ys
    return matched, added, removed


def full_text(root, proj):
    return proj.replace("R", "\x00", 1).replace("\x00", root) if "R" in proj else proj


# ---------------------------------------------------------------- STEP P: the preprocessing rules
class PInfo:
    """per (prog, fn, unit): the input's let-ref bindings and fresh-pointer locals, the substrate's partners."""

    def __init__(self, prog, fn, unit):
        Fi = B.getfn("input", prog, fn, unit)
        Fs = B.getfn("substrate", prog, fn, unit)
        self.letref = []      # (full text of P, mode, name)
        self.fresh = {}       # fresh-pointer local name -> partner root name (substrate `let freshN = *p`)
        if Fi is None:
            return
        for l, n in Fi.debug.items():
            if not re.fullmatch(r"fresh\d+", n):
                continue
            ty = Fi.decl.get(l, "")
            if ty.startswith("&"):
                for rhs, span, _, _ in Fi.defs.get(l, []):
                    m = re.match(r"^&(?:mut )?(.*)$", rhs.rstrip(";"))
                    if not m:
                        continue
                    P = m.group(1)
                    mr = B.LOC.search(P)
                    if not mr:
                        continue
                    full = full_text(Fi.norm(int(mr.group(1))), Fi.norm_place(P))
                    rd = wr = 0
                    for bb, cl, st, sp in Fi.blocks:
                        if st.startswith("(*_%d) = " % l):
                            wr += 1
                        if re.search(r"(copy|move) \(\*_%d\)" % l, st) or (st.startswith("(*_%d) = " % l) and
                                                                           ("(*_%d)" % l) in st[len("(*_%d) = " % l):]):
                            rd += 1
                    mode = "rmw" if rd and wr else ("store" if wr else ("read" if rd else "pass"))
                    self.letref.append((full, mode, n))
            elif ty.startswith(("*mut ", "*const ")) and Fs is not None:
                sl = [x for x, nn in Fs.debug.items() if nn == n]
                if sl and not Fs.decl.get(sl[0], "").startswith(("*mut ", "*const ")):
                    partner = "?"
                    for rhs, _, _, _ in Fs.defs.get(sl[0], []):
                        mm = re.match(r"^(?:copy |move )?\(\*_(\d+)\)", rhs)
                        if mm:
                            partner = Fs.norm(Fs.base_local(int(mm.group(1))))
                    self.fresh[n] = partner


_pinfo = {}


def pinfo(prog, fn, unit):
    k = (prog, fn, unit)
    if k not in _pinfo:
        _pinfo[k] = PInfo(prog, fn, unit)
    return _pinfo[k]


def p_rule(prog, unit, r, change):
    PI = pinfo(prog, r["function"], unit)
    full = full_text(r["root"], r["proj"])
    if "offset({offset(" in r["key"] or (change == "added" and re.search(r"offset\(\{[^{}]*\}, \{\(\{AddWithOverflow", r["key"])):
        return "offset-merge", "`p.offset(a).offset(b)` -> `p.offset((a) + (b))` (the preprocessor's \"Merge multiple pointer offsets\")"
    if "__idx_" in r["key"]:
        modes = sorted(set(m for f, m, n in PI.letref if "offset" in f or "[" in f))
        return "letref-%s+index-hoist" % ("/".join(modes) or "?"), \
            "`let ref mut freshN = *X.offset(e); *freshN op= v` -> `*X.offset(e) op= v` (\"Remove let ref\"), then e reads " \
            "the same pointer so `{ let __idx_0 = e; *X.offset(__idx_0) op= v }` (\"Hoist self-referential indexing\")"
    if r["root"] in PI.fresh:
        return "fresh-pointer", "input `%s` raw (`let %s = p; p = p.offset(1); *%s`) -> substrate `let %s = *%s` value" % (
            r["root"], r["root"], r["root"], r["root"], PI.fresh[r["root"]])
    if change == "added" and r["root"] in set(PI.fresh.values()):
        fs = [n for n, p in PI.fresh.items() if p == r["root"]]
        return "fresh-pointer", "the access through %s now on `*%s` (substrate `*%s = v; let freshN = *%s`)" % (
            ",".join(fs[:3]), r["root"], r["root"], r["root"])
    hits = [(f, m, n) for f, m, n in PI.letref if full == f or full in f]
    if hits:
        f, m, n = min(hits, key=lambda h: len(h[0]))
        where = "the bound place itself" if full == f else "inside the bound place's computation"
        return "letref-%s" % m, "`let ref mut %s = %s` inlined at every use (%s)" % (n, f[:80], where)
    return "other", "no let-ref / fresh-pointer binding covers this key"


# ---------------------------------------------------------------- STEP W: constructs and causes
def split_args(s):
    out, d, cur = [], 0, ""
    for c in s:
        if c in "([<{":
            d += 1
        elif c in ")]>}":
            d -= 1
        if c == "," and d == 0:
            out.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur)
    return out


def callee_of(st):
    m = re.match(r"^(?:_\d+ = )?([\w:<>\[\] ,&*]+?)\((.*)\) -> ", st)
    return (m.group(1), m.group(2)) if m else (None, None)


def consumer(F, local, seen=None, hops=0):
    seen = seen or set()
    if local in seen or hops > 6:
        return ("other", "", "cycle")
    seen.add(local)
    if local in F.debug and hops > 0:
        return ("decl", "", F.debug[local])
    for st, bb, idx in F.uses.get(local, []):
        md = re.match(r"^_(\d+) = (.*)$", st)
        rhs = md.group(2) if md else st
        if " -> " in rhs and "(" in rhs:
            cp, args = callee_of(st)
            if cp:
                toks = [x.strip() for x in split_args(args)]
                pos = next((i for i, x in enumerate(toks) if re.search(r"(?<![\w])_%d\b" % local, x)), None)
                return ("call", st, (cp, pos))
        if md:
            dst = int(md.group(1))
            if re.search(r"\bSome\(", rhs) or ("Option" in rhs and "Some" in rhs):
                return ("option", st, F.debug.get(dst, "_%d" % dst))
            if re.match(r"^&(mut |raw (mut|const) )?\(\*_%d\)" % local, rhs) or re.match(r"^(move |copy )?_%d( as .*)?$" % local, rhs):
                if dst in F.debug:
                    return ("decl", st, F.debug[dst])
                return consumer(F, dst, seen, hops + 1)
            if dst in F.debug:
                return ("decl", st, F.debug[dst])
            return ("other", st, "assign")
        return ("other", st, "use")
    return ("other", "", "no-use")


def resolve_callee(prog, caller_fn, cpath):
    last = cpath.split("::")[-1]
    mod = caller_fn.rsplit("::", 1)[0]
    for c in (cpath, "src::" + cpath, mod + "::" + last, "src::%s::%s" % (cpath.split("::")[0], last)):
        if os.path.exists(B.dump_path("ours", prog, c, "T2")):
            return c
    return cpath


def formal_ty(side, prog, fn, pos):
    F = B.getfn(side, prog, fn, "T2")
    return F.decl.get(pos + 1, "?") if (F is not None and pos is not None) else "?"


_subj = {}


def subjects(prog):
    if prog not in _subj:
        out = collections.defaultdict(list)
        sout = {r["subject_key"]: r for r in csv.DictReader(open(CEN % (prog, "subject-outcomes")), delimiter="\t")}
        for r in csv.DictReader(open(CEN % (prog, "subjects")), delimiter="\t"):
            k, o = r["subject_key"], r["owner_fn"]
            name = k[len(o) + 2:k.rindex("#")] if k.startswith(o + "::") and "#" in k else "?"
            out[(o, name)].append((r, sout.get(k, {})))
        _subj[prog] = out
    return _subj[prog]


def subject_of(prog, fn, name, depth_hint=None):
    rows = subjects(prog).get((fn, name), [])
    if not rows:
        return "-", "not a census subject"
    rows = sorted(rows, key=lambda x: x[0]["ptr_depth"])
    r, o = rows[0]
    st = "%s/%s/%s" % (o.get("family", r["family"]), o.get("delivery", "?"), o.get("emitted_form", "?"))
    if o.get("delivery") != "realized-as-predicted":
        st += " reason=" + (r["reason"] or "-")
    return r["subject_key"], st


def tycat(t):
    t = t.strip()
    if t.startswith(("*mut ", "*const ")):
        return "raw"
    if re.match(r"^(std::|core::)?(option::)?Option<", t):
        return "option"
    if re.match(r"^&('\w+ )?(mut )?\[", t):
        return "slice-ref"
    if t.startswith("&"):
        return "ref"
    if "Box<" in t:
        return "box"
    return "value"


def is_rawtemp(root):
    """(v): a raw temporary made from a local / static: `x.as_mut_ptr()`, `&mut x as *mut T`, `&raw mut x`."""
    return root.startswith("{") and re.search(r"as_mut_ptr\(|as_ptr\(|&raw (mut|const) [A-Za-z_(]|\{&mut [A-Za-z_][\w]*\} as \(", root) is not None


def w_added(prog, unit, r):
    """construct of a site the rewriter added (an `ours` row)."""
    F = B.getfn("ours", prog, r["function"], unit)
    st = r["stmt"].rstrip(";")
    md = re.match(r"^_(\d+) = &(mut )?\(\*.*\)$", st)
    mr = re.match(r"^_(\d+) = &raw (mut|const) \(\*_\d+\)$", st)
    if mr:
        F0 = F
        kind_, cst, det = consumer(F0, int(mr.group(1)))
        if kind_ == "call":
            cp, pos = det
            callee = resolve_callee(prog, r["function"], cp)
            fo = formal_ty("ours", prog, callee, pos)
            return "vi", callee, "ref->raw coercion: the delivered reference %s passed to raw formal %s(arg%s): %s" % (
                F.norm(int(r["local"][1:])), callee.split("::")[-1], pos, fo), *subject_of(prog, r["function"], F.norm(int(r["local"][1:])))
        return "vi", "-", "`&raw (*%s)` consumed by %s" % (F.norm(int(r["local"][1:])), det), "-", "-"
    base = F.base_local(int(r["local"][1:]))
    bname = F.norm(base) if (base in F.debug or 1 <= base <= F.nargs) else "-"
    skey, sst = subject_of(prog, r["function"], bname) if bname != "-" else ("-", "-")
    if md:
        kind_, cst, det = consumer(F, int(md.group(1)))
        if kind_ == "call":
            cp, pos = det
            callee = resolve_callee(prog, r["function"], cp)
            fi, fo = formal_ty("substrate", prog, callee, pos), formal_ty("ours", prog, callee, pos)
            d = "%s(arg%s): formal %s -> %s" % (callee.split("::")[-1], pos, fi, fo)
            if not os.path.exists(B.dump_path("ours", prog, callee, "T2")) or not fo.startswith("&"):
                rt = F.decl.get(base, "?")
                what = {"as_ptr": "`.as_ptr()` on the delivered slice (autoref `&*%s`) into a foreign raw formal" % bname,
                        "as_mut_ptr": "`.as_mut_ptr()` on the delivered slice (autoref `&mut *%s`)" % bname,
                        "from_mut": "`core::ptr::from_mut(&mut *%s)`: the delivered reference made raw again (pointer comparison)" % bname,
                        "from_ref": "`core::ptr::from_ref(&*%s)`: the delivered reference made raw again" % bname}
                key = re.sub(r"::<[^<>]*(<[^<>]*>)*[^<>]*>$", "", cp).split("::")[-1]
                return "vi", cp, "reborrow into library call %s: %s; root %s : %s" % (
                    key, what.get(key, "not a crate function with a reference formal"), bname, rt), skey, sst
            if is_rawtemp(r["root"]):
                c = "v-static" if "static(" in r["root"] else "v-local"
                return c, callee, d + "; operand a raw temporary " + r["root"][:90], skey, sst
            if r["root"].startswith("{"):
                op = "operand a raw place reached through a temporary: %s (named base %s)" % (r["root"][:90], bname)
            else:
                op = "operand root %s" % bname
            return "i", callee, d + "; " + op, skey, sst
        if kind_ == "decl":
            c = "iii" if "pair" in sst else "ii"
            return c, "-", "view `%s` declared from `&*%s`" % (det, bname), skey, sst
        if kind_ == "option":
            return "iv", "-", "`Some(&*%s)` into %s" % (bname, det), skey, sst
        return "vi", "-", "reborrow consumed by %s (%s)" % (det, cst[:80]), skey, sst
    return "vi", "-", "not a reborrow: %s on root %s (%s)" % (r["kind"], bname, st[:80]), skey, sst


def w_removed(prog, unit, r):
    """cause of a site the rewriter removed (a `substrate` row)."""
    Fs = B.getfn("substrate", prog, r["function"], unit)
    Fo = B.getfn("ours", prog, r["function"], unit)
    base = Fs.base_local(int(r["local"][1:]))
    named = base in Fs.debug or 1 <= base <= Fs.nargs
    name = Fs.norm(base) if named else "-"
    if not named:
        return "other", "root a temporary with no named base: %s" % r["root"][:90], "-", "-"
    skey, sst = subject_of(prog, r["function"], name)
    if Fo is None:
        return "other", "function absent from ours", skey, sst
    if name.startswith("arg"):
        oty = Fo.decl.get(base, "?")
    else:
        tys = Fo.ty_of_name(name)
        oty = tys[0] if tys else "?"
    ity = Fs.decl.get(base, "?")
    c = tycat(oty)
    if c == "option" and re.search(r"Option<&", oty):
        # the access in ours goes through an Option accessor temporary (`.as_mut().unwrap()` / `.unwrap()`)
        acc = any(re.search(r"\b(as_mut|as_ref|unwrap)\(", d) for ds in Fo.defs.values() for d, *_ in ds)
        return "option-accessor", "%s: %s -> %s; access through `.as_mut().unwrap()` / `.unwrap()` temporaries%s" % (
            name, ity, oty, "" if acc else " (no accessor found)"), skey, sst
    if c in ("ref", "slice-ref", "box", "option") or "SliceCursor" in oty:
        return "made-safe", "%s: %s -> %s" % (name, ity, oty), skey, sst
    if c == "raw":
        return "other", "%s still raw in ours (%s); the access itself is gone or reshaped" % (name, oty), skey, sst
    return "made-safe" if c == "value" and "fresh" not in name else "other", "%s: %s -> %s" % (name, ity, oty), skey, sst


# ---------------------------------------------------------------- driver
def run():
    rows = []           # b-sites rows
    perfn = {}          # (prog, fn) -> dict
    totals = {}
    for prog in B.PROGS:
        for unit in UNITS:
            S = {s: B.load_sites(s, prog, unit) for s in B.SIDES}
            got = tuple(len(S[s]) for s in B.SIDES)
            assert got == MEASURED[unit][prog], (prog, unit, got)
            cnt = {s: collections.Counter(r["function"] for r in S[s]) for s in B.SIDES}
            for step, a, b in (("P", "input", "substrate"), ("W", "substrate", "ours")):
                m, ad, rm = match(S[a], S[b])
                totals[(prog, unit, step)] = (len(S[a]), len(S[b]), m, len(ad), len(rm))
                for r in ad + rm:
                    change = "added" if r in ad else "removed"
                    callee = skey = sst = "-"
                    if step == "P":
                        cc, det = p_rule(prog, unit, r, change)
                    elif change == "added":
                        cc, callee, det, skey, sst = w_added(prog, unit, r)
                    else:
                        cc, det, skey, sst = w_removed(prog, unit, r)
                    rows.append(dict(program=prog, unit=unit, step=step, change=change, function=r["function"],
                                     construct_cause_rule=cc, callee=callee, detail=det, root=r["root"][:140], proj=r["proj"],
                                     subject=skey, subject_status=sst, kind=r["kind"], side=r["side"],
                                     span=r["span"].split("/")[-1], src=B.span_text(r["span"])[:100], stmt=r["stmt"]))
            for fn in set(cnt["input"]) | set(cnt["substrate"]) | set(cnt["ours"]):
                d = perfn.setdefault((prog, fn), {"program": prog, "function": fn})
                for s in B.SIDES:
                    d["%s_%s" % (unit, s)] = cnt[s][fn]
    return rows, perfn, totals


def per_function(rows, perfn):
    W_ADD = ("i", "ii", "iii", "iv", "v-local", "v-static", "vi")
    W_REM = ("made-safe", "option-accessor", "other")
    out = []
    agg = collections.defaultdict(collections.Counter)
    for r in rows:
        agg[(r["program"], r["function"])]["%s_%s_%s_%s" % (r["unit"], r["step"], r["change"], r["construct_cause_rule"])] += 1
        agg[(r["program"], r["function"])]["%s_%s_%s" % (r["unit"], r["step"], r["change"])] += 1
        if r["step"] == "W" and r["change"] == "added" and r["construct_cause_rule"] in ("i", "v-local", "v-static"):
            agg[(r["program"], r["function"])]["callee:" + r["unit"] + ":" + r["callee"].split("::")[-1]] += 1
    for (prog, fn), d in sorted(perfn.items()):
        a = agg[(prog, fn)]
        row = dict(d)
        for u in UNITS:
            for s in B.SIDES:
                row.setdefault("%s_%s" % (u, s), 0)
            row["%s_P_net" % u] = row["%s_substrate" % u] - row["%s_input" % u]
            row["%s_W_net" % u] = row["%s_ours" % u] - row["%s_substrate" % u]
            row["%s_P_added" % u], row["%s_P_removed" % u] = a["%s_P_added" % u], a["%s_P_removed" % u]
            row["%s_W_added" % u], row["%s_W_removed" % u] = a["%s_W_added" % u], a["%s_W_removed" % u]
            pr = collections.Counter()
            for k, v in a.items():
                mk = re.match(r"^%s_P_(added|removed)_(.+)$" % u, k)
                if mk:
                    pr[mk.group(2)] += v if mk.group(1) == "added" else -v
            row["%s_P_by_rule" % u] = ";".join("%s:%+d" % kv for kv in sorted(pr.items()) if kv[1]) or "-"
            for c in W_ADD:
                row["%s_W_add_%s" % (u, c)] = a["%s_W_added_%s" % (u, c)]
            for c in W_REM:
                row["%s_W_rem_%s" % (u, c)] = a["%s_W_removed_%s" % (u, c)]
            row["%s_W_bridges_by_callee" % u] = ",".join("%s:%d" % (k.split(":", 2)[2], v) for k, v in sorted(a.items())
                                                          if k.startswith("callee:%s:" % u)) or "-"
            ok = (row["%s_P_added" % u] - row["%s_P_removed" % u] == row["%s_P_net" % u]
                  and row["%s_W_added" % u] - row["%s_W_removed" % u] == row["%s_W_net" % u])
            row["%s_check" % u] = "ok" if ok else "MISMATCH"
        if not any(row["%s_%s" % (u, x)] for u in UNITS for x in ("P_added", "P_removed", "W_added", "W_removed")):
            continue
        out.append(row)
    return out


PF_COLS = ["program", "function",
           "T2_input", "T2_substrate", "T2_ours", "T2_P_net", "T2_P_added", "T2_P_removed", "T2_P_by_rule",
           "T2_W_net", "T2_W_added", "T2_W_removed",
           "T2_W_add_i", "T2_W_add_ii", "T2_W_add_iii", "T2_W_add_iv", "T2_W_add_v-local", "T2_W_add_v-static", "T2_W_add_vi",
           "T2_W_rem_made-safe", "T2_W_rem_option-accessor", "T2_W_rem_other", "T2_W_bridges_by_callee", "T2_check",
           "official_input", "official_substrate", "official_ours", "official_P_net", "official_P_added", "official_P_removed",
           "official_P_by_rule", "official_W_net", "official_W_added", "official_W_removed",
           "official_W_add_i", "official_W_add_ii", "official_W_add_iii", "official_W_add_iv", "official_W_add_v-local",
           "official_W_add_v-static", "official_W_add_vi",
           "official_W_rem_made-safe", "official_W_rem_option-accessor", "official_W_rem_other", "official_W_bridges_by_callee",
           "official_check"]
SITE_COLS = ["program", "unit", "step", "change", "function", "construct_cause_rule", "callee", "detail", "subject",
             "subject_status", "root", "proj", "kind", "side", "span", "src", "stmt"]


def write_tsv(path, cols, rows):
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", lineterminator="\n", extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def main():
    rows, perfn, totals = run()
    pf = per_function(rows, perfn)
    for (prog, unit, step), (na, nb, m, a, rm) in sorted(totals.items()):
        print("%-9s %-8s %s %5d -> %5d matched %5d added %4d removed %4d net %+d" % (prog, unit, step, na, nb, m, a, rm, a - rm))
    c = collections.Counter((r["program"], r["unit"], r["step"], r["change"], r["construct_cause_rule"]) for r in rows)
    for k in sorted(c):
        print("  ", k, c[k])
    bad = [r for r in pf if r["T2_check"] != "ok" or r["official_check"] != "ok"]
    print("per-function rows", len(pf), "mismatch", len(bad))
    if "--write" in sys.argv:
        rows.sort(key=lambda r: (r["program"], r["unit"], r["step"], r["function"], r["change"], r["construct_cause_rule"], r["span"]))
        write_tsv(os.path.join(HERE, "b-sites.tsv"), SITE_COLS, rows)
        write_tsv(os.path.join(HERE, "b-per-function.tsv"), PF_COLS, pf)
    return rows, pf, totals


if __name__ == "__main__":
    main()
