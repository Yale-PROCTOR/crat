#!/usr/bin/env python3
"""b_report.py -- relay 148 task B: tables for README.md and the corrections against A1 / A2 (b-corrections.tsv).
Reads b-sites.tsv / b-per-function.tsv (run `python3 -B b.py --write` first) and out/a1-libzahl, out/a2-official.
usage: python3 -B b_report.py  (prints markdown; writes b-corrections.tsv)"""
import collections, csv, os, sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)
PF = list(csv.DictReader(open(os.path.join(HERE, "b-per-function.tsv")), delimiter="\t"))
SITES = list(csv.DictReader(open(os.path.join(HERE, "b-sites.tsv")), delimiter="\t"))
I = lambda r, k: int(r[k])
ADD = [("i", "i"), ("ii", "ii"), ("iii", "iii"), ("iv", "iv"), ("v-local", "v-loc"), ("v-static", "v-sta"), ("vi", "vi")]
REM = [("made-safe", "safe"), ("option-accessor", "opt"), ("other", "oth")]


def wcell(r, u):
    a = " ".join("%s %d" % (lab, I(r, "%s_W_add_%s" % (u, k))) for k, lab in ADD if I(r, "%s_W_add_%s" % (u, k)))
    d = " ".join("%s %d" % (lab, I(r, "%s_W_rem_%s" % (u, k))) for k, lab in REM if I(r, "%s_W_rem_%s" % (u, k)))
    return "%+d (+%s / −%s)" % (I(r, u + "_W_net"), a or "0", d or "0")


PRULE = collections.defaultdict(collections.Counter)
for _s in SITES:
    if _s["step"] == "P":
        PRULE[(_s["program"], _s["function"], _s["unit"])][(_s["construct_cause_rule"], _s["change"])] += 1


def pcell(r, u):
    n = I(r, u + "_P_net")
    c = PRULE[(r["program"], r["function"], u)]
    if not c:
        return "%+d" % n
    rules = sorted(set(k for k, _ in c))
    parts = []
    for k in rules:
        a, d = c[(k, "added")], c[(k, "removed")]
        parts.append("%s %s" % (k, "/".join(x for x in (("+%d" % a) if a else "", ("−%d" % d) if d else "") if x)))
    return "%+d (%s)" % (n, ", ".join(parts))


def table(prog):
    rows = [r for r in PF if r["program"] == prog]
    groups = collections.OrderedDict()
    for r in rows:
        name = r["function"].split("::")[-1]
        sig = tuple(v for k, v in r.items() if k not in ("program", "function"))
        groups.setdefault((name, sig), []).append(r)
    out = ["| function | T2 in / sub / ours | P net | W net (+added by construct / −removed by cause) | official in / sub / ours | off. P | off. W |",
           "|---|---|---|---|---|---|---|"]
    items = sorted(groups.items(), key=lambda kv: (-abs(I(kv[1][0], "T2_ours") - I(kv[1][0], "T2_input")) * len(kv[1]), kv[0][0]))
    for (name, _), rs in items:
        r = rs[0]
        lab = name if len(rs) == 1 else "%s ×%d copies" % (name, len(rs))
        if len(rs) == 1 and sum(1 for x in rows if x["function"].split("::")[-1] == name) > 1:
            lab = r["function"].split("::", 1)[1].replace("::", "::")
        out.append("| %s | %d / %d / %d | %s | %s | %d / %d / %d | %s | %s |" % (
            lab, I(r, "T2_input"), I(r, "T2_substrate"), I(r, "T2_ours"), pcell(r, "T2"), wcell(r, "T2"),
            I(r, "official_input"), I(r, "official_substrate"), I(r, "official_ours"), pcell(r, "official"), wcell(r, "official")))
    # totals over every function of the program (not only the changed rows)
    tot = collections.Counter()
    for s in SITES:
        if s["program"] != prog:
            continue
        tot[(s["unit"], s["step"], s["change"], s["construct_cause_rule"])] += 1
    return out, tot


def totals_line(prog, tot, u, meas):
    P = collections.Counter()
    for (uu, st, ch, c), n in tot.items():
        if uu == u and st == "P":
            P[c] += n if ch == "added" else -n
    a = " ".join("%s %d" % (lab, tot[(u, "W", "added", k)]) for k, lab in ADD if tot[(u, "W", "added", k)])
    d = " ".join("%s %d" % (lab, tot[(u, "W", "removed", k)]) for k, lab in REM if tot[(u, "W", "removed", k)])
    pa = sum(n for (uu, st, ch, c), n in tot.items() if uu == u and st == "P" and ch == "added")
    pr = sum(n for (uu, st, ch, c), n in tot.items() if uu == u and st == "P" and ch == "removed")
    wa = sum(n for (uu, st, ch, c), n in tot.items() if uu == u and st == "W" and ch == "added")
    wr = sum(n for (uu, st, ch, c), n in tot.items() if uu == u and st == "W" and ch == "removed")
    return pa, pr, wa, wr, ", ".join("%s %+d" % kv for kv in sorted(P.items()) if kv[1]) or "0", a, d


# ---------------------------------------------------------------- corrections
def corrections():
    meas = {(r["program"], r["function"]): r for r in PF}
    allfn = collections.defaultdict(dict)
    rows = []
    a1 = list(csv.DictReader(open(os.path.join(OUT, "a1-libzahl/a1-per-function.tsv")), delimiter="\t"))
    for r in a1:
        if r["function"] == "TOTAL":
            continue
        m = meas.get(("libzahl", r["function"]))
        mp = I(m, "T2_P_net") if m else 0
        mw = I(m, "T2_W_net") if m else int(r["net"])
        mrem = (I(m, "T2_W_rem_made-safe") + I(m, "T2_W_rem_option-accessor")) if m else 0
        mbr = (I(m, "T2_W_add_i") + I(m, "T2_W_add_v-local") + I(m, "T2_W_add_v-static")) if m else 0
        sub = I(m, "T2_substrate") if m else int(r["full_deref_input"])
        old_p = int(r["added_vi_substrate"]) - int(r["removed_substrate"])
        old_w = int(r["net"]) - old_p
        old_sub = int(r["full_deref_input"]) + old_p
        checks = [("T2 substrate count", old_sub, sub), ("T2 P net (A1: vi − substrate-removed)", old_p, mp),
                  ("T2 W net (A1: rewriter)", old_w, mw), ("T2 W removed made-safe (A1 removed_made_safe)", int(r["removed_made_safe"]), mrem),
                  ("T2 W bridges i+v (A1 i+v)", int(r["added_i_call_bridge"]) + int(r["added_v_raw_temp_bridge"]), mbr)]
        for what, o, n in checks:
            if o != n:
                rows.append(dict(source="A1", program="libzahl", function=r["function"], quantity=what, old=o, new=n))
    a2 = list(csv.DictReader(open(os.path.join(OUT, "a2-official/a2-per-function.tsv")), delimiter="\t"))
    for r in a2:
        m = meas.get((r["program"], r["function"]))
        for u, col in (("official", "official_by_rule"), ("T2", "T2_by_rule")):
            by = collections.Counter()
            if r[col] != "-":
                for kv in r[col].split(";"):
                    k, v = kv.rsplit(":", 1)
                    by[k] += int(v)
            old_p = by["c'-letref-inline"] + by["c'-fresh-pointer"]
            old_w = sum(v for k, v in by.items() if not k.startswith("c'-") and not k.startswith("("))
            new_p = I(m, u + "_P_net") if m else 0
            new_w = I(m, u + "_W_net") if m else 0
            if old_p != new_p:
                rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s P net (A2 substrate, predicted)" % u, old=old_p, new=new_p))
            if old_w != new_w:
                rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s W net (A2 rewriter)" % u, old=old_w, new=new_w))
            # rule-level
            if m:
                pr = collections.Counter()
                if m[u + "_P_by_rule"] != "-":
                    for kv in m[u + "_P_by_rule"].split(";"):
                        k, v = kv.rsplit(":", 1)
                        pr[k] += int(v)
                new_let = sum(v for k, v in pr.items() if k.startswith("letref"))
                if by["c'-letref-inline"] != new_let:
                    rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s let-ref (A2 c'-letref-inline)" % u, old=by["c'-letref-inline"], new=new_let))
                if by["c'-fresh-pointer"] != pr["fresh-pointer"]:
                    rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s fresh-pointer" % u, old=by["c'-fresh-pointer"], new=pr["fresh-pointer"]))
                ob = by["d-bridge"]
                nb = I(m, u + "_W_add_i") + I(m, u + "_W_add_v-local") + I(m, u + "_W_add_v-static") + I(m, u + "_W_add_vi")
                if ob != nb:
                    rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s W added (A2 d-bridge)" % u, old=ob, new=nb))
                os_ = -by["subject-made-safe"] - by["c-option-accessor"]
                ns = I(m, u + "_W_rem_made-safe") + I(m, u + "_W_rem_option-accessor")
                if os_ != ns:
                    rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s W removed (A2 made-safe + option accessor)" % u, old=os_, new=ns))
                if -by["c-option-accessor"] != I(m, u + "_W_rem_option-accessor"):
                    rows.append(dict(source="A2", program=r["program"], function=r["function"], quantity="%s W removed option-accessor (A2 c-option-accessor)" % u, old=-by["c-option-accessor"], new=I(m, u + "_W_rem_option-accessor")))
    with open(os.path.join(HERE, "b-corrections.tsv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["source", "program", "function", "quantity", "old", "new"], delimiter="\t", lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    return rows


def kept_a():
    """official sites in ours whose root (a debug-named local) is no longer raw: still counted (rule (a))."""
    import bcore as B
    out = collections.Counter()
    for prog in B.PROGS:
        for side in ("substrate", "ours"):
            for r in B.load_sites(side, prog, "official"):
                F = B.getfn(side, prog, r["function"], "official")
                t = F.decl.get(int(r["local"][1:]), "?")
                if not t.startswith(("*mut ", "*const ")):
                    out[(prog, side)] += 1
    return out


if __name__ == "__main__":
    print("kept (a):", dict(kept_a()))
    for prog in ("libzahl", "json.h", "urlparser"):
        out, tot = table(prog)
        print("\n### %s\n" % prog)
        print("\n".join(out))
        for u in ("T2", "official"):
            print(u, totals_line(prog, tot, u, None))
    rows = corrections()
    print("\ncorrections", len(rows))
    for r in rows:
        print("  ", r)
