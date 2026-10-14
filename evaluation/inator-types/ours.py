#!/usr/bin/env python3
"""relay 143, our half: for each of the 317 positions (reconcile.json), the EMITTED type in our census's emitted tree
(the safe twin __crat_safe_<f> where the exposure split one off), its bucket (ref / mut / box / raw), the model kind
(the solve's slot rows: <fn>::_0@d0 = return, <fn>::_<k>@d0 = parameter k (MIR local = index + 1), <struct>::field<N>@d0),
and for every raw position the cause from the census's own tables.
usage: ours.py <run-root with prep/<p>/{census-t1, s1-rows-t1.tsv}> <out.tsv>
Fails closed through SystemExit."""
import csv, glob, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import positions as P

csv.field_size_limit(10 ** 9)
W = os.path.dirname(os.path.abspath(__file__))


def die(m):
    raise SystemExit("ours: FAIL: " + m)


def bucket(t):
    t = re.sub(r"\s+", " ", t.strip())
    u = re.sub(r"^Option<\s*", "", t)
    if u.startswith("Box<"):
        return "box"
    if re.match(r"^&\s*('\w+\s+)?mut\b", u):
        return "mut"
    if u.startswith("&"):
        return "ref"
    if re.match(r"^\*(mut|const)\b", u):
        return "raw"
    if re.match(r"^(\w+::)*SliceCursorMut\b", u) or re.match(r"^(\w+::)*\w*CursorMut\b", u):
        return "mut"
    if re.match(r"^(\w+::)*\w*Cursor\b", u):
        return "ref"
    return "other:" + t[:60]


def tsv(path):
    if not os.path.exists(path):
        return []
    return list(csv.DictReader(open(path, encoding="utf-8"), delimiter="\t", quoting=csv.QUOTE_NONE))


def main():
    run, out = sys.argv[1], sys.argv[2]
    rec = json.load(open(W + "/reconcile.json"))["rows"]
    rows_out = []
    for prog in sorted({r["program"] for r in rec}):
        d = f"{run}/prep/{prog}"
        cen = f"{d}/census-t1"
        tree = f"{cen}/emitted-trees/{prog}"
        if not os.path.isdir(tree):
            print("WARNING: no emitted tree for", prog)
            for r in [x for x in rec if x["program"] == prog]:
                rows_out.append({"program": prog, "kind": r["kind"], "owner": r["c_owner"], "index": r["index"], "name": r["c_name"],
                                 "c2rust": r["c2rust"], "emitted": "(no emitted tree)", "twin": "no", "ours": "no-tree",
                                 "model": "-", "raw_cause": "", "inator": r["inator"], "inator_bucket": r["bucket"]})
            continue
        # emitted signatures and fields, by the same parser as the c2rust side (lib.rs and src/)
        os.makedirs(f"{W}/tmpcrate/{prog}/src", exist_ok=True)
        text = ""
        for f in sorted(glob.glob(f"{tree}/**/*.rs", recursive=True)):
            if not f.endswith("build.rs"):
                text += open(f, encoding="utf-8").read() + "\n"
        open(f"{W}/tmpcrate/{prog}/src/all.rs", "w").write(text)
        aliases = {m.group(1): m.group(2).strip() for m in re.finditer(r"^\s*pub type (\w+) = (.*?);$", text, flags=re.M)}
        def resolve(t):
            t = t.strip()
            for _ in range(20):
                core = re.sub(r"^Option<\s*(.*)>$", r"\1", t)
                if t in aliases:
                    t = aliases[t]
                elif core in aliases and core != t:
                    t = "Option<" + aliases[core] + ">"
                else:
                    break
            return t
        em = {}
        for r in P.c2rust_rows(f"{W}/tmpcrate/{prog}"):
            owner = r["owner"]
            twin = owner.startswith("__crat_safe_")
            if twin:
                owner = owner[len("__crat_safe_"):]
            k = (r["kind"], owner, r["index"])
            if twin or k not in em:
                em[k] = dict(r, twin=twin)
        # model kinds
        mk = {}
        for line in open(f"{d}/s1-rows-t1.tsv"):
            key, kind = line.rstrip("\n").split("\t")[:2]
            mk[key.split("::", 2)[-1] if key.count("::") >= 2 else key] = kind
        def model(kind, owner, idx):
            if kind == "field":
                cands = [v for k, v in mk.items() if re.fullmatch(rf"(.*::)?{re.escape(owner)}::field{idx}@d0", k)]
            else:
                loc = 0 if kind == "return" else idx + 1
                cands = [v for k, v in mk.items() if re.fullmatch(rf"(.*::)?{re.escape(owner)}::_{loc}@d0", k)]
            return cands[0] if len(set(cands)) == 1 else ("ambiguous" if cands else "-")
        subj = {}
        for s in tsv(f"{cen}/{prog}.raw-boundary-subjects.tsv"):
            if s.get("arg_index", "-") not in ("-", ""):
                subj.setdefault((s["owner_fn"].split("::")[-1], int(s["arg_index"]) - 1), []).append(s)
        reverts = {r_.get("function", r_.get("identity", "")).split("::")[-1] for r_ in tsv(f"{cen}/{prog}.raw-boundary-final-reverts.tsv")}
        diag_fns = {r_.get("function", "").split("::")[-1] for r_ in tsv(f"{cen}/{prog}.raw-boundary-compiler-diagnostics.tsv")}
        for r in [x for x in rec if x["program"] == prog]:
            k = (r["kind"], r["c_owner"], r["index"])
            e = em.get(k)
            et = e["rtype"] if e else "(absent from the emitted tree)"
            b = bucket(resolve(et)) if e else "absent"
            m = model(r["kind"], r["c_owner"], r["index"])
            cause = ""
            if b == "raw":
                ss = sorted(subj.get((r["c_owner"], r["index"]), []), key=lambda x: x.get("ptr_depth", "")) if r["kind"] == "param" else []
                parts = [f"model {m}"]
                for s in ss:
                    parts.append(f"census (depth {s.get('ptr_depth')}) decision {s['decision']} reason {s['reason']}" + (f" ({s['reason_detail']})" if s.get('reason_detail', '-') not in ('-', '') else "")
                                 + (f" exclusion {s['exclusion']}" if s.get('exclusion', '-') not in ('-', '') else ""))
                if r["c_owner"] in diag_fns or r["c_owner"] in reverts:
                    parts.append("function reverted by the compile check")
                cause = "; ".join(parts)
            rows_out.append({"program": prog, "kind": r["kind"], "owner": r["c_owner"], "index": r["index"], "name": r["c_name"],
                             "c2rust": r["c2rust"], "emitted": et, "twin": "yes" if e and e.get("twin") else "no",
                             "ours": b, "model": m, "raw_cause": cause, "inator": r["inator"], "inator_bucket": r["bucket"]})
    cols = list(rows_out[0].keys())
    with open(out, "w") as f:
        w = csv.DictWriter(f, fieldnames=cols, delimiter="\t", lineterminator="\n")
        w.writeheader()
        for r in rows_out:
            w.writerow(r)
    import collections
    for prog in sorted({r["program"] for r in rows_out}):
        rs = [r for r in rows_out if r["program"] == prog]
        print(prog, len(rs), dict(collections.Counter(r["ours"] for r in rs)), "model", dict(collections.Counter(r["model"] for r in rs)))


if __name__ == "__main__":
    main()
