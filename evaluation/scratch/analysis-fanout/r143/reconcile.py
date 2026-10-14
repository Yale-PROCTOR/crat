"""relay 143: reconcile &inator's positions with the c2rust translation's (the same C declarations)."""
import json, os, sys, collections, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import positions as P
W = "scratch/analysis-fanout/r143"
C = "scratch/analysis-fanout/rq3/c2rust-out"
inj = json.load(open(W + "/inator-positions.json"))
PROGS = ["running-example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]
allrows = []
summary = {}
for p in PROGS:
    inr = inj["out"][p]["rows"]
    cr = P.c2rust_rows(f"{C}/{p}")
    def ikey(r):
        o = re.sub(r"^(struct|union)\.", "", r["owner"])
        return (r["kind"], o, r["index"])
    # tisp: anonymous aggregates, matched by layout (stypes field list vs c2rust field list, index for index)
    ANON = {"tisp": {"C2RustUnnamed_11": "anon", "C2RustUnnamed_15": "anon.0", "C2RustUnnamed_14": "anon.1",
                     "C2RustUnnamed_13": "anon.2", "C2RustUnnamed_12": "anon.3"}}.get(p, {})
    # glibc's siginfo_t / sigaction / sigval internals (fields __pid_t, __uid_t, __sigval_t, __sighandler_t): header aggregates
    LIBC_ANON = {"tisp": {"C2RustUnnamed", "sigval"} | {"C2RustUnnamed_%d" % n for n in range(0, 11)}}.get(p, set())
    excluded_anon = sorted({r["owner"] for r in cr if r["kind"] == "field" and r["owner"] in LIBC_ANON and r["owner"] not in ANON})
    cr = [r for r in cr if not (r["kind"] == "field" and r["owner"] in LIBC_ANON and r["owner"] not in ANON)]
    for r in cr:
        if r["kind"] == "field" and r["owner"] in ANON:
            r["owner"] = ANON[r["owner"]]
    structs_c = {r["owner"] for r in cr if r["kind"] == "field"}
    def cname(o):   # c2rust appends _0 to a struct name that collides with a typedef of the same name
        return o[:-2] if o.endswith("_0") and o[:-2] not in structs_c else o
    def ckey(r):
        o = "main" if r["owner"] == "main_0" else r["owner"]
        if r["kind"] == "field":
            o = cname(o)
        return (r["kind"], o, r["index"])
    I = {ikey(r): r for r in inr if not (r["kind"] == "field" and re.sub(r"^(struct|union)\.", "", r["owner"]).startswith("__"))}
    LIBC = re.compile(r"^(_IO_|__)")   # libc header structs (stdio's FILE and friends): not defined in the program
    excluded_libc = sorted({r["owner"] for r in cr if r["kind"] == "field" and LIBC.match(r["owner"])})
    cr = [r for r in cr if not (r["kind"] == "field" and LIBC.match(r["owner"]))]
    Cp = {ckey(r): r for r in cr if r["owner"] != "main"}   # 'pub fn main()' is c2rust's synthetic wrapper
    cptr = {k: r for k, r in Cp.items() if r["ck"] == "pointer"}
    cfn = {k: r for k, r in Cp.items() if r["ck"] == "fnptr"}
    iptr = {k for k, r in I.items() if r["sptr"]}
    both = sorted(set(I) & set(cptr))            # the C declaration is a pointer (c2rust) and &inator has the position
    fnptr_in_inator = sorted(set(I) & set(cfn))
    only_i = sorted(iptr - set(cptr) - set(cfn))  # &inator reads a pointer the c2rust side does not have as one
    only_c = sorted(set(cptr) - set(I))
    for k in both:
        allrows.append({"program": p, "kind": k[0], "owner": k[1], "index": k[2], "name": Cp[k]["name"],
                        "c2rust": Cp[k]["rtype"], "c_owner": Cp[k]["orig_owner"], "c_name": Cp[k]["name"], "inator": I[k]["rtype"], "bucket": I[k]["bucket"],
                        "ghost_inner": I[k]["ghost_inner"], "inator_stype": I[k]["stype"]})
    summary[p] = {"both": len(both), "fnptr": len(cfn), "fnptr_seen_by_inator": len(fnptr_in_inator),
                  "only_inator": [(k, I[k]["rtype"], ("c2rust: " + Cp[k]["ck"] + " " + Cp[k]["rtype"]) if k in Cp else "c2rust: absent") for k in only_i],
                  "only_c2rust": [(k, cptr[k]["rtype"]) for k in only_c],
                  "buckets": dict(collections.Counter(I[k]["bucket"] for k in both)),
                  "inator_source_not_ptr": [(k, I[k]["stype"], I[k]["rtype"]) for k in both if not I[k]["sptr"]], "excluded_libc_structs": excluded_libc + excluded_anon}
    print(p, "both", len(both), "fnptr", len(cfn), "(inator sees", len(fnptr_in_inator), ") only-inator", len(only_i), "only-c2rust", len(only_c), summary[p]["buckets"])
json.dump({"rows": allrows, "summary": summary}, open(W + "/reconcile.json", "w"), indent=1)
