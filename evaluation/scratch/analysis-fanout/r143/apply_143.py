#!/usr/bin/env python3
"""apply_143.py -- analysis-fanout 119 (relay 143, R1068-1): seed the RQ3 types keys rq3.inator.<p>.types.* and their
totals into a COPY of the record, inserted after rq3.inator.ulidgen.reported-s, all `pending`.
  &inator's half: r143/reconcile.json + inator-positions.json (the kept artifacts, trial 1).
  our half: <ours-positions.tsv> if given (ours.py at the final head), else our keys are written EMPTY.
usage: apply_143.py <out-record> [<ours-positions.tsv> <head> <mode final|fallback> <run-dir>]
Fails closed through SystemExit (no assert)."""
import csv, collections, hashlib, json, os, re, subprocess, sys

W = "scratch/analysis-fanout/r143"
DOCS = "crat/docs"
NAME = {"running-example": "example"}
PROGS = ["running-example", "ulidgen", "leftpad", "amp", "nandc", "rbtree", "carrays", "jccc", "tisp"]
IB = ["ref", "mut", "box", "rc", "cell", "refcell", "ghost", "other"]
OB = ["ref", "mut", "box", "raw"]


def die(m):
    raise SystemExit("apply_143: FAIL: " + m)


def need(c, m):
    if not c:
        die(m)


ROW_RE = re.compile(r"^\| (?P<key>[^|]*?) \| (?P<value>[^|]*?) \| (?P<status>[^|]*?) \| (?P<layer>[^|]*?) "
                    r"\| (?P<unit>[^|]*?) \| (?P<prov>.*) \|$")


def main():
    out = sys.argv[1]
    ours_tsv = sys.argv[2] if len(sys.argv) > 2 else None
    raw = subprocess.run(["git", "-C", DOCS, "show", "origin/main:paper/numbers-of-record.md"], capture_output=True, check=True).stdout
    lines = raw.decode("utf-8").split("\n")
    keys = {}
    for i, l in enumerate(lines):
        m = ROW_RE.match(l)
        if m and m.group("key"):
            keys[m.group("key")] = i
    need("rq3.inator.ulidgen.reported-s" in keys, "anchor")
    need(not any(k.startswith("rq3.inator.") and ".types." in k for k in keys), "types keys already in the record")
    rec = json.load(open(W + "/reconcile.json"))
    inj = json.load(open(W + "/inator-positions.json"))
    S = rec["summary"]
    shas = {l.split()[1].split("/")[-1]: l.split()[0] for l in open(W + "/tarball-sha256.txt")}
    # our half
    ours = {}
    if ours_tsv:
        head, mode, run = sys.argv[3], sys.argv[4], sys.argv[5]
        need(mode in ("final", "fallback"), "mode")
        for r in csv.DictReader(open(ours_tsv), delimiter="\t", quoting=csv.QUOTE_NONE):
            ours.setdefault(r["program"], []).append(r)
        for p in PROGS:
            need(len(ours.get(p, [])) == S[p]["both"], "%s: ours rows %d != positions %d" % (p, len(ours.get(p, [])), S[p]["both"]))
            need(all(r["ours"] in OB for r in ours[p]), "%s: a position outside ref/mut/box/raw: %s" % (p, {r['ours'] for r in ours[p]} - set(OB)))
        prep = {p: json.load(open(f"{run}/prep/{p}/prep.json")) for p in PROGS}
    c2sha = {}
    for l in open("scratch/analysis-fanout/rq3/c2rust-out/c2rust-out-sha256.tsv"):
        c = l.rstrip("\n").split("\t")
        if len(c) >= 4 and c[1].endswith("src/source.rs"):
            c2sha[c[0]] = c[3]
    new = []
    tot = collections.Counter()
    def row(key, value, unit, prov):
        need("|" not in prov and "\t" not in prov and "\n" not in prov, key)
        new.append("| %s | %s | pending | n/a | %s | %s |" % (key, value, unit, prov))
    UNIT = ("the unit (relay 143 section 1): a parameter, return or struct field whose C type is a pointer, of a function "
            "DEFINED in the program (main in) or a struct defined in it; function pointers out; both sides read the same C "
            "(&inator: the artifact's benchmarks/<p>/source.c; ours: the c2rust translation of it); positions present on both sides")
    for p in PROGS:
        n = NAME.get(p, p)
        s = S[p]
        binary = inj["out"][p]["binary"]
        tar = "diag/diag-trials-raw.tar.gz" if "diag" in binary else "results/trials-raw.tar.gz"
        IPROV = ("analysis-fanout 119 (relay 143, R1068-1): &inator's type of each position, from the kept artifacts "
                 "(agents/artifacts/2026-09-29-rq3-inator/%s, sha256 %s = its SHA256SUMS), %s: rtypes.txt (its Rust type "
                 "fragments) joined label for label to stypes.txt (its source types); bucket by the outermost constructor: "
                 "&'n -> ref, &'n mut -> mut, Box -> box, Rc -> rc, Cell / RefCell -> cell / refcell, ghost (the paper p. 9: "
                 "the referent itself, T / Option<T>) -> ghost, unknown / anything else -> other; a struct field prints as its "
                 "place; positions joined to the c2rust translation (c2rust src/source.rs sha256 %s; r143/reconcile.py); "
                 "R667-1 stands except for this table (no rate, waiver or parity number from the nine); %s"
                 % (tar, shas[os.path.basename(tar)][:16], binary, c2sha.get(p, "?")[:16], UNIT))
        row(f"rq3.inator.{n}.types.pos", s["both"], "count", IPROV + "; positions on both sides")
        for b in IB:
            v = s["buckets"].get(b, 0)
            tot["inator." + b] += v
            row(f"rq3.inator.{n}.types.inator.{b}", v, "count", IPROV + "; &inator bucket " + b)
        if ours:
            c = collections.Counter(r["ours"] for r in ours[p])
            OPROV = ("analysis-fanout 119 (relay 143): our EMITTED type of each position at the %s head %s (%s), the nine "
                     "through the RQ3 pipeline (substrate -> S2 entry -> S1 solve -> census child, one trial; timing not of "
                     "record), the solve env of record era5c-r215-kindorder/jobs (analysis %s, configuration %s, the nine's "
                     "launch %s); emitted tree read by r143/ours.py (the safe twin where the exposure split one); bucket: "
                     "& / Option<&> / &[] / a read cursor -> ref, &mut / Option<&mut> / &mut [] / a mutable cursor -> mut, "
                     "Box / Option<Box> / Box<[]> -> box, *mut / *const -> raw (a compile-check revert counts raw); %s"
                     % (mode, head[:9], "the final landed head" if mode == "final" else "NOT the final head: batch 60, the fallback",
                        (prep[p].get("analysis") or "-")[:8], (prep[p].get("configuration") or "-")[:8], prep[p]["launch_digest"][:8], UNIT))
            for b in OB:
                tot["ours." + b] += c.get(b, 0)
                row(f"rq3.inator.{n}.types.ours.{b}", c.get(b, 0), "count", OPROV + "; our bucket " + b)
        else:
            for b in OB:
                row(f"rq3.inator.{n}.types.ours.{b}", "", "count", "PRE-REGISTERED (relay 143): EMPTY until our half runs at the final landed head (r143/our-half.sh); " + UNIT)
        row(f"rq3.inator.{n}.types.fnptr", s["fnptr"], "count",
            "analysis-fanout 119 (relay 143): function-pointer positions excluded from the unit (a note beside the table): c2rust's Option<unsafe extern \"C\" fn ...> type"
            + ("; tisp: anon.1 field 1 (Prim), which &inator prints as ptr(unknown)" if s["fnptr"] else ""))
        un = len(s["only_inator"]) + len(s["only_c2rust"])
        why = "; ".join(["%s %s %s: %s" % (k[0], k[1], k[2], "&inator only (glibc's extern-inline definition in the IR)" if k[1] in ("atoi", "atol") else "&inator only")
                         for k, _, _ in s["only_inator"]] + ["%s %s %s: c2rust only (a single-field struct absent from &inator's struct list)" % (k[0], k[1], k[2]) for k, _ in s["only_c2rust"]])
        row(f"rq3.inator.{n}.types.unmatched", un, "count", "analysis-fanout 119 (relay 143): positions on one side only, each named: " + (why or "none") +
            "; libc header aggregates (_IO_FILE, __va_list_tag, glibc's siginfo/sigaction internals) are outside the unit, not counted here")
        tot["pos"] += s["both"]; tot["fnptr"] += s["fnptr"]; tot["unmatched"] += un
    TP = "analysis-fanout 119 (relay 143): the sum over the nine program rows of the same name"
    row("rq3.inator.total.types.pos", tot["pos"], "count", TP)
    for b in IB:
        row(f"rq3.inator.total.types.inator.{b}", tot["inator." + b], "count", TP)
    for b in OB:
        row(f"rq3.inator.total.types.ours.{b}", tot["ours." + b] if ours else "", "count", TP if ours else "PRE-REGISTERED (relay 143): EMPTY until our half runs")
    row("rq3.inator.total.types.fnptr", tot["fnptr"], "count", TP)
    row("rq3.inator.total.types.unmatched", tot["unmatched"], "count", TP)
    need(len(new) == 150, "rows %d" % len(new))
    a = keys["rq3.inator.ulidgen.reported-s"] + 1
    outl = lines[:a] + new + lines[a:]
    text = "\n".join(outl)
    open(out, "w", encoding="utf-8").write(text)
    print("in md5", hashlib.md5(raw).hexdigest(), "out md5", hashlib.md5(text.encode()).hexdigest(), "inserted", len(new),
          "pos", tot["pos"], {k: v for k, v in tot.items() if k.startswith(("inator", "ours"))})


if __name__ == "__main__":
    main()
