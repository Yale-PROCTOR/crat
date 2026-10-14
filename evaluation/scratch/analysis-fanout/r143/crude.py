"""relay 143: the seat's crude count (interface lines of rtypes.txt incl. externs, trial 1), reproduced and reconciled with
the unit by name."""
import json, os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import positions as P
inj = json.load(open("inator-positions.json")); rec = json.load(open("reconcile.json"))
SEAT = {"amp": 25, "carrays": 65, "jccc": 116, "leftpad": 12, "nandc": 9, "rbtree": 35, "running-example": 9, "tisp": 138, "ulidgen": 27}
def all_positions(d):
    """every interface line: params + returns of defined AND declared functions, struct fields"""
    lines = open(d + "/rtypes.txt", encoding="utf-8").read().split("\n")
    out = []
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r"^struct (\S+?)(<.*?>)?\s+\{$", l)
        if m:
            i += 1
            while not lines[i].startswith("};"):
                fm = re.match(r"^\s+(.*?)\s+(\d+);$", lines[i]); out.append(("field", m.group(1), fm.group(2), fm.group(1))); i += 1
            i += 1; continue
        m0 = re.match(r"^(\[.*[⁰¹²³⁴⁵⁶⁷⁸⁹])\s+(\S+)\(\)( \{|;)$", l)
        if m0:
            out.append(("return", m0.group(2), "-1", m0.group(1), m0.group(3) == " {")); i += 1; continue
        m = re.match(r"^(\[.*[⁰¹²³⁴⁵⁶⁷⁸⁹])\s+(\S+)\($", l)
        if m:
            ps = []; i += 1
            while not lines[i].startswith(")"):
                ps.append(P.split_type_name(lines[i])); i += 1
            body = lines[i].strip() == ") {"
            out.append(("return", m.group(2), "-1", m.group(1), body))
            for k, (t, n) in enumerate(ps):
                out.append(("param", m.group(2), str(k), t, body))
            i += 1; continue
        i += 1
    return out
tot = 0
for p, seat in SEAT.items():
    d = inj["out"][p]["dir"]
    rows = []
    for r in all_positions(d):
        b, t = P.inator_bucket(P.strip_labels(r[3]))
        if b in ("ref", "mut", "box", "rc", "ghost", "cell", "refcell"):
            rows.append((r, b))
    n = len(rows); tot += n
    both = {(x["kind"], x["owner"], x["index"]) for x in rec["rows"] if x["program"] == p}
    why = collections.Counter()
    for r, b in rows:
        owner = re.sub(r"^(struct|union)\.", "", r[1])
        if (r[0], owner, int(r[2])) in both: why["in the unit"] += 1
        elif r[0] != "field" and not r[4]: why["extern / intrinsic declaration (no body)"] += 1
        elif r[0] == "field": why["struct field whose own type is not a pointer (a ghost place over a scalar/struct) or a libc/anonymous aggregate"] += 1
        else: why["defined function, C type not a pointer (by-value struct, scalar) or outside the unit"] += 1
    print(p, "crude", n, "seat", seat, "|", dict(why))
print("total crude", tot, "seat 436")
