#!/usr/bin/env python3
"""r146: per-slot model kinds of four caches through r100's bounded head reader (model_head.read_head; the tail is
never read): L01^14 (era5c-l01p14-restored-solve, both owner terms on), L01^14u (era5c-l01p14u-solve), S39
(era5c-r211-s39pp, 58'''), 60-KINDORDER (era5c-r215-kindorder, 60s'). r141's dump_heads141.py extended by one column.
Output models.tsv: program slot kind14 kind14u kinds39 kind60sp ('-' = absent); summary.txt per program.
Fails closed via SystemExit."""
import collections, json, os, sys
sys.path.insert(0, "scratch/analysis-fanout/r100/keymap")
from model_head import read_head
AW = "dev/worktrees"
SOLVES = [AW + "/era5c-l01p14-restored-solve", AW + "/era5c-l01p14u-solve", AW + "/era5c-r211-s39pp", AW + "/era5c-r215-kindorder"]
O = os.path.dirname(os.path.abspath(__file__))
progs = [x["program"] for x in json.load(open(SOLVES[1] + "/launch-manifest.json"))["programs"]]
if len(progs) != 20:
    raise SystemExit("not twenty")
out = open(O + "/models.tsv", "w"); out.write("program\tslot\tkind14\tkind14u\tkinds39\tkind60sp\n")
summ = open(O + "/summary.txt", "w")
for p in progs:
    ms = []
    for S in SOLVES:
        e = json.load(open(f"{S}/workers/{p}.json"))["completed"]["cache_entry"]
        if not os.path.exists(e):
            e = os.path.join(S, "cache/era5b-model-cache-v1", os.path.basename(e))
        prog, u, m, n = read_head(e)
        if prog != p or set(u) != set(m):
            raise SystemExit(f"{p}: head program {prog} / universe != model")
        ms.append(m)
    a, b, c, d = ms
    for k in sorted(set(a) | set(b) | set(c) | set(d)):
        out.write(f"{p}\t{k}\t{a.get(k, '-')}\t{b.get(k, '-')}\t{c.get(k, '-')}\t{d.get(k, '-')}\n")
    mv = lambda x, y: dict(collections.Counter((x.get(k, '-'), y.get(k, '-')) for k in set(x) | set(y) if x.get(k) != y.get(k)))
    line = (f"{p}\tslots14={len(a)}\tslots14u={len(b)}\tslotss39={len(c)}\tslots60sp={len(d)}\t14u={dict(collections.Counter(b.values()))}\t"
            f"s39={dict(collections.Counter(c.values()))}\t60sp={dict(collections.Counter(d.values()))}\tmoved14->14u={mv(a, b)}\tmoved14u->s39={mv(b, c)}\t"
            f"moved14->s39={mv(a, c)}\tmoveds39->60sp={mv(c, d)}\tmoved14->60sp={mv(a, d)}")
    print(line, flush=True); summ.write(line + "\n")
