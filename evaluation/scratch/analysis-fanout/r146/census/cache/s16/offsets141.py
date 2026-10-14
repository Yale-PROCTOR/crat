#!/usr/bin/env python3
"""r141: licensing-offsets.txt for one solve (r110 s16u hash_licensing's locate, one solve only): name 0 start end len.
argv: SOLVE OUT. Programs from the L01^14u launch manifest (the twenty); entry = workers/<p>.json completed.cache_entry,
falling back to the solve's own cache dir (the S39 row's host-b ten). Fails closed via SystemExit."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from locate_licensing import locate
S, OUT = sys.argv[1], sys.argv[2]
progs = [x["program"] for x in json.load(open("worktrees/era5c-l01p14u-solve/launch-manifest.json"))["programs"]]
if len(progs) != 20:
    raise SystemExit("not twenty programs")
with open(OUT, "w") as w:
    for p in progs:
        e = json.load(open(f"{S}/workers/{p}.json"))["completed"]["cache_entry"]
        if not os.path.exists(e):
            e = os.path.join(S, "cache/era5b-model-cache-v1", os.path.basename(e))
        size, s, en = locate(e)
        if s is None or en is None:
            raise SystemExit(f"{p}: licensing section not located")
        w.write(f"{os.path.basename(e)} 0 {s} {en} {en - s}\n")
        print(p, os.path.basename(e), s, en, en - s, flush=True)
