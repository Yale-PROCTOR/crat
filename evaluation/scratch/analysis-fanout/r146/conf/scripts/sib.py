#!/usr/bin/env python3
"""r141 conf: waiver.sibling-sites / .programs = the pending-sibling-overlap receipts of a census (count + descriptors per
program; the .tsv must carry only its header). Fails closed through raise SystemExit."""
import glob, json, os, sys
M = 'scratch/main'
for b in sys.argv[1:]:
    fs = sorted(glob.glob(f'{M}/{b}/*.raw-boundary-pending-sibling-overlap.json'))
    if len(fs) != 20:
        raise SystemExit(f'{b}: {len(fs)} sibling json files, not 20')
    tot = progs = desc = 0
    for f in fs:
        d = json.load(open(f))
        if not isinstance(d.get('count'), int):
            raise SystemExit('no integer count in ' + f)
        n = len(d.get('descriptors', []))
        if n != d['count']:
            raise SystemExit(f'count {d["count"]} != descriptors {n} in {f}')
        tot += d['count']; desc += n; progs += bool(d['count'])
    tsv = sorted(glob.glob(f'{M}/{b}/*.raw-boundary-pending-sibling-overlap.tsv'))
    rows = sum(sum(1 for _ in open(t)) - 1 for t in tsv)
    print(f'{b}\tjson_files={len(fs)}\tcount={tot}\tdescriptors={desc}\tprograms={progs}\ttsv_files={len(tsv)}\ttsv_rows={rows}')
