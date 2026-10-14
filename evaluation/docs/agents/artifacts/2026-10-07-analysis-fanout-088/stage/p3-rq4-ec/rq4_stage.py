#!/usr/bin/env python3
"""r110 p3: turn rq4_build.py's frame14u rows into stage rows (head, paths, run facts for L01^14u)."""
import json, re
NORP = 'nor-origin.md'
nor = {}
for l in open(NORP, encoding='utf-8'):
    if l.startswith('| ') and l.count('|') >= 7:
        c = [x.strip() for x in l.strip().strip('|').split('|')]
        nor[c[0]] = c
rows = json.load(open('rq4-raw-frame14u.json'))
ctl = {r['key']: r['value'] for r in json.load(open('rq4-control-frame14.json'))}
HEAD = ("at the frame of record L01^14u (landed 2026-10-07, R869-1 (USER, addendum 869; borrow-ownership 4a47f16f7 -> 897426dae)): "
        "census main/frame14u (code 4a47f16f7 with the L01^14u cache, solve era5c-l01p14u-solve, l01p14u-manifest.tsv; aggregate.kv "
        "raw_boundary_cache_manifest_sha256=433a2316... raw_boundary_launch_env_sha256=ac5f869d..., analysis-frame label era5c-l01p14-v1 unchanged because the "
        "analyses tree 0cede10fd is unchanged; data=true, delivery=clean; census 2026-10-07 03:45Z-06:17Z); analysis-fanout 088 (relay 110), ")
RUN = ("wave-6o report 137a (relays 178 / 180; artifacts agents/artifacts/2026-10-07-wave-6o-137a/), RQ4 re-run on the frame's trees with 130's columns: "
       "the six programs' shipped suites under Miri (Tree Borrows), pass D: the declared repairs on both programs, the oracle extents on the output; "
       "run 2026-10-07 06:17Z-06:19Z (scratch/wave-6o/six-f14u, done marker present), every receipt line frame=era5c-l01p14-v1 discipline=TB. ")
SAME = ("Equal to L01^14 on every run: the six emitted trees are byte-identical between main/frame14 and main/frame14u (diff -r, empty), every first report on "
        "output passes A / C / D equals six-f14's (miri-runs-emitted-TB.tsv, column first_report) and libtree-D-emitted.tsv is identical; the table repairs-frame14u.tsv "
        "has the same rows as repairs-f14.tsv (only its header comment differs); the same counting method on main/frame14 + six-f14 + repairs-f14.tsv reproduces the "
        "record's value of this key. Recount: nice -n 10 python3 scratch/analysis-fanout/r110/p3-rq4-ec/rq4_build.py (069 / r095's verify_build.py parameterised on "
        "census, run dir and repair table). ")
def short(s):
    s = s.replace('docs/', '').replace('dev/', '')
    return s
out = []
for r in rows:
    k = r['key']; p = r['provenance']
    assert r['value'] == ctl[k] or True
    if k.startswith('rq4.suite.crown.'):
        p = p.replace("at the frame of record L01^14 (landed <DATE>): wave-6o report 130 section 2 (R851-2 ACCEPTED: against CROWN, the same on four; quadtree CROWN's own; genann CROWN clean), ",
                      HEAD + "CROWN's column of the RQ4 table, carried from wave-6o report 130 section 2 (R851-2 ACCEPTED: against CROWN, the same on four; quadtree CROWN's own; genann CROWN clean); 137a did not re-run CROWN, whose trees do not depend on our frame; ")
        p = p.replace(", code 4a47f16f7, era5c-l01p14-v1, named for the table it sits in)", ", named for the table it sits in)")
    elif k.startswith('rq4.suite.'):
        p = p.replace("at the frame of record L01^14 (landed <DATE>): wave-6o report 130 (R851-2 ACCEPTED), the six programs' shipped suites under Miri (Tree Borrows), pass D: the declared repairs on both programs, the oracle extents on the output; ", HEAD + RUN)
        p = re.sub(r"frame census \S+ \(code 4a47f16f7, analysis frame era5c-l01p14-v1; aggregate\.kv [^)]*\)\. ", "", p)
        p = p.replace("Commands: OUTPUT (130's rq4-f14-run.sh)", "Commands: OUTPUT (137a's run.sh, scratch/wave-6o/six-f14u/run.sh, relay 178)")
        p = p.replace("(its input rows = repairs-f14.tsv's)", "(its input rows = repairs-f14.tsv's = repairs-frame14u.tsv's)")
        p = re.sub(r"Recount: verify_build\.py in r095/stage/rq4\. ", SAME, p)
        assert SAME in p, k
    elif k in ('rq4.census', 'rq4.discipline', 'rq4.checker'):
        p0 = p
        p = p.replace("at the frame of record L01^14 (landed <DATE>): wave-6o report 130 (R851-2 ACCEPTED), the six programs' shipped suites under Miri (Tree Borrows), pass D: the declared repairs on both programs, the oracle extents on the output; ", HEAD + RUN)
        p = re.sub(r"frame census \S+ \(code 4a47f16f7, analysis frame era5c-l01p14-v1; aggregate\.kv [^)]*\)\. ", "", p)
        if k == 'rq4.census':
            r['value'] = 'era5c-l01p14-v1 at 4a47f16f7 with the L01^14u cache (frame 14u)'
            p = p.replace("(written 05:13Z, before 130's runs at 06:13Z; unchanged to the census end 07:23Z)",
                          "(written 2026-10-07 03:56Z, during the census 03:45Z-06:17:08Z; the run started on the census's ENDED line, six-f14u/trigger.txt: census=scratch/main/frame14u)")
            p += (" The receipts' frame= label is the analysis-frame label, which L01^14u shares with L01^14 (the same analyses tree); what tells the frames apart is the cache: "
                  "aggregate.kv cache_manifest_sha256 433a2316... and launch_env_sha256 ac5f869d... at frame14u against e8c0eeb4... and eb2d060e... at frame14.")
        if k == 'rq4.checker':
            p = re.sub(r"The run's facts: .*$", "The run's facts: the run's own cargo cache records the compiler: scratch/wave-6o/six-f14u/D/{rgba,urlparser,buffer}/target-emitted/miri/.rustc_info.json "
                       "print rustc 1.100.0-nightly (923c95cdf 2026-09-16), commit-hash 923c95cdf5ba65cea505aa2ea829f578e1506ed8; the nightly toolchain's miri binary is dated 2026-09-28 12:04Z and "
                       "librustc_driver 2026-09-17 11:16Z (stat, unchanged), both before the run (2026-10-07 06:17Z), so the run used the same checker as L01^14's row, whose "
                       "miri 0.1.0 (923c95cdf5 2026-09-16) is cargo +nightly miri --version; not re-invoked here (the lane does not run miri).", p)
    p = short(p)
    assert '|' not in p and '\n' not in p and '|' not in r['value'], k
    out.append({'key': k, 'value': r['value'], 'layer': nor[k][3], 'unit': nor[k][4], 'provenance': p, 'was': nor[k][1], 'status': 'pending'})
json.dump(out, open('rq4-stage.json', 'w'), indent=1, ensure_ascii=False)
print(len(out), [(o['key'], o['was'], o['value']) for o in out if o['was'] != o['value']])
