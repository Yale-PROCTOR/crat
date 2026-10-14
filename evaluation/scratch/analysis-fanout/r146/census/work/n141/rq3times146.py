#!/usr/bin/env python3
"""rq3times146.py <solve-dir>: the RQ3 twenty-program analysis times (analysis-fanout 104 / 106's definition): per program the
`wall_s` of the last complete `program` record in <solve>/progress.jsonl (one decimal), their sum (rq3.total.analysis-s), the
largest program brotli (rq3.largest.analysis-s, integer) and the sum over the other nineteen (rq3.rest.analysis-s, integer);
the host of each from workers/<p>.json, and the solve's concurrency read from the launch / program events. Read-only; fails
closed via SystemExit."""
import json, os, sys, datetime
S = sys.argv[1].rstrip('/')
P20 = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree', 'libzahl', 'lil',
       'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
ev = [json.loads(l) for l in open(S + '/progress.jsonl') if l.strip()]
wall, host, t0, t1 = {}, {}, {}, {}
for e in ev:
    if e.get('event') == 'launch':
        t0[e['program']] = e.get('utc')
    if e.get('event') == 'program' and e.get('status') == 'complete':
        wall[e['program']] = float(e['wall_s'])
        t1[e['program']] = e.get('utc')
missing = [p for p in P20 if p not in wall]
for p in P20:
    try:
        host[p] = json.load(open(f'{S}/workers/{p}.json')).get('host', '?')
    except FileNotFoundError:
        host[p] = '?'
ts = lambda x: datetime.datetime.strptime(x, '%Y-%m-%dT%H:%M:%SZ').timestamp()
conc = 0
pts = [(ts(t0[p]), 1) for p in t0 if t0[p] and t1.get(p)] + [(ts(t1[p]), -1) for p in t1 if t1[p] and t0.get(p)]
c = 0
for _, d in sorted(pts, key=lambda x: (x[0], x[1])):
    c += d; conc = max(conc, c)
done = [e for e in ev if e.get('event') == 'done']
print(f'# solve {S}: {len(wall)} of 20 programs with a complete record; missing {missing}; hosts {sorted(set(host.values()))}; '
      f'max concurrent (launch..complete) {conc}; done events {len(done)} ' + (json.dumps({k: v for k, v in done[-1].items() if k != "event"}) if done else ''))
for p in P20:
    if p in wall:
        print(f"rq3.{p.replace('.', '')}.analysis-s\t{wall[p]:.1f}\t{host[p]}\t{t0.get(p, '?')}\t{t1.get(p, '?')}")
if not missing:
    tot = sum(wall.values())
    print(f'rq3.total.analysis-s\t{tot:.1f}')
    print(f"rq3.largest.analysis-s\t{wall['brotli']:.0f}\t(brotli {wall['brotli']:.1f})")
    print(f"rq3.rest.analysis-s\t{tot - wall['brotli']:.0f}\t(sum of the other nineteen {tot - wall['brotli']:.1f})")
