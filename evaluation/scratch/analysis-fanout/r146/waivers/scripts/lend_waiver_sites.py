"""lend_waiver_sites.py <cache-dir>: analysis-fanout 038's lend_waiver_sites.py parameterized by the cache dir, with the chunk
tail kept as intended (038's `len(buf) - 1 << 20` parses as `(len(buf) - 1) << 20`, so its tail is always empty and a list
straddling a 64 MiB boundary is missed; here the last 1 MiB is re-scanned -- sites are a set, so re-scanning cannot double count).
Prints both the fixed count and the count under 038's tail (the control's form)."""
import glob, json, re, sys
C = sys.argv[1]
pat = re.compile(rb'"waivers":(\[[^\]]*\])')
tot = tot_f = tot_orig = 0
for f in sorted(glob.glob(C + '/*.json')):
    p = re.search(rb'"program": *"([^"]+)"', open(f, 'rb').read(400)).group(1).decode()
    sites, sf, orig = set(), set(), set()
    with open(f, 'rb') as fh:
        tail = b''; off = 0
        while True:
            chunk = fh.read(1 << 26)
            if not chunk: break
            buf = tail + chunk; last = 0; base = off - len(tail)
            for m in pat.finditer(buf):
                last = m.end()
                for w in json.loads(m.group(1)):
                    s = (w['caller'], w['block'], w['statement'], w['argument'])
                    sites.add(s); sf.add(s + (w['formal'],))
                    if m.start() >= len(tail): orig.add(s)  # wholly inside this chunk: what 038's empty tail sees
            tail = buf[max(last, len(buf) - (1 << 20)):]
            off += len(chunk)
    if sites:
        print(f'{p}\t{len(sites)}\t(site, formal) {len(sf)}\t038-tail {len(orig)}', flush=True)
        for c, b, s, a in sorted(sites): print(f'    lend-waiver(tier-2, kind=indirect-call, site={c}:bb{b}[{s}]:arg{a})')
    tot += len(sites); tot_f += len(sf); tot_orig += len(orig)
print('total receipts', tot, ' (site, formal)', tot_f, ' 038-tail', tot_orig)
