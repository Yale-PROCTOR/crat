#!/usr/bin/env python3
"""r141 conf: ec4.cover.decline's solve-side half -- main's frame14u-r863.sh criterion (5) re-pointed at a manifest:
per manifest entry, the receipt fields repair / guarded_fallbacks / guarded_verifications / a5_mode streamed from the
entry's head (64 MiB chunks, <= 2 GiB, never parsed whole) + the solve progress records (status, returncode, wall_s).
usage: guarded.py <cache-dir> <manifest.tsv> <progress.jsonl>... ; fails closed (raise SystemExit)."""
import csv, json, os, re, sys
C, MAN = sys.argv[1], sys.argv[2]
rows = list(csv.DictReader(open(MAN), delimiter='\t'))
if len(rows) != 20:
    raise SystemExit('manifest: not 20 rows')
prog = {}
for pf in sys.argv[3:]:
    for l in open(pf):
        if l.strip():
            r = json.loads(l)
            if r.get('event') == 'program' and r.get('status') == 'complete':
                prog[r['key']] = (pf, r)
want = ('repair', 'guarded_fallbacks', 'guarded_verifications', 'a5_mode')
n_g = n_fb = n_c = 0
for m in rows:
    f = os.path.join(C, m['fingerprint'] + '.json')
    if not os.path.exists(f):
        raise SystemExit('missing entry ' + f)
    keys, pos, tail = {}, 0, b''
    with open(f, 'rb') as fh:
        while pos < (2 << 30) and len(keys) < len(want):
            chunk = fh.read(64 << 20)
            if not chunk:
                break
            buf = tail + chunk
            for k in want:
                if k not in keys:
                    mm = re.search(k.encode() + rb'=([A-Za-z0-9_]+)', buf)
                    if mm:
                        keys[k] = mm.group(1).decode()
            tail, pos = buf[-256:], pos + len(chunk)
    pr = prog.get(m['fingerprint'])
    ok_c = bool(pr) and pr[1].get('returncode') == 0 and pr[1].get('entry_sha256') == m['entry_sha256']
    n_c += ok_c; n_g += keys.get('repair') == 'guarded'; n_fb += keys.get('guarded_fallbacks') == '0'
    print('\t'.join([m['program'], keys.get('repair', '?'), keys.get('guarded_fallbacks', '?'), keys.get('guarded_verifications', '?'),
                     keys.get('a5_mode', '?'), 'complete' if ok_c else 'NO-RECORD',
                     str(pr[1].get('wall_s')) if pr else '-', str(pr[1].get('utc')) if pr else '-',
                     os.path.basename(os.path.dirname(pr[0])) + '/' + os.path.basename(pr[0]) if pr else '-']))
print(f'# complete rc=0 with entry_sha256 = manifest {n_c}/20; repair=guarded {n_g}/20; guarded_fallbacks=0 {n_fb}/20')
