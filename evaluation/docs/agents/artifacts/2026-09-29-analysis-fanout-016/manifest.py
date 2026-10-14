#!/usr/bin/env python3
"""analysis-fanout 016: the nine &inator benchmarks' input manifest and C LoC.

  manifest.py GH_BENCHMARKS_DIR ZENODO_BENCHMARKS_DIR CLOC_PL OUTDIR
writes OUTDIR/inputs-sha256.tsv (every file of every benchmark directory at the GitHub commit, with its
SHA-256, and whether the Zenodo benchmarks.tar.gz carries it byte-identically) and OUTDIR/loc.tsv (cloc code
lines over the directory's .c/.h files, the measure Table 3's 'C LoC' column reproduces, beside Table 3).
"""
import hashlib, os, subprocess, sys
NINE = ['running-example', 'ulidgen', 'leftpad', 'amp', 'nandc', 'rbtree', 'carrays', 'jccc', 'tisp']
TABLE3 = {'running-example': 41, 'ulidgen': 69, 'leftpad': 72, 'amp': 99, 'nandc': 122, 'rbtree': 346,
          'carrays': 618, 'jccc': 1394, 'tisp': 3656}          # &inator paper (PLDI 2026), Table 3, "C LoC"
gh, zen, cloc, out = sys.argv[1:5]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
with open(os.path.join(out, 'inputs-sha256.tsv'), 'w') as f:
    f.write('program\tpath\tbytes\tsha256\tzenodo\n')
    for b in NINE:
        for d, dn, fn in sorted(os.walk(os.path.join(gh, b))):
            dn.sort()
            for n in sorted(fn):
                p = os.path.join(d, n); rel = os.path.relpath(p, gh)
                z = os.path.join(zen, rel)
                zs = ('same' if sha(z) == sha(p) else 'DIFFERS') if os.path.isfile(z) else 'absent'
                f.write(f'{b}\t{rel}\t{os.path.getsize(p)}\t{sha(p)}\t{zs}\n')
with open(os.path.join(out, 'loc.tsv'), 'w') as f:
    f.write('program\tc_files\tcloc_code\ttable3_c_loc\tmatch\n')
    for b in NINE:
        r = subprocess.run(['perl', cloc, '--quiet', '--csv', '--include-ext=c,h', os.path.join(gh, b)],
                           capture_output=True, text=True, check=True).stdout
        s = [l.split(',') for l in r.splitlines() if ',SUM,' in l or ',C,' in l or ',C/C++ Header,' in l]
        tot = next(int(x[4]) for x in s if x[1] == 'SUM') if any(x[1] == 'SUM' for x in s) else sum(int(x[4]) for x in s)
        nf = sum(int(x[0]) for x in s if x[1] != 'SUM')
        f.write(f'{b}\t{nf}\t{tot}\t{TABLE3[b]}\t{"yes" if tot == TABLE3[b] else "no"}\n')
