#!/usr/bin/env python3
"""relay 104: SLOC (seed_numbers.py's definition of record: non-blank, not-wholly-comment lines over .rs files except build.rs)
per program, total and excluding data tables (a file at least 99.9 % of whose physical lines lie inside static/const initializers)."""
import glob, importlib.util, json, os, sys
sp = importlib.util.spec_from_file_location('sn', 'docs/agents/tools/seed_numbers.py')
spec2 = importlib.util.spec_from_file_location('fr', 'scratch/analysis-fanout/r104/frac_lib.py')
fr = importlib.util.module_from_spec(spec2); spec2.loader.exec_module(fr)
src = open('docs/agents/tools/seed_numbers.py').read()
ns = {}; exec(src[src.index('def sloc_of_text'):src.index('def sloc(root)')], ns); sloc_of_text = ns['sloc_of_text']
base = sys.argv[1]; out = {}
for prog in sorted(p for p in os.listdir(base) if os.path.isdir(os.path.join(base, p))):
    files = sorted(f for f in glob.glob(f'{base}/{prog}/**/*.rs', recursive=True) if os.path.basename(f) != 'build.rs')
    rows = []
    for f in files:
        t = open(f, errors='replace').read(); L = t.count('\n'); d = fr.data_lines(t)
        rows.append({'file': os.path.relpath(f, f'{base}/{prog}'), 'lines': L, 'sloc': sloc_of_text(t), 'data_share': (d / L if L else 0)})
    data = [r for r in rows if r['data_share'] >= 0.999]
    out[prog] = {'files': len(rows), 'sloc_total': sum(r['sloc'] for r in rows), 'sloc': sum(r['sloc'] for r in rows if r not in data),
                 'excluded': [(r['file'], r['sloc'], r['lines'], round(r['data_share'], 5)) for r in data]}
    print(prog, out[prog]['files'], out[prog]['sloc_total'], out[prog]['sloc'], out[prog]['excluded'])
json.dump(out, open(sys.argv[2], 'w'), indent=1)
t = sum(v['sloc'] for v in out.values()); tt = sum(v['sloc_total'] for v in out.values())
lg = max(out, key=lambda p: out[p]['sloc'])
print('setup.sloc', t, 'total', tt, 'largest', lg, out[lg]['sloc'], out[lg]['sloc_total'], 'rest', t - out[lg]['sloc'], tt - out[lg]['sloc_total'])
