#!/usr/bin/env python3
"""relay 104: setup.<prog>.sloc (data tables excluded) and setup.<prog>.sloc.total; setup.sloc / setup.largest-sloc by the same rule, with .total keys."""
import json, re, sys
NR, J = sys.argv[1], sys.argv[2]
d = json.load(open(J))
key = lambda p: p.replace('.', '')
RULE = ('SLOC = non-blank lines that are not wholly comment, over the program\'s .rs files except build.rs, in the c2rust output as distributed '
        '(benchmarks/rs-crown/<prog>; agents/tools/seed_numbers.py\'s definition of record, main 132). A DATA TABLE is excluded: a file at least 99.9 % of whose physical lines '
        'lie inside static or const initializers (generated data, not code). On the twenty this excludes exactly brotli\'s three dictionary files '
        '(src/common/dictionary.rs 122,883 lines, 99.98 % data; src/enc/encoder_dict.rs 286,489, 99.98 %; src/enc/dictionary_hash.rs 65,547, 99.99 %) and no other file '
        '(the next highest share is brotli\'s src/common/context.rs, 99.81 %, 2,054 lines). The seat\'s wording "a file of static initializers with no function body" does not fit its own list: '
        'encoder_dict.rs ends in one function body (BrotliInitEncoderDictionary) and dictionary.rs in two, while the wording would exclude small static tables '
        '(brotli constants.rs, context.rs, command.rs, fast_log.rs; bzip2 crctable.rs, randtable.rs) and keep two dictionaries; the share rule gives the seat\'s list. '
        'Tool: agents/artifacts/2026-10-06-analysis-fanout-080/sloc104.py; analysis-fanout 080 (relay 104). Frame-independent (the distributed input). ')
lines = open(NR).read().split('\n'); idx = {}
for i, l in enumerate(lines):
    m = re.match(r'^\| ([A-Za-z][A-Za-z0-9._-]*) \|', l)
    if m: idx[m.group(1)] = i
def setrow(k, v, p, unit='SLOC'):
    assert '|' not in p
    if k in idx:
        c = [x.strip() for x in lines[idx[k]].split('|')]
        lines[idx[k]] = f'| {k} | {v} | pending | {c[4]} | {c[5]} | {p} |'
    else:
        lines.insert(len(lines) - (1 if lines[-1] == '' else 0), f'| {k} | {v} | pending | n/a | {unit} | {p} |')
for prog, v in d.items():
    ex = v['excluded']
    exs = ('excluded here: ' + '; '.join(f'{f} ({s:,} SLOC)' for f, s, L, sh in ex)) if ex else 'no data table in this program'
    setrow(f'setup.{key(prog)}.sloc', str(v['sloc']), RULE + f'{prog}: {v["files"]} files, {v["sloc_total"]:,} SLOC in all; {exs}.')
    setrow(f'setup.{key(prog)}.sloc.total', str(v['sloc_total']), RULE + f'{prog}: every .rs file except build.rs, data tables included ({v["files"]} files).')
t = sum(v['sloc'] for v in d.values()); tt = sum(v['sloc_total'] for v in d.values())
lg = max(d, key=lambda p: d[p]['sloc'])
setrow('setup.sloc', str(t), RULE + f'The twenty, data tables excluded (156,209 = the sum of setup.<prog>.sloc); with them {tt:,} = setup.sloc.total. Re-seeded by the same rule so the total agrees with the per-program rows (was 631,128, every file).')
setrow('setup.sloc.total', str(tt), RULE + 'The twenty, every .rs file except build.rs (the previous setup.sloc).')
setrow('setup.largest-sloc', str(d[lg]['sloc']), RULE + f'The largest program ({lg}) by SLOC with data tables excluded: {d[lg]["sloc"]:,} (was 537,692 with its three dictionary files = setup.largest-sloc.total). {lg} stays the largest either way (next: tulipindicators 19,760).')
setrow('setup.largest-sloc.total', str(d[lg]['sloc_total']), RULE + f'{lg} with every file (the previous setup.largest-sloc).')
open(NR, 'w').write('\n'.join(lines).rstrip('\n') + '\n'); print('ok', t, tt, lg)
