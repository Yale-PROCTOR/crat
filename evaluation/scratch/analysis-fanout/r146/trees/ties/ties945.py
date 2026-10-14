#!/usr/bin/env python3
"""r140/trees: rq2.wins.decl / rq2.ties.decl recounted under R945-1 (relay 138 item 4, relay 139): CROWN's counter in
full, the same cells as Table 5 (rq1.<p>.decl.* as emitted = R945-1 + R947-2; rq2.<p>.decl.crown / .laertes = R945-1).

usage: ties945.py <t5r945 dir> <out dir>
Per program, exact fractions (no rounding):
  ours    = (ours_made - R947-2) / before    (R947-2: tulipindicators' 12 twin Box locals the walker reads raw as emitted;
                                               re-derived per run by r140/trees: the same 12 keys at 58 and 58'')
  crown   = crown_made / before              (R945-1 = evaluation.tsv; 0 movers)
  laertes = L_made / L_U                     (R945-1: absent with a before counterpart = made safe); brotli 0 (dagger,
                                               R891-1, as CROWN's Table 2 / ties_decl.py's PUBLISHED_LAERTES)
  win: ours > max(crown, laertes); tie: ours == max(crown, laertes) (exact); else below.
Also printed (provenance only): the same with ours = the twin reading (ours_twin_made), and without R947-2."""
import json, os, sys
from fractions import Fraction as F
T5, OUT = sys.argv[1], sys.argv[2]
R9472 = {'tulipindicators': 12}
per = json.load(open(os.path.join(T5, 'per-program.json')))
os.makedirs(OUT, exist_ok=True)
rows, res = [], {}
for variant in ('as-emitted', 'as-emitted-no-R947-2', 'twin'):
    wins, ties = [], []
    for r in per:
        p, b = r['program'], r['before']
        o = r['ours_twin_made'] if variant == 'twin' else r['ours_made'] - (R9472.get(p, 0) if variant == 'as-emitted' else 0)
        on, cn = F(o, b), F(r['crown_made'], b)
        ln = F(0) if p == 'brotli' else F(r['L_made'], r['L_U'])
        best = max(cn, ln)
        v = 'win' if on > best else ('tie' if on == best else 'below')
        (wins if v == 'win' else ties if v == 'tie' else []).append(p)
        if variant == 'as-emitted':
            rows.append([p, str(b), str(o), f'{100 * float(on):.4f}', str(r['crown_made']), f'{100 * float(cn):.4f}',
                         '-' if p == 'brotli' else f"{r['L_made']}/{r['L_U']}", f'{100 * float(ln):.4f}', v])
    res[variant] = (wins, ties)
with open(os.path.join(OUT, 'per-program-decl945.tsv'), 'w') as f:
    f.write('program\tbefore\tours_made\tours_rate\tcrown_made\tcrown_rate\tlaertes_made/U\tlaertes_rate\tverdict\n')
    for r in rows:
        f.write('\t'.join(r) + '\n')
with open(os.path.join(OUT, 'ties-decl945.tsv'), 'w') as f:
    f.write('variant\twins\tties\twin_programs\ttie_programs\n')
    for v, (w, t) in res.items():
        f.write(f'{v}\t{len(w)}\t{len(t)}\t{",".join(w)}\t{",".join(t)}\n')
print(open(os.path.join(OUT, 'ties-decl945.tsv')).read())
