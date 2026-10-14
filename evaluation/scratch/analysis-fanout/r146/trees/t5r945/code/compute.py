#!/usr/bin/env python3
"""r130/t5: Table 5's declaration keys under R945-1 (CROWN's counter in full), at batch 56, from existing typed
counter outputs (no binary run). Writes per-program.tsv, keys.tsv, per-key/<tool>/<p>.tsv, movers.tsv, controls.txt."""
import csv, json, os, re, statistics, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r945 as R
import srcscan as S

AF = 'scratch/analysis-fanout'
OUT = f'{AF}/r146/trees/t5/out'          # r133: the t5 run (ours58 = main/batch58; other sides cp -rL copies of r122/gtree/t5/out)
T5 = f'{AF}/r146/trees/t5r945'
CRAT = 'crat'
INPUT = f'{CRAT}/benchmarks/rs-crown'
CROWN = f'{CRAT}/benchmarks/rs-crown-transformed'
OURS = 'scratch/main/batch58pps39/emitted-trees'
ART = 'crown-artifact/comparison'
REC = 'tmp/scratchpad/wt067/paper/numbers-of-record.md'
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
LPATH = {l.split('/')[0]: os.path.dirname(l.strip()) for l in open(f'{ART}/laertes-path') if l.strip()}


def key(p):
    return p.replace('.', '')


def pct(n, d):
    return 100.0 * n / d if d else float('nan')


def fmt(x):
    return f'{x:.1f}%'


def record():
    rec = {}
    for line in open(REC):
        m = re.match(r'^\| (rq[12]\.[^ |]+) \| ([^|]*)\| ([^|]*)\|', line)
        if m:
            rec[m.group(1)] = (m.group(2).strip(), m.group(3).strip())
    return rec


def evaluation():
    ev = {}
    for r in csv.reader(open(f'{CROWN}/evaluation.tsv')):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]))
    return ev


def universe(p, flat=False, roottest=False):
    f = f'{OUT}/universe/{p}{"-flat" if flat else ""}{"-roottest" if roottest else ""}.txt'
    return {l for l in open(f).read().split('\n') if l}


def side_rows(side, p):
    if side.startswith('laertes') and p == 'urlparser':
        d = f'{OUT}/urlparser-roottest/{side}/urlparser'
    else:
        d = f'{OUT}/{side}/{p}'
    st = open(f'{d}/status.txt').read().split('\t')[0].strip()
    if st != 'ok':
        return None
    return R.rows(f'{d}/positions.tsv')


def laertes_dir(p, before=False):
    lc = f'{ART}/laertes-crown/after/{p}'
    d = lc if os.path.isdir(lc) else (f'{ART}/laertes-laertes/after/{LPATH[p]}' if p in LPATH else None)
    return d.replace('/after/', '/before/') if (d and before) else d


def classify(d0, U, fns, flat):
    """per key: (n raw-outer bindings, class) with class in raw / safe-form / <shape> / non-pointer / removed."""
    out = {}
    for k in sorted(U):
        bs = d0.get(k, [])
        nraw = sum(1 for b in bs if R.is_raw_outer(b[3]))
        if nraw:
            cls = 'raw'
        elif bs:
            shapes = sorted({R.shape(b) for b in bs if R.shape(b)})
            cls = 'shape:' + '+'.join(shapes) if shapes else 'safe-form'
        else:
            owner, _, var = k.rpartition('::')
            bodies = S.find(fns, owner, flat) if fns is not None else []
            cls = 'non-pointer' if S.has_binding(bodies, var) else ('removed' if bodies else 'removed:fn-gone')
        out[k] = (nraw, cls, len(bs))
    return out


def main():
    ev, rec = evaluation(), record()
    os.makedirs(f'{T5}/per-key', exist_ok=True)
    ctl, per, movers = [], [], []
    tot = dict(B=0, crown_after=0, ours=0, ours_twin=0, ours_keys=0, ours_twin_keys=0, laertes=0, laertes_own_B=0,
               laertes_own_A=0)
    for p in PROGS:
        flatL = os.path.exists(f'{OUT}/laertes_after/{p}/flat.txt') and \
            open(f'{OUT}/laertes_after/{p}/flat.txt').read().strip() == 'flat'
        U = universe(p)
        # ---- input: CROWN's before, per MIR local
        d_in = R.depth0(side_rows('input', p), U)
        B = sum(R.crown_count(d_in).values())
        multi_in = sum(1 for v in R.crown_count(d_in).values() if v > 1)
        ctl.append(f'input\t{p}\tbefore(per binding)={B}\t|U|={len(U)}\tevaluation={ev[p][0]}\tmulti={multi_in}\t'
                   f'{"exact" if B == len(U) == ev[p][0] else "MISMATCH"}')
        # ---- CROWN's output: R753's control
        fc = S.tree_functions(f'{CROWN}/{p}')
        d_c = R.depth0(side_rows('crown', p), U)
        cc = classify(d_c, U, fc, False)
        Ac = sum(R.crown_count(d_c).values())
        ctl.append(f'crown\t{p}\tafter(per binding)={Ac}\tevaluation={ev[p][1]}\t'
                   f'{"exact" if (B, Ac) == ev[p] else "MISMATCH"}')
        # ---- ours (batch 56), as emitted and twin
        fo = S.tree_functions(f'{OURS}/{p}')
        rs_o = side_rows('ours58pps39', p)
        d_o, d_t = R.depth0(rs_o, U, asemitted=True), R.depth0(rs_o, U, twin=True)
        d_raw = R.depth0(rs_o, U)  # the literal reading (twin bodies unread): diagnostic only
        A_lit = sum(R.crown_count(d_raw).values())
        fo_t = {k: v for k, v in fo.items() if not (k[0], '__crat_safe_' + k[1]) in fo}
        fo_t.update({(m, n[len('__crat_safe_'):]): b for (m, n), b in fo.items() if n.startswith('__crat_safe_')})
        co, ct = classify(d_o, U, fo_t, False), classify(d_t, U, fo_t, False)
        Ao, At = sum(R.crown_count(d_o).values()), sum(R.crown_count(d_t).values())
        ko = sum(1 for v in co.values() if v[1] != 'raw')
        kt = sum(1 for v in ct.values() if v[1] != 'raw')
        # ---- Laertes
        if p == 'brotli':
            lrow = dict(L_made=None)
        else:
            UL = universe(p, flatL, roottest=(p == 'urlparser'))
            fa = S.tree_functions(laertes_dir(p))
            fb = S.tree_functions(laertes_dir(p, True))
            d_la = R.depth0(side_rows('laertes_after', p), UL, flatL)
            d_lb = R.depth0(side_rows('laertes_before', p), UL, flatL)
            cl = classify(d_la, UL, fa, flatL)
            AL = sum(R.crown_count(d_la).values())
            nocp = [k for k in UL if k not in d_lb]                         # no counterpart in Laertes's before tree
            nocp_norow = [k for k in nocp if cl[k][0] == 0]                  # ... and not already raw in the after tree
            nocp_binding = [k for k in nocp if S.has_binding(S.find(fb, k.rpartition('::')[0]), k.rpartition('::')[2])]
            L_not = AL + len(nocp_norow)
            L_made = len(UL) - L_not
            # provenance: against Laertes's own before tree (the mapped keys; CROWN's evaluate.sh/mkcomparison.sh)
            LB = sum(R.crown_count(d_lb).values())
            lrow = dict(L_U=len(UL), L_after_raw=AL, L_nocp=len(nocp), L_nocp_norow=len(nocp_norow),
                        L_nocp_binding_nonptr=len(nocp_binding), L_made=L_made, L_rate=pct(L_made, len(UL)),
                        L_own_before=LB, L_own_after=AL, L_own_rate=pct(LB - AL, LB),
                        L_multi_after=sum(1 for v in R.crown_count(d_la).values() if v > 1))
            for k, (n, c, nb) in sorted(cl.items()):
                if c != 'raw':
                    movers.append(('laertes', p, k, c + (':no-counterpart-in-before' if k in nocp else '')))
            json.dump({k: list(v) + [k in nocp] for k, v in cl.items()}, open(f'{T5}/per-key/laertes-{p}.json', 'w'),
                      indent=0)
        for tool, cls in (('crown', cc), ('ours', co), ('ours-twin', ct)):
            for k, (n, c, nb) in sorted(cls.items()):
                if c != 'raw':
                    movers.append((tool, p, k, c))
            json.dump({k: list(v) for k, v in cls.items()}, open(f'{T5}/per-key/{tool}-{p}.json', 'w'), indent=0)
        row = dict(program=p, U=len(U), before=B, crown_after=Ac, crown_made=B - Ac, crown_rate=pct(B - Ac, B),
                   ours_after=Ao, ours_made=B - Ao, ours_literal_made=B - A_lit, ours_rate=pct(B - Ao, B), ours_keys_made=ko,
                   ours_twin_after=At, ours_twin_made=B - At, ours_twin_rate=pct(B - At, B), ours_twin_keys_made=kt,
                   ours_multi=sum(1 for v in R.crown_count(d_o).values() if v > 1),
                   ours_twin_multi=sum(1 for v in R.crown_count(d_t).values() if v > 1),
                   **lrow)
        per.append(row)
    open(f'{T5}/controls.txt', 'w').write('\n'.join(ctl) + '\n')
    cols = list(dict.fromkeys(c for r in per for c in r))
    with open(f'{T5}/per-program.tsv', 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for r in per:
            f.write('\t'.join('' if r.get(c) is None else (f'{r[c]:.4f}' if isinstance(r.get(c), float) else str(r[c]))
                              for c in cols) + '\n')
    with open(f'{T5}/movers.tsv', 'w') as f:
        f.write('tool\tprogram\tkey\tclass\n')
        for m in movers:
            f.write('\t'.join(m) + '\n')
    json.dump(per, open(f'{T5}/per-program.json', 'w'), indent=1)
    print('\n'.join(ctl))


if __name__ == '__main__':
    main()
