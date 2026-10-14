#!/usr/bin/env python3
"""analysis-fanout r125/b (relay 125, S31(b)): the twin reading of CROWN's declaration counter, per program.

usage: decl_twin.py <census dir> <out dir>

Method = decl_walker_vs_census.py (030/030a/045), with the PRE-BUILT rq2_decl_driver (never built here):
- control first, fail-closed: CROWN's own twenty reproduce evaluation.tsv (plain and inline-mods);
- as emitted:  driver <tree> <analysis_results> inline-mods slots=<p>.walker-slots.tsv
- twin:        driver <tree> <analysis_results> inline-mods crat-twin slots=<p>.walker-slots-twin.tsv
  (each `__crat_safe_<f>` body read under <f>'s name); safe = slots with walker != none;
- census side: decl_walker_vs_census.census_side (main's seed_numbers definition: a universe declaration is delivered
  when all its census subjects are realized-as-predicted), to report the slot-level difference both ways.
Writes <out>/per-program.tsv and <out>/summary.json. Writes no key."""
import csv, json, os, subprocess, sys

sys.path.insert(0, 'docs/agents/tools/rq2')
sys.dont_write_bytecode = True
import decl_walker_vs_census as D  # noqa: E402  (imports seed_numbers; driver() is never called)

EXE = 'scratch/analysis-fanout/r10/target-tool/release/rq2_decl_driver'
SN = D.SN


def measure(tree, ar, flags):
    out = subprocess.run(['nice', '-n', '10', EXE, tree, ar] + list(flags), check=True, capture_output=True,
                         text=True).stdout.split()
    d = dict(x.split('=') for x in out)
    return {k: (float(v) if k == 'rate' else int(v)) for k, v in d.items()}


def main():
    census, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    ev = {}
    for r in csv.reader(open(os.path.join(SN.CROWN, 'evaluation.tsv'))):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]))
    for p in sorted(ev):
        for flags in ((), ('inline-mods',)):
            c = measure(os.path.join(SN.CROWN, p), os.path.join(SN.CROWN, p, 'analysis_results'), flags)
            if (c['universe'], c['after']) != ev[p] or c['parse_failures']:
                sys.exit(f'control failed on {p} {flags}: {c} vs {ev[p]}; nothing written')
    rows = []
    for p in SN.PROGRAMS:
        U = SN.crown_universe(p)
        tree = os.path.join(census, 'emitted-trees', p)
        ar = os.path.join(SN.CROWN, p, 'analysis_results')
        s_ae = os.path.join(out, f'{p}.walker-slots.tsv')
        s_tw = os.path.join(out, f'{p}.walker-slots-twin.tsv')
        ae = measure(tree, ar, ('inline-mods', f'slots={s_ae}'))
        tw = measure(tree, ar, ('inline-mods', 'crat-twin', f'slots={s_tw}'))
        wae = {r['key']: r['walker'] for r in csv.DictReader(open(s_ae), delimiter='\t')}
        wtw = {r['key']: r['walker'] for r in csv.DictReader(open(s_tw), delimiter='\t')}
        if set(wae) != U or set(wtw) != U:
            sys.exit(f'{p}: walker universe != crown_universe; nothing written')
        safe_ae = {k for k, v in wae.items() if v != 'none'}
        safe_tw = {k for k, v in wtw.items() if v != 'none'}
        assert len(safe_ae) == ae['eliminated_ref'] + ae['eliminated_box'], (p, 'ae')
        assert len(safe_tw) == tw['eliminated_ref'] + tw['eliminated_box'], (p, 'twin')
        _, delivered = D.census_side(census, p, U)
        rows.append({'program': p, 'before': len(U), 'ae_safe': len(safe_ae), 'twin_safe': len(safe_tw),
                     'twin_ref': tw['eliminated_ref'], 'twin_box': tw['eliminated_box'],
                     'ae_rate': SN.pct(len(safe_ae), len(U)), 'twin_rate': SN.pct(len(safe_tw), len(U)),
                     'twin_minus_ae': len(safe_tw - safe_ae), 'ae_minus_twin': len(safe_ae - safe_tw),
                     'census_delivered': len(delivered), 'twin_census_only': len(delivered - safe_tw),
                     'twin_walker_only': len(safe_tw - delivered),
                     'parse_failures': ae['parse_failures'] + tw['parse_failures']})
    with open(os.path.join(out, 'per-program.tsv'), 'w') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    tb = sum(r['before'] for r in rows)
    s = {'census': census, 'control': 'evaluation.tsv 20/20 plain and inline-mods', 'before': tb,
         'ae_safe': sum(r['ae_safe'] for r in rows), 'twin_safe': sum(r['twin_safe'] for r in rows),
         'census_delivered': sum(r['census_delivered'] for r in rows),
         'twin_census_only': sum(r['twin_census_only'] for r in rows),
         'twin_walker_only': sum(r['twin_walker_only'] for r in rows)}
    s['ae_rate'] = SN.pct(s['ae_safe'], tb)
    s['twin_rate'] = SN.pct(s['twin_safe'], tb)
    json.dump(s, open(os.path.join(out, 'summary.json'), 'w'), indent=1)
    print(json.dumps(s, indent=1))


if __name__ == '__main__':
    main()
