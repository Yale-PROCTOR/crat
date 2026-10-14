#!/usr/bin/env python3
"""decl_walker_vs_census.py — analysis-fanout 030 (relay 042, R748-1): CROWN's declaration counter, verbatim, on our
emitted trees, beside main's census-based `rq1.<prog>.decl.*`, with the slot-level difference both ways.

  decl_walker_vs_census.py --census <census dir> --out <dir> [--label <text>]

<census dir> is a census of the twenty (main's `frameNN/`): `emitted-trees/<prog>/` and the `<prog>.raw-boundary-*.tsv`.

- The walker: the `crown_artifact_inventory` library, unmodified, through `decl_driver` (015) with `inline-mods`
  (our trees hold the modules inline in one `lib.rs`; the option gives the walker CROWN's one-file-per-module keys).
- The control first, fail-closed: CROWN's own twenty outputs reproduce `evaluation.tsv` (2,414 -> 1,711), with and
  without `inline-mods`; else nothing is written.
- The census side is main's definition, imported from `seed_numbers.py` (the universe, the subject-outcomes join):
  a universe declaration is delivered when all its census subjects are `realized-as-predicted`.
- No key is written."""
import argparse, csv, json, os, re, subprocess, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'record'))
import seed_numbers as SN  # noqa: E402

csv.field_size_limit(10**9)
CROWN = SN.CROWN
TARGET = os.environ.get('RQ2_TARGET', os.path.join(HERE, 'decl_driver', 'target'))


def driver():
    exe = os.path.join(TARGET, 'release', 'rq2_decl_driver')
    subprocess.run(['cargo', 'build', '--release', '--offline', '--quiet', '--manifest-path',
                    os.path.join(HERE, 'decl_driver', 'Cargo.toml'), '--target-dir', TARGET], check=True)
    return exe


def measure(exe, emitted, analysis, flags=()):
    out = subprocess.run([exe, emitted, analysis] + list(flags), check=True, capture_output=True, text=True).stdout.split()
    d = dict(x.split('=') for x in out)
    return {k: (float(v) if k == 'rate' else int(v)) for k, v in d.items()}


def control(exe):
    ev = {}
    for r in csv.reader(open(os.path.join(CROWN, 'evaluation.tsv'))):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]))
    tot = [0, 0]
    for p in sorted(ev):
        for flags in ((), ('inline-mods',)):
            c = measure(exe, os.path.join(CROWN, p), os.path.join(CROWN, p, 'analysis_results'), flags)
            if (c['universe'], c['after']) != ev[p] or c['parse_failures']:
                sys.exit(f'control failed on {p} {flags}: {c} vs evaluation.tsv {ev[p]}; nothing written')
        tot[0] += ev[p][0]
        tot[1] += ev[p][1]
    return tot


def census_side(census, prog, universe):
    outcomes = SN.table(census, prog, 'subject-outcomes') or []
    subjects = {r['subject_key']: r for r in (SN.table(census, prog, 'subjects') or [])}
    by = defaultdict(list)
    for r in outcomes:
        k = re.sub(r'#\d+(@d\d+)?$', '', r['subject_key'])
        s = subjects.get(r['subject_key'], {})
        by[k].append({'delivery': r['delivery'], 'form': r.get('emitted_form', '-'),
                      'position': 'param' if s.get('arg_index') not in (None, '', '-') else 'local',
                      'reason': s.get('reason_detail') or s.get('reason') or '-'})
    delivered = {d for d in universe if by.get(d) and all(x['delivery'] == 'realized-as-predicted' for x in by[d])}
    return by, delivered


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--census', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--label', default='')
    a = ap.parse_args()
    exe = driver()
    ctl = control(exe)
    os.makedirs(a.out, exist_ok=True)
    rows, census_only, walker_only = [], [], []
    form_counts, why_counts, delivered_forms = Counter(), Counter(), Counter()
    for p in SN.PROGRAMS:
        universe = SN.crown_universe(p)
        tree = os.path.join(a.census, 'emitted-trees', p)
        if not os.path.isdir(tree):
            sys.exit(f'{p}: no emitted tree in {a.census}; nothing written (a typed failure is reported, not counted)')
        slots = os.path.join(a.out, f'{p}.walker-slots.tsv')
        w = measure(exe, tree, os.path.join(CROWN, p, 'analysis_results'), ('inline-mods', f'slots={slots}'))
        walker = {r['key']: r['walker'] for r in csv.DictReader(open(slots), delimiter='\t')}
        if set(walker) != universe:
            sys.exit(f'{p}: the walker universe differs from seed_numbers.crown_universe; nothing written')
        by, delivered = census_side(a.census, p, universe)
        safe = {k for k, c in walker.items() if c != 'none'}
        # the diagnostic (not CROWN's counter verbatim): the exposure wrapper's safe twin read under the C name
        slots_t = os.path.join(a.out, f'{p}.walker-slots-twin.tsv')
        measure(exe, tree, os.path.join(CROWN, p, 'analysis_results'), ('inline-mods', 'crat-twin', f'slots={slots_t}'))
        safe_t = {r['key'] for r in csv.DictReader(open(slots_t), delimiter='\t') if r['walker'] != 'none'}
        for k in delivered:
            for f in sorted({f"{x['position']}:{x['form']}" for x in by[k]}):
                delivered_forms[f] += 1
        for k in sorted(delivered - safe):
            forms = sorted({f"{x['position']}:{x['form']}" for x in by[k]})
            census_only.append({'program': p, 'key': k, 'census_forms': ','.join(forms)})
            for f in forms:
                form_counts[f] += 1
        for k in sorted(safe - delivered):
            d = by.get(k, [])
            why = ','.join(sorted({f"{x['delivery']}:{x['form']}" for x in d})) or 'no-census-subject'
            walker_only.append({'program': p, 'key': k, 'walker': walker[k], 'census': why,
                                'reasons': ';'.join(sorted({x['reason'] for x in d})) or '-'})
            why_counts[why] += 1
        rows.append({'program': p, 'before': len(universe), 'walker_ref': w['eliminated_ref'],
                     'walker_box': w['eliminated_box'], 'walker_after': w['after'],
                     'walker_rate': f"{100.0 * (w['eliminated_ref'] + w['eliminated_box']) / len(universe):.1f}%",
                     'census_delivered': len(delivered), 'census_rate': SN.pct(len(delivered), len(universe)),
                     'census_only': len(delivered - safe), 'walker_only': len(safe - delivered),
                     'twin_walker_safe': len(safe_t), 'twin_census_only': len(delivered - safe_t),
                     'twin_walker_only': len(safe_t - delivered),
                     'parse_failures': w['parse_failures']})
    tb = sum(r['before'] for r in rows)
    tw = sum(r['walker_ref'] + r['walker_box'] for r in rows)
    tc = sum(r['census_delivered'] for r in rows)
    with open(os.path.join(a.out, 'per-program.tsv'), 'w') as f:
        wr = csv.DictWriter(f, fieldnames=list(rows[0]), delimiter='\t', lineterminator='\n')
        wr.writeheader()
        wr.writerows(rows)
    for name, data in (('census-only.tsv', census_only), ('walker-only.tsv', walker_only)):
        with open(os.path.join(a.out, name), 'w') as f:
            if data:
                wr = csv.DictWriter(f, fieldnames=list(data[0]), delimiter='\t', lineterminator='\n')
                wr.writeheader()
                wr.writerows(data)
    summary = {'label': a.label, 'census': a.census, 'control': f'{ctl[0]} -> {ctl[1]} (20/20, plain and inline-mods)',
               'before': tb, 'walker_safe': tw, 'walker_rate': SN.pct(tw, tb), 'census_delivered': tc,
               'census_rate': SN.pct(tc, tb), 'census_only': len(census_only), 'walker_only': len(walker_only),
               'twin_walker_safe': sum(r['twin_walker_safe'] for r in rows),
               'twin_census_only': sum(r['twin_census_only'] for r in rows),
               'twin_walker_only': sum(r['twin_walker_only'] for r in rows),
               'census_delivered_forms': dict(delivered_forms.most_common()),
               'census_only_forms': dict(form_counts.most_common()), 'walker_only_census_side': dict(why_counts.most_common())}
    json.dump(summary, open(os.path.join(a.out, 'summary.json'), 'w'), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
