#!/usr/bin/env python3
"""relay 118 (analysis-fanout 095): Table 4's declaration column -- every raw-outermost declaration of the input,
counted safe when its depth-0 pointer layer(s) in the emitted program are all safe forms.

usage: alldecl.py            (reads only existing positions.tsv tables; writes per-program.json, decls-*.tsv here)

Inputs (read only):
  ours    r116/t4/out-ours-14u/ours/<p>/positions.tsv   (frame14u's emitted trees, the S25a run)
  input / crown / laertes   r065/out/{input,crown,laertes}/<p>/positions.tsv  (symlinks into r043, the 031a run)
  laertes libzahl           r117/out/laertes/libzahl/positions.tsv  (relay 117's adapted tree)
Rules imported from pos_census.py (docs agents/tools/rq2): RAW, SAFE, counted (byref out), dedupe_fields (fields once
per struct NAME, first module by path order), key / key_last (the T1 join: exact, unique-last-segment fallback),
twin_rows (ours), strip.
"""
import csv, json, os, re, sys
from collections import Counter, defaultdict

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import pos_census as P  # noqa: E402

AF = 'scratch/analysis-fanout'
HERE = os.environ['HERE']
CURSOR = {'cursor', 'cursor-mut', 'opt-cursor', 'opt-cursor-mut'}
SAFE_OUTER = P.SAFE | CURSOR
KINDS = ('param', 'return', 'local', 'field')
csv.field_size_limit(10**9)


def src(side, prog):
    if side == 'ours':
        return os.environ['OURSDIR'] + '/' + prog
    if side == 'laertes' and prog == 'libzahl':
        return f'{AF}/r117/out/laertes/libzahl'
    return f'{AF}/r065/out/{side}/{prog}'


def load(side, prog):
    d = src(side, prog)
    st = open(os.path.join(d, 'status.txt')).read().split('\t')[0].strip()
    if st != 'ok':
        return None, st
    return list(csv.DictReader(open(os.path.join(d, 'positions.tsv')), delimiter='\t')), 'ok'


def dkey(r):
    return P.key(r)[:4]


def dkey_last(r):
    return P.key_last(r)[:4]


def outer(rows):
    """The depth-0 pointer layers outside a function-pointer signature."""
    return [r['form'] for r in rows if r['depth'] == '0' and r['ctx'] != 'fnptr']


def group(rows):
    g = defaultdict(list)
    for r in rows:
        g[(dkey(r), r['owner'])].append(r)
    return g


def output_index(rows):
    """dkey -> the first output owner in file order (mimics P.delivered's setdefault); dkey_last -> owners."""
    first, last_owners, last_first = {}, defaultdict(set), {}
    for r in rows:
        first.setdefault(dkey(r), r['owner'])
        last_owners[dkey_last(r)].add(r['owner'])
        last_first.setdefault(dkey_last(r), (dkey(r), r['owner']))
    return first, last_owners, last_first


def population(prog):
    rin_all, st = load('input', prog)
    assert st == 'ok'
    g_all = group(rin_all)
    stats = Counter()
    # exclusions, per declaration (input as compiled, before dedupe)
    for (k, owner), rs in g_all.items():
        has_raw_outer = any(f in P.RAW for f in outer(rs))
        has_raw_any = any(r['form'] in P.RAW for r in rs)
        if k[0] == 'static':
            stats['static.decls'] += 1
            stats['static.raw-outer'] += has_raw_outer
            stats['static.raw-any'] += has_raw_any
            continue
        if rs[0]['binding'] == 'byref':
            stats['byref.decls'] += 1
            stats['byref.raw-any'] += any(r['form'] in P.RAW and r['ctx'] != 'fnptr' for r in rs)
            continue
    rin, dropped = P.dedupe_fields(P.counted(rin_all))
    stats['dup-field-layers-dropped'] = dropped
    pop = {}
    for (k, owner), rs in group(rin).items():
        if k[0] not in KINDS:
            continue
        o = outer(rs)
        raw_outer = any(f in P.RAW for f in o)
        raw_fnptr = any(r['form'] in P.RAW and r['ctx'] == 'fnptr' for r in rs)
        raw_nonfn = any(r['form'] in P.RAW and r['ctx'] != 'fnptr' for r in rs)
        if raw_outer:
            pop[k] = rs
            if any(f not in P.RAW for f in o):
                stats['pop.mixed-outer'] += 1
            if len(o) > 1:
                stats['pop.multi-outer'] += 1
        elif raw_fnptr and not raw_nonfn:
            stats['fnptr-only'] += 1
        elif raw_nonfn:
            stats['raw-below-safe-outer'] += 1      # D3 says 0
    return pop, stats


FRESH = re.compile(r'^fresh\d+$')


def judge(prog, side, pop):
    rows, st = load(side, prog)
    if rows is None:
        return None, st
    rows = P.counted(rows)
    if side == 'ours':
        rows = P.twin_rows(rows)
    g = group(rows)
    first, last_owners, last_first = output_index(rows)
    owners_out = {P.strip(r['owner']) for r in rows if r['kind'] != 'field'}
    res = {}
    for k, rs in pop.items():
        hit = None
        if k in first:
            hit, how = g[(k, first[k])], 'exact'
        else:
            kl = (k[0], k[1].rpartition('::')[2]) + k[2:] if k[0] != 'field' else k
            if len(last_owners.get(kl, ())) == 1:
                k2, o2 = last_first[kl]
                hit, how = g[(k2, o2)], 'last-segment'
        if hit is None:
            if k[0] == 'local' and FRESH.match(k[2]):
                cause = 'absent:fresh'
            elif k[0] != 'field' and k[1] not in owners_out and k[1].rpartition('::')[2] not in {
                    o.rpartition('::')[2] for o in owners_out}:
                cause = 'absent:owner-absent'
            else:
                cause = 'absent:other'
            res[k] = (False, cause, '')
            continue
        o = outer(hit)
        if not o:
            res[k] = (False, 'present:no-outer-pointer', how)
        elif all(f in SAFE_OUTER for f in o):
            res[k] = (True, 'safe:' + '+'.join(sorted(set(o))), how)
        else:
            res[k] = (False, 'raw:' + '+'.join(sorted(set(o))), how)
    return res, 'ok'


def main():
    out = {}
    for p in P.PROGRAMS:
        pop, stats = population(p)
        row = {'program': p, 'before': len(pop), 'stats': dict(stats),
               'kinds': dict(Counter(k[0] for k in pop))}
        for side in ('ours', 'crown', 'laertes'):
            res, st = judge(p, side, pop)
            row[f'{side}.status'] = st
            if res is None:
                continue
            row[f'{side}.safe'] = sum(1 for v in res.values() if v[0])
            row[f'{side}.causes'] = dict(Counter(v[1].split(':')[0] + (':' + v[1].split(':')[1] if v[1].startswith(('absent', 'present')) else '') for v in res.values()))
            row[f'{side}.absent'] = sum(1 for v in res.values() if v[1].startswith('absent'))
            row[f'{side}.last-segment'] = sum(1 for v in res.values() if v[2] == 'last-segment')
            row[f'{side}.safe-forms'] = dict(Counter(v[1] for v in res.values() if v[0]))
            with open(os.path.join(HERE, 'decls', f'{side}-{p}.tsv'), 'w') as f:
                f.write('kind\towner\tname\tidx\tinput_outer\tsafe\tcause\tjoin\n')
                for k in sorted(pop):
                    v = res[k]
                    f.write('\t'.join([*k, '+'.join(outer(pop[k])), 'yes' if v[0] else 'no', v[1], v[2]]) + '\n')
        out[p] = row
    json.dump(out, open(os.path.join(HERE, 'per-program.json'), 'w'), indent=1)
    for p, r in out.items():
        print(p, r['before'], *(f"{s}={r.get(s + '.safe', r[s + '.status'])}" for s in ('ours', 'crown', 'laertes')),
              'absent-ours', r['ours.absent'], r['stats'])


if __name__ == '__main__':
    os.makedirs(os.path.join(HERE, 'decls'), exist_ok=True)
    main()
