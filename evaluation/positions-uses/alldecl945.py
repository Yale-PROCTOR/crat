#!/usr/bin/env python3
"""relay 130 (R945-1, the USER, 10-10): Table 4's alldecl keys under CROWN's counter in full.

A population declaration (095 §1's 7,227, unchanged) is MADE SAFE in a tool's emitted program when its outermost
level there is not a raw pointer:
  (s) joined, every depth-0 non-fn-pointer layer a safe form or the cursor   (= the strict, pre-R945-1 rule)
  (n) joined, no depth-0 non-fn-pointer layer left (re-typed to a non-pointer)
  (a) absent from the emitted T1 table (no join) AND it has a counterpart in the tool's own BEFORE tree:
        ours / CROWN: the before tree is the shared input (benchmarks/rs-crown), so every population declaration has one;
        Laertes: the artifact's comparison/laertes-*/before tree, joined by the SAME join (exact key, then unique last
        segment) -- an input declaration with no counterpart there keeps 'not made safe' (counted per program).
  Raw at depth 0 (incl. [*mut T; N], Option<*mut T>, NonNull) stays RAW.
Types: the counter rq2_pos_counter is typed (rustc MIR types, alias-resolved): a declaration has a T1 row iff its
type has a pointer layer; an unannotated binding is judged by its MIR type, never by a syntactic reader.

Reuses r122/gtree/r118/alldecl.py (batch 56's copy of r118/stage/alldecl.py: population, group, output_index, outer,
load, the join) unchanged; only `src` is extended (side 'laertes_before'; 'input' re-pointable for the provenance
population measured on Laertes's own before tree).

usage: HERE=<this dir> OURSDIR=<...>/r122/gtree/t4/out-ours-56/ours python3 alldecl945.py
"""
import csv, importlib.util, json, os, re, statistics, sys
from collections import Counter, defaultdict

AF = 'scratch/analysis-fanout'
HERE = os.path.dirname(os.path.abspath(__file__))
os.environ['HERE'] = HERE
assert os.environ['OURSDIR']  # r133: set explicitly (batch58, or batch56 for the control)
spec = importlib.util.spec_from_file_location('alldecl', os.path.join(HERE, 'alldecl.py'))  # byte-identical copy of r122/gtree/r118/alldecl.py
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)
P = A.P

LB = f'{AF}/r116/t5/out/laertes_before'      # t4's out-laertes-before is byte-identical for the 18; + libzahl adapted
_src0 = A.src
INPUT_OVERRIDE = {}


def src(side, prog):
    if side == 'laertes_before':
        return f'{LB}/{prog}'
    if side == 'input' and prog in INPUT_OVERRIDE:
        return INPUT_OVERRIDE[prog]
    return _src0(side, prog)


A.src = src

LAERTES_LAERTES = ('bzip2', 'genann', 'libcsv', 'libzahl', 'lil', 'robotfindskitten', 'tulipindicators', 'urlparser')
CREDIT_FORMS = {'opt-raw-mut', 'opt-raw-const', 'nonnull', 'opt-nonnull'}


class Index:
    """The output side of A.judge's join, verbatim (exact key with the first output owner; else unique last segment)."""

    def __init__(self, rows):
        self.g = A.group(rows)
        self.first, self.last_owners, self.last_first = A.output_index(rows)

    def find(self, k):
        if k in self.first:
            return self.g[(k, self.first[k])], 'exact'
        kl = (k[0], k[1].rpartition('::')[2]) + k[2:] if k[0] != 'field' else k
        if len(self.last_owners.get(kl, ())) == 1:
            k2, o2 = self.last_first[kl]
            return self.g[(k2, o2)], 'last-segment'
        return None, ''


def rows_of(side, prog):
    rows, st = A.load(side, prog)
    if rows is None:
        return None, st
    rows = P.counted(rows)
    if side == 'ours':
        rows = P.twin_rows(rows)
    return rows, 'ok'


def depth0(rs):
    return [r for r in rs if r['depth'] == '0' and r['ctx'] != 'fnptr']


def credit_shape(rs):
    """Depth-0 layers Table 5's reading (CROWN's counter) credits and Table 4's does not."""
    tags = set()
    for r in depth0(rs):
        if r['form'] in P.RAW and r['form'] in CREDIT_FORMS:
            tags.add('option-raw' if r['form'].startswith('opt-raw') else 'nonnull')
        if r['form'] in P.RAW and r['ctx'] == 'elem':
            tags.add('array-of-raw')
        if r['form'] in P.RAW and r['ctx'] == 'arg':
            tags.add('generic-arg-raw')
    return sorted(tags)


def judge945(prog, side, pop, before_idx=None):
    """-> {k: (strict_safe, r945_safe, cls, join, credit_tags, out_type)}"""
    rows, st = rows_of(side, prog)
    if rows is None:
        return None, st
    idx = Index(rows)
    res = {}
    for k in pop:
        hit, how = idx.find(k)
        if hit is not None:
            o = A.outer(hit)
            ty = '; '.join(sorted({r['type'] for r in depth0(hit)}))
            if not o:
                res[k] = (False, True, 'n:present-no-outer-pointer', how, [], ty)
            elif all(f in A.SAFE_OUTER for f in o):
                res[k] = (True, True, 's:safe', how, [], ty)
            else:
                res[k] = (False, False, 'raw:' + '+'.join(sorted(set(o))), how, credit_shape(hit), ty)
            continue
        if side in ('ours', 'crown'):
            res[k] = (False, True, 'a:absent', '', [], '')
        else:
            bh, bhow = before_idx.find(k) if before_idx else (None, '')
            if bh is not None:
                res[k] = (False, True, 'a:absent-after-present-before', 'before:' + bhow, [], '')
            else:
                res[k] = (False, False, 'x:absent-after-no-before-counterpart', '', [], '')
    return res, 'ok'


# ------------------------------------------------------------------------------------------------ ours: source check
TREES = os.environ['TREES']  # r133: main/batch58 (or batch56 for the control)
FN = re.compile(r'^\s*(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?(?:extern\s+"C"\s+)?fn\s+(\w+)', re.M)
_bodies = {}


def bodies(prog):
    if prog not in _bodies:
        out = defaultdict(list)
        for f in sorted(__import__('glob').glob(f'{TREES}/{prog}/**/*.rs', recursive=True)):
            t = open(f, errors='replace').read()
            ms = list(FN.finditer(t))
            for i, m in enumerate(ms):
                end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
                out[m.group(1)].append(t[m.start():end])
        _bodies[prog] = out
    return _bodies[prog]


def ours_absent_source(prog, k):
    """Corroboration only (the verdict is the typed table's): what the emitted source holds for an absent declaration."""
    kind, owner, name, idx = k
    if kind == 'field':
        return 'field-absent', '-'
    fn = owner.rpartition('::')[2]
    texts = bodies(prog).get('__crat_safe_' + fn, []) + bodies(prog).get(fn, [])
    if not texts:
        return 'function-absent', '-'
    if kind == 'local':
        pat = re.compile(r'let\s+(?:mut\s+)?' + re.escape(name) + r'\b[^;\n]*')
        for t in texts:
            m = pat.search(t)
            if m:
                return 'kept-nonpointer', m.group(0).strip()
        return 'binding-removed', '-'
    # param / return of a function whose text exists: a body, or only a foreign declaration?
    has_body = any(re.match(r'[^;{]*\{', t, re.S) for t in texts)
    sig = re.sub(r'\s+', ' ', texts[0].split('{')[0].split(';')[0])[:160]
    return ('function-present-with-body' if has_body else 'foreign-declaration-only'), sig


def main():
    out, alld = {}, {}
    for p in P.PROGRAMS:
        pop, stats = A.population(p)
        row = {'program': p, 'before': len(pop)}
        lb_rows, lb_st = rows_of('laertes_before', p)
        lb_idx = Index(lb_rows) if lb_rows is not None else None
        row['laertes_before.status'] = lb_st
        dec = {}
        for side in ('ours', 'crown', 'laertes'):
            res, st = judge945(p, side, pop, lb_idx if side == 'laertes' else None)
            row[f'{side}.status'] = st
            if res is None:
                continue
            if side == 'ours':
                # a param / return whose function survives in the emitted program only as a FOREIGN declaration
                # (`extern "C" { fn atoi(__nptr: *const c_char) ... }`) keeps a counterpart whose outermost level is
                # raw: not removed, not made safe (the counter reads bodies, so it lists no row for it).
                for k, v in list(res.items()):
                    if v[2] == 'a:absent' and ours_absent_source(p, k)[0] == 'foreign-declaration-only':
                        res[k] = (False, False, 'raw:foreign-declaration', v[3], v[4], 'foreign signature')
            dec[side] = res
            row[f'{side}.strict'] = sum(v[0] for v in res.values())
            row[f'{side}.r945'] = sum(v[1] for v in res.values())
            row[f'{side}.cls'] = dict(Counter(v[2] for v in res.values()))
            row[f'{side}.credit'] = dict(Counter(t for v in res.values() for t in v[4]))
            row[f'{side}.credit_decls'] = sum(1 for v in res.values() if v[4])
            with open(os.path.join(HERE, 'decls', f'{side}-{p}.tsv'), 'w') as f:
                f.write('kind\towner\tname\tidx\tinput_outer\tstrict\tr945\tclass\tjoin\tcredit\tout_depth0_type'
                        + ('\tsource\temitted' if side == 'ours' else '') + '\n')
                for k in sorted(pop):
                    v = res[k]
                    extra = []
                    if side == 'ours':
                        extra = (list(ours_absent_source(p, k)) if v[2] in ('a:absent', 'raw:foreign-declaration')
                                 else ['-', '-'])
                    f.write('\t'.join([*k, '+'.join(A.outer(pop[k])), 'yes' if v[0] else 'no',
                                       'yes' if v[1] else 'no', v[2], v[3], ','.join(v[4]) or '-', v[5] or '-',
                                       *extra]) + '\n')
        # control: strict verdicts == batch 56's alldecl decls/*.tsv
        for side in dec:
            ref = {}
            for l in open(os.environ['CTL_DECLS'] + f'/{side}-{p}.tsv').read().splitlines()[1:]:
                c = l.split('\t')
                ref[tuple(c[:4])] = c[5] == 'yes'
            assert set(ref) == set(pop), (p, side)
            bad = [k for k in pop if ref[k] != dec[side][k][0]]
            assert not bad, (p, side, bad[:3])
        # provenance: Laertes's own figure, measured against its own before tree
        if lb_rows is not None and row['laertes.status'] == 'ok':
            INPUT_OVERRIDE[p] = f'{LB}/{p}'
            try:
                pop_lb, _ = A.population(p)
            finally:
                INPUT_OVERRIDE.pop(p)
            res_lb, _ = judge945(p, 'laertes', pop_lb, lb_idx)
            row['own.before'] = len(pop_lb)
            row['own.strict'] = sum(v[0] for v in res_lb.values())
            row['own.r945'] = sum(v[1] for v in res_lb.values())
            row['own.cls'] = dict(Counter(v[2] for v in res_lb.values()))
            # how the two populations meet (input declarations vs Laertes-before declarations, same join)
            inp_rows, _ = rows_of('input', p)
            in_idx = Index(inp_rows)
            row['own.pop_in_input'] = sum(1 for k in pop_lb if in_idx.find(k)[0] is not None)
            row['input.pop_in_lbefore'] = sum(1 for k in pop if lb_idx.find(k)[0] is not None)
        out[p] = row
        alld[p] = dec
    json.dump(out, open(os.path.join(HERE, 'per-program.json'), 'w'), indent=1)
    for p, r in out.items():
        print(p, r['before'], *(f"{s}={r.get(s + '.strict', r[s + '.status'])}->{r.get(s + '.r945', '')}"
                                for s in ('ours', 'crown', 'laertes')),
              'own:', r.get('own.before'), r.get('own.strict'), r.get('own.r945'))


if __name__ == '__main__':
    os.makedirs(os.path.join(HERE, 'decls'), exist_ok=True)
    main()
