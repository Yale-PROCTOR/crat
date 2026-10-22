"""Tables effect-all and effect-crown: every cited `rq1.*` / `rq2.*` key from the counters' tables.

Definitions:
  uses        T2 `full_roots` (every place rooted at a raw-pointer-typed local whose projection holds a Deref).
              before = the input's; a tool's rate = (input - tool) / input on the whole tree.
  alldecl     the population = every raw-outermost param / return / local / field of the input (byref bindings out,
              fields once per struct name, function-pointer-only layers out); a declaration is made safe when its
              depth-0 layers in the tool's output are all safe forms (or the cursor), when it holds no depth-0 pointer
              layer any more, or when it is absent from the output (removed). Joins: exact key, else the unique
              last path segment. Ours: absent counts as removed unless the function survives only as a foreign
              declaration; a last-segment join to another function's raw declaration while the declaration's own
              function is in the output is a mis-join and reads as removed. Laertes: absent counts as safe only when
              the declaration has a counterpart in Laertes's own before tree.
  decl        CROWN's population U = CROWN's fn_data keys at depth 0 labelled Mut and Ptr; before = |U| (= the input's
              raw bindings of U); a tool makes a key safe when none of its depth-0 bindings is still `*mut` / `*const`.
              Ours: the twin reading (`__jobcrat_safe_f`'s rows read as f's, the C-named wrapper's own rows dropped).
  decl-uses   CROWN's usage rule (`official`, rooted at a U key, with a Deref): before = CROWN's own count of record
              (its evaluation table); ours twin = (official on the input - official_raw on our tree) / official on
              the input; CROWN = its evaluation table; Laertes = (official on its before tree - official_raw on its
              after tree) / (official before + the input uses of U keys its translation does not hold).
  Laertes has no output for brotli (it crashes; CROWN's artifact ships none): its cells are 0.0 % and brotli counts
  as 0 made safe in the Laertes totals. libzahl's Laertes uses are compared over the functions both trees define (the
  Laertes tree inlines the headers in every module), and libzahl is outside the Laertes uses total.
  Totals are pooled: summed delivered over summed before. A rate over 0 is `---`."""
import os, re
from collections import defaultdict

import common as C

RAWF = {'raw-mut', 'raw-const', 'opt-raw-mut', 'opt-raw-const', 'nonnull', 'opt-nonnull'}
_base = {'ref', 'mut-ref', 'slice-ref', 'slice-mut', 'str-ref', 'box', 'box-slice'}
SAFEF = _base | {'opt-' + b for b in _base}
CUR = {'cursor', 'cursor-mut', 'opt-cursor', 'opt-cursor-mut'}
P = C.pct


def rate(a, b):
    return P(a, b) if b else '---'


def tail(s):
    return s.rpartition('::')[2]


def untwin(owner):
    h, _, t = owner.rpartition('::')
    if t.startswith(C.TW):
        return (h + '::' if h else '') + t[len(C.TW):], True
    return owner, False


def read_twin(rows):
    tw = {untwin(r['owner'])[0] for r in rows if untwin(r['owner'])[1]}
    out = []
    for r in rows:
        o, t = untwin(r['owner'])
        if not t and o in tw and r['kind'] in ('param', 'return', 'local'):
            continue
        out.append({**r, 'owner': o})
    return out


def nobyref(rows):
    return [r for r in rows if r['binding'] != 'byref']


def one_struct_copy(rows):
    first = {}
    for r in rows:
        if r['kind'] == 'field':
            n = tail(r['owner'])
            if n not in first or r['owner'] < first[n]:
                first[n] = r['owner']
    return [r for r in rows if r['kind'] != 'field' or first[tail(r['owner'])] == r['owner']]


def k6(r, short=False):
    if r['kind'] == 'field':
        o = tail(r['owner'])
    else:
        o = C.unsrc(r['owner'])
        if short:
            o = tail(o)
    return (r['kind'], o, r['name'], r['idx'] if r['kind'] in ('param', 'local') else '-', r['depth'], r['layer'])


def T(side, p, name, base=None):
    return C.tab(base or C.counted(side, p), name)


def all_population(rows):
    g = defaultdict(list)
    for r in one_struct_copy(nobyref(rows)):
        if r['kind'] in ('param', 'return', 'local', 'field'):
            g[k6(r)[:4]].append(r)
    return {k: rs for k, rs in g.items()
            if any(r['form'] in RAWF for r in rs if r['depth'] == '0' and r['ctx'] != 'fnptr')}


def finder(rows):
    grp, first, lown, lfirst = defaultdict(list), {}, defaultdict(set), {}
    for r in rows:
        k4 = k6(r)[:4]
        grp[(k4, r['owner'])].append(r)
        first.setdefault(k4, r['owner'])
        kl = k6(r, True)[:4]
        lown[kl].add(r['owner'])
        lfirst.setdefault(kl, (k4, r['owner']))

    def find(k4):
        if k4 in first:
            return grp[(k4, first[k4])], 'exact'
        kl = k4 if k4[0] == 'field' else (k4[0], tail(k4[1])) + k4[2:]
        if len(lown.get(kl, ())) == 1:
            return grp[lfirst[kl]], 'last'
        return None, None
    return find


def safe_rows(hit):
    o = [r['form'] for r in hit if r['depth'] == '0' and r['ctx'] != 'fnptr']
    return (not o) or all(f in SAFEF or f in CUR for f in o)


FNRE = re.compile(r'(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?(?:extern\s+"C"\s+)?fn\s+(\w+)')
_fn = {}


def foreign_only(tree, fn):
    if tree not in _fn:
        idx = defaultdict(list)
        for dp, _, fs in os.walk(tree):
            for f in sorted(fs):
                if f.endswith('.rs'):
                    t = open(os.path.join(dp, f), errors='replace').read()
                    ms = list(FNRE.finditer(t))
                    for i, m in enumerate(ms):
                        idx[m.group(1)].append(t[m.start():ms[i + 1].start() if i + 1 < len(ms) else len(t)])
        _fn[tree] = idx
    texts = _fn[tree].get(C.TW + fn, []) + _fn[tree].get(fn, [])
    if not texts:
        return False
    return not any(re.match(r'[^;{]*\{', t, re.S) for t in texts)


def alldecl_ours(p, pop):
    ro = read_twin(nobyref(T('ours', p, 'positions.tsv')))
    find = finder(ro)
    safe, lastj = 0, []
    for k4 in pop:
        hit, how = find(k4)
        if hit is not None:
            ok = safe_rows(hit)
            if how == 'last':
                lastj.append((k4, ok))
            safe += ok
            continue
        if k4[0] in ('param', 'return') and foreign_only(os.path.join(C.TREES, p), tail(k4[1])):
            continue
        safe += 1
    owners = {C.unsrc(r['owner']) for r in ro if r['kind'] != 'field'}
    return safe + sum(1 for k4, ok in lastj if not ok and k4[1] in owners)


def d0(rows, U, flat=False):
    out = defaultdict(list)
    for r in rows:
        if r['kind'] in ('param', 'local') and r['depth'] == '0' and r['layer'] == '0':
            kk = r['owner'] + '::' + r['name']
            kk = C.unsrc(kk) if flat else kk
            if kk in U:
                out[kk].append(r['type'])
    return out


def rawn(m):
    return sum(1 for ts in m.values() for t in ts if t.startswith(('*mut ', '*const ')))


def laertes_decl(p):
    """(made safe, |U_L|): |U_L| - the raw-outer bindings after - the keys with no counterpart before and no raw after."""
    if p == 'urlparser':
        base = os.path.join(C.WORK, 'urlparser-roottest')
        UL = {k[len('test::'):] if k.startswith('test::') else k for k in (C.unsrc(x) for x in C.universe(p))}
        A, B, fl = T('laertes', p, 'positions.tsv', f'{base}/laertes/{p}'), \
            T('laertes_before', p, 'positions.tsv', f'{base}/laertes_before/{p}'), True
    else:
        fl = open(os.path.join(C.counted('laertes', p), 'flat.txt')).read().strip() == 'flat'
        UL = {C.unsrc(x) for x in C.universe(p)} if fl else C.universe(p)
        A, B = T('laertes', p, 'positions.tsv'), T('laertes_before', p, 'positions.tsv')
    a, b = d0(A, UL, fl), d0(B, UL, fl)
    raw_after = {kk: sum(1 for t in ts if t.startswith(('*mut ', '*const '))) for kk, ts in a.items()}
    nocp = [kk for kk in UL if kk not in b and not raw_after.get(kk)]
    return len(UL) - sum(raw_after.values()) - len(nocp), len(UL)


def SMALL_OUT(p):
    return C.SMALL and p in C.LARGE


def measure():
    """{key: value} for every cited rq1 / rq2 key this table set carries; an unproduced key's value is
    `skipped (<why>)`. Also returns per-program rows for the CSV tables."""
    v, rows = {}, {p: {'program': p} for p in C.PROGS}
    ours, why = set(), {}
    for p in C.PROGS:
        st = C.status(C.counted('ours', p))
        if SMALL_OUT(p):
            why[p] = 'skipped (--small)'
        elif st == 'ok':
            ours.add(p)
        elif st in ('no-tree', 'no-run'):
            why[p] = 'skipped (no emitted tree)'
        else:
            why[p] = f'error (the typed counter failed on our tree: {st})'
    all_ours = len(ours) == len(C.PROGS)
    have_crown = all(C.have_crown(p) for p in C.PROGS) and all(
        C.status(C.counted('crown', p)) == 'ok' for p in C.PROGS)
    have_laertes = os.path.isdir(C.COMPARISON) and have_crown
    ctl = os.path.join(C.WORK, 'crown-control.txt')
    control_ok = os.path.exists(ctl) and open(ctl).read().startswith('ok')
    ev = C.evaluation()
    small = 'skipped (--small)' if C.SMALL else 'skipped (an emitted tree absent)'
    no_crown = 'skipped (no third-party: CROWN)'
    no_lae = 'skipped (no third-party: Laertes trees)'
    no_ctl = 'skipped (CROWN control ' + ('failed' if os.path.exists(ctl) and open(ctl).read().startswith('FAILED')
                                          else 'not run: CROWN outputs or evaluation table absent') + ')'

    # ------------------------------------------------ the input side, ours, CROWN and Laertes by program
    S = defaultdict(int)
    acc = defaultdict(dict)
    for p in C.PROGS:
        k = C.K(p)
        R = rows[p]
        inp_pos = T('input', p, 'positions.tsv')
        inp_use = T('input', p, 'uses.tsv')
        if inp_pos is None or inp_use is None:
            raise SystemExit(f'rq1: the typed counter did not complete on the input {p}')
        ui = sum(int(r['full_roots']) for r in inp_use)
        pop = all_population(inp_pos)
        R.update(uses_before=ui, alldecl_before=len(pop))
        v[f'rq1.{k}.uses.before'] = str(ui)
        v[f'rq1.{k}.alldecl.before'] = str(len(pop))
        S['ui'] += ui
        S['pop'] += len(pop)
        if p in ours:
            uo = sum(int(r['full_roots']) for r in T('ours', p, 'uses.tsv'))
            ad = alldecl_ours(p, pop)
            acc['uo'][p], acc['ad'][p] = uo, ad
            R.update(uses_ours=ui - uo, alldecl_ours=ad)
            v[f'rq1.{k}.uses.rate'] = rate(ui - uo, ui)
            v[f'rq1.{k}.alldecl.rate'] = rate(ad, len(pop))
        else:
            v[f'rq1.{k}.uses.rate'] = v[f'rq1.{k}.alldecl.rate'] = why[p]
        # CROWN's trees: uses and every-declaration columns
        if have_crown:
            cpos = nobyref(T('crown', p, 'positions.tsv'))
            uc = sum(int(r['full_roots']) for r in T('crown', p, 'uses.tsv'))
            fc = finder(cpos)
            c_safe = sum(safe_rows(h) if h is not None else True for h, _ in (fc(k4) for k4 in pop))
            acc['uc'][p], acc['ac'][p] = uc, c_safe
            R.update(uses_crown=ui - uc, alldecl_crown=c_safe)
            v[f'rq2.{k}.uses.crown'] = rate(ui - uc, ui)
            v[f'rq2.{k}.alldecl.crown'] = rate(c_safe, len(pop))
        else:
            v[f'rq2.{k}.uses.crown'] = v[f'rq2.{k}.alldecl.crown'] = no_crown
        # Laertes's distributed trees
        if have_laertes:
            if C.status(C.counted('laertes', p)) == 'no-tree':
                v[f'rq2.{k}.uses.laertes'] = v[f'rq2.{k}.alldecl.laertes'] = '0.0%'
                acc['al'][p] = 0
                R.update(uses_laertes='no output', alldecl_laertes='no output')
            else:
                lpos, luse = T('laertes', p, 'positions.tsv'), T('laertes', p, 'uses.tsv')
                if lpos is None or luse is None:
                    raise SystemExit(f'rq1: the typed counter did not complete on Laertes\'s tree of {p}')
                if p == 'libzahl':
                    fi, fo = defaultdict(int), defaultdict(int)
                    for x in inp_use:
                        fi[C.unsrc(x['function'])] += int(x['full_roots'])
                    for x in luse:
                        fo[C.unsrc(x['function'])] += int(x['full_roots'])
                    com = set(fi) & set(fo)
                    ji, jo = sum(fi[f] for f in com), sum(fo[f] for f in com)
                    v[f'rq2.{k}.uses.laertes'] = rate(ji - jo, ji)
                    R['uses_laertes'] = f'{ji - jo} of {ji} (the {len(com)} functions both trees define)'
                else:
                    ul = sum(int(r['full_roots']) for r in luse)
                    acc['ul'][p] = ul
                    v[f'rq2.{k}.uses.laertes'] = rate(ui - ul, ui)
                    R['uses_laertes'] = ui - ul
                fl, fb = finder(nobyref(lpos)), finder(nobyref(T('laertes_before', p, 'positions.tsv')))
                l_safe = 0
                for k4 in pop:
                    h, _ = fl(k4)
                    l_safe += safe_rows(h) if h is not None else (fb(k4)[0] is not None)
                acc['al'][p] = l_safe
                R['alldecl_laertes'] = l_safe
                v[f'rq2.{k}.alldecl.laertes'] = rate(l_safe, len(pop))
        else:
            v[f'rq2.{k}.uses.laertes'] = v[f'rq2.{k}.alldecl.laertes'] = no_lae

        # ------------------------------------------------ CROWN's population (Table effect-crown)
        if not control_ok:
            for key in (f'rq1.{k}.decl.before', f'rq1.{k}.decl-uses.before', f'rq1.{k}.decl-twin.rate',
                        f'rq1.{k}.decl-uses-twin.rate', f'rq2.{k}.decl-uses.crown', f'rq2.{k}.decl-uses.laertes'):
                v[key] = no_ctl
            v[f'rq2.{k}.decl.crown'] = v[f'rq2.{k}.decl.laertes'] = no_ctl
            continue
        U = C.universe(p)
        B = rawn(d0(inp_pos, U))
        if B != len(U):
            raise SystemExit(f'rq1: {p}: the input\'s raw bindings of CROWN\'s population ({B}) != |U| ({len(U)})')
        i25 = sum(int(r['official']) for r in inp_use)
        acc['U'][p], acc['i25'][p] = len(U), i25
        v[f'rq1.{k}.decl.before'] = str(len(U))
        v[f'rq1.{k}.decl-uses.before'] = str(ev[p][2])
        R.update(decl_before=len(U), decl_uses_before=ev[p][2], decl_uses_input_2025=i25)
        craw = rawn(d0(T('crown', p, 'positions.tsv'), U))
        acc['dc'][p] = len(U) - craw
        v[f'rq2.{k}.decl.crown'] = rate(len(U) - craw, len(U))
        b23, a23 = ev[p][2], ev[p][3]
        acc['eb'][p], acc['ea'][p] = b23, a23
        v[f'rq2.{k}.decl-uses.crown'] = rate(b23 - a23, b23)
        R.update(decl_crown=len(U) - craw, decl_uses_crown=f'{b23} -> {a23}')
        if p in ours:
            ro = T('ours', p, 'positions.tsv')
            tw = rawn(d0(read_twin(ro), U))
            rem_tw = sum(int(r['official_raw']) for r in T('ours', p, 'uses.tsv'))
            acc['dt'][p], acc['rt'][p] = len(U) - tw, rem_tw
            v[f'rq1.{k}.decl-twin.rate'] = rate(len(U) - tw, len(U))
            v[f'rq1.{k}.decl-uses-twin.rate'] = rate(i25 - rem_tw, i25)
            R.update(decl_ours_twin=len(U) - tw, decl_uses_ours_twin=i25 - rem_tw)
        else:
            v[f'rq1.{k}.decl-twin.rate'] = v[f'rq1.{k}.decl-uses-twin.rate'] = why[p]
        if not have_laertes:
            v[f'rq2.{k}.decl.laertes'] = v[f'rq2.{k}.decl-uses.laertes'] = no_lae
        elif C.status(C.counted('laertes', p)) == 'no-tree':
            v[f'rq2.{k}.decl.laertes'] = v[f'rq2.{k}.decl-uses.laertes'] = '0.0%'
            acc['dl'][p] = 0
            R.update(decl_laertes='no output', decl_uses_laertes='no output')
        else:
            made, ul_ = laertes_decl(p)
            acc['dl'][p] = made
            v[f'rq2.{k}.decl.laertes'] = rate(made, ul_)
            if p == 'urlparser':
                base = os.path.join(C.WORK, 'urlparser-roottest')
                lb = sum(int(r['official']) for r in T('', p, 'uses.tsv', f'{base}/laertes_before/{p}'))
                la = sum(int(r['official_raw']) for r in T('', p, 'uses.tsv', f'{base}/laertes/{p}'))
                lU = 0
            else:
                lb = sum(int(r['official']) for r in T('laertes_before', p, 'uses.tsv'))
                la = sum(int(r['official_raw']) for r in T('laertes', p, 'uses.tsv'))
                unb = set(open(os.path.join(C.counted('laertes_before', p), 'universe-unmapped.txt')).read().split())
                una = set(open(os.path.join(C.counted('laertes', p), 'universe-unmapped.txt')).read().split())
                if unb != una:
                    raise SystemExit(f'rq1: {p}: Laertes before / after leave different universe keys unmapped')
                lU = 0
                if unb:
                    byfn = defaultdict(list)
                    for q in U:
                        byfn[q.rsplit('::', 1)[0]].append(C.unsrc(q) in unb or q in unb)
                    iu = {x['function']: int(x['official']) for x in inp_use}
                    lU = sum(iu.get(f, 0) for f, fl_ in byfn.items() if all(fl_))
            acc['lb'][p], acc['la'][p], acc['lU'][p] = lb, la, lU
            v[f'rq2.{k}.decl-uses.laertes'] = rate(lb - la, lb + lU)
            R.update(decl_laertes=made, decl_uses_laertes=f'{lb - la} of {lb + lU}')

    # ------------------------------------------------ totals (pooled over the twenty)
    v['rq1.total.uses.before'] = str(S['ui'])
    v['rq1.total.alldecl.before'] = str(S['pop'])
    ui = {p: rows[p]['uses_before'] for p in C.PROGS}
    pop = {p: rows[p]['alldecl_before'] for p in C.PROGS}
    if all_ours:
        v['rq1.total.uses.rate'] = rate(S['ui'] - sum(acc['uo'].values()), S['ui'])
        v['rq1.total.alldecl.rate'] = rate(sum(acc['ad'].values()), S['pop'])
    else:
        v['rq1.total.uses.rate'] = v['rq1.total.alldecl.rate'] = small
    if have_crown:
        v['rq2.total.uses.crown'] = rate(S['ui'] - sum(acc['uc'].values()), S['ui'])
        v['rq2.total.alldecl.crown'] = rate(sum(acc['ac'].values()), S['pop'])
    else:
        v['rq2.total.uses.crown'] = v['rq2.total.alldecl.crown'] = no_crown
    if have_laertes:
        n18 = [p for p in C.PROGS if p in acc['ul']]           # brotli (no output) and libzahl (function join) out
        v['rq2.total.uses.laertes'] = rate(sum(ui[p] - acc['ul'][p] for p in n18),
                                           sum(ui[p] for p in n18) + ui['brotli'])
        v['rq2.total.alldecl.laertes'] = rate(sum(acc['al'].values()), S['pop'])
    else:
        v['rq2.total.uses.laertes'] = v['rq2.total.alldecl.laertes'] = no_lae
    if control_ok:
        TU = sum(acc['U'].values())
        TI = sum(acc['i25'].values())
        v['rq1.total.decl.before'] = str(TU)
        v['rq1.total.decl-uses.before'] = str(sum(acc['eb'].values()))
        v['rq2.total.decl.crown-rate'] = rate(sum(acc['dc'].values()), TU)
        v['rq2.total.decl-uses.crown'] = rate(sum(acc['eb'].values()) - sum(acc['ea'].values()), sum(acc['eb'].values()))
        if all_ours:
            v['rq1.total.decl-twin.rate'] = rate(sum(acc['dt'].values()), TU)
            v['rq1.total.decl-uses-twin.rate'] = rate(TI - sum(acc['rt'].values()), TI)
        else:
            v['rq1.total.decl-twin.rate'] = v['rq1.total.decl-uses-twin.rate'] = small
        if have_laertes:
            v['rq2.total.decl.laertes-rate'] = rate(sum(acc['dl'].values()), TU)
            ln = sum(acc['lb'][p] - acc['la'][p] for p in acc['lb'])
            ld = sum(acc['lb'][p] + acc['lU'][p] for p in acc['lb'])
            br = acc['i25']['brotli'] if 'brotli' not in acc['lb'] else 0
            v['rq2.total.decl-uses.laertes'] = rate(ln, ld + br)
        else:
            v['rq2.total.decl.laertes-rate'] = v['rq2.total.decl-uses.laertes'] = no_lae
    else:
        for key in ('rq1.total.decl.before', 'rq1.total.decl-uses.before', 'rq2.total.decl.crown-rate',
                    'rq2.total.decl-uses.crown', 'rq1.total.decl-twin.rate', 'rq1.total.decl-uses-twin.rate',
                    'rq2.total.decl.laertes-rate', 'rq2.total.decl-uses.laertes'):
            v[key] = no_ctl
    return v, [rows[p] for p in C.PROGS]
