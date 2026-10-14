#!/usr/bin/env python3
"""strata_d6.py (analysis-fanout 112, relay 138: copy of r133 strata.py; ONLY change: D6 -- in_u also admits a subject whose census
decision is a safe form, and owning.decided also counts family raw with census decision box, whatever the outcome)
strata.py <census-dir> <solve-dir> [--r454 TSV] [--out OUT.tsv] [--rows ROWS.tsv]

analysis-fanout relay 108, group 3: the RQ1 breadth strata of Appendix E (tab:rq1-strata) at a frame census.
READ-ONLY: reads the census dir, the solve dir's workers/<p>.json -> its cache entry's HEAD only (universe + model, through
r100's bounded reader model_head.py; the GB-sized tail is never read), and the R454 exclusion list in the docs repo.

The decided-safe universe U (rq1.frame14.safe-decisions' recipe; = rq5_forms.py's universe):
  census subjects with family in {ref, slice, optional, box, cursor} or delivery == realized-as-predicted,
  less the R454 `let ref mut` bindings (counts_toward_N == true) and any `universe-exclusion*` row.

Strata computed here (others are dispositions (b)/(c)/(d), see the report):
  owning  (Owning locals and parameters; frozen denominator: allocation-rooted declarations)
     decided   = U ∩ (family box, or family raw delivered with emitted_form box)          [= rq5 box + boxslice decided]
     delivered = decided ∩ realized-as-predicted                                         [= rq1.frame14.delivered-box]
     cand      = in-scope modeled subjects (not unmodeled, not R454) carrying allocation evidence in this census:
                 model_kind owning (d0) | decided owning | reason/exclusion starting return-certificate / contract-allocation
                 / box- | named in <p>.raw-boundary-allocator-contract-receipt.tsv (fn::binding join)
  fields  (Owning fields; frozen denominator: program-defined pointer fields)
     cand      = model field slots at depth 0 (`<struct>::field<i>[::element]@d0`) whose struct is not a libc/system
                 struct (the 2026-09-05 sizing read's 144-slot split: _IO_FILE, __sFILE, __sbuf, _IO_marker,
                 _RuneLocale, _RuneEntry, _RuneRange, __va_list_tag, _win_st)
     decided   = cand with model kind owning
     delivered = <p>.raw-boundary-field-transactions.tsv rows status=applied, revert_status=active, form containing
                 `box`, on a struct that has model field slots (function-local arrays excluded)
  depth   (Nested pointer depth; frozen denominator: inner-depth slots behind a safe outer)
     cand      = inner (d1) slots of (i) subjects in U with ptr_depth 2 (each has exactly one inner slot; no subject has
                 depth 3), plus (ii) field d1 slots whose d0 slot the model decides ref/owning
     decided   = cand whose inner slot the model decides ref/owning
     delivered = (i) subjects delivered whose emitted declaration (<p>.raw-boundary-delivery-declarations.json, the
                 `__crat_safe_` twin read as its function) is safe at BOTH levels: the type under the outer
                 &/&mut/[]/Option/Box is itself &/&mut/[]/Option<&|Box>/Box, type aliases resolved from the emitted tree
                 (`pub type X = *mut ..` is raw); (ii) fields: none (no field transaction delivers a nested form)
  outparam decided  = pointer formals (census subjects with arg_index, ptr_depth >= 2) whose inner slot (d1..) the model
                 decides owning (an owning pointee handed back through the formal)
           delivered = census subjects whose decision or emitted_form names an out-parameter form (vocabulary check)
           cand: not computed (no census instrument records out-parameter candidates or their dataflow derivation).
"""
import argparse, collections, csv, glob, json, os, re, sys

csv.field_size_limit(1 << 30)
sys.path.insert(0, 'scratch/analysis-fanout/r100/keymap')
from model_head import read_head  # noqa: E402  bounded prefix reader (universe + model only)

R454_DEFAULT = 'docs/agents/artifacts/2026-09-18-universe-exclusion-r454/ref-mut-bindings-51.tsv'
SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
SAFE_KIND = {'ref', 'owning'}
LIBC_STRUCTS = {'_IO_FILE', '__sFILE', '__sbuf', '_IO_marker', '_RuneLocale', '_RuneEntry', '_RuneRange',
                '__va_list_tag', '_win_st'}
FIELD_RE = re.compile(r'^(?P<owner>.+)::field(?P<idx>\d+)(?P<elem>::element)?@d(?P<depth>\d+)$')
ALLOC_REASON = ('return-certificate', 'contract-allocation', 'box-')


def tsv(path):
    with open(path, newline='') as f:
        return list(csv.DictReader(f, delimiter='\t', quoting=csv.QUOTE_NONE))


def model_of(solve, p):
    w = json.load(open(f'{solve}/workers/{p}.json'))
    entry = w['completed']['cache_entry']
    if not os.path.exists(entry):  # the solve dir may have moved; same basename under its cache dir
        entry = f'{solve}/cache/era5b-model-cache-v1/{os.path.basename(entry)}'
    prog, _u, model, _n = read_head(entry)
    assert prog in (None, p), (prog, p)
    return model


def split_type(t):
    """One outer safe layer off a rendered type; returns (outer_is_safe, inner) or (False, t)."""
    t = t.strip()
    for pre in ('Option<', '::std::option::Option<', 'core::option::Option<', 'std::option::Option<'):
        if t.startswith(pre) and t.endswith('>'):
            ok, inner = split_type(t[len(pre):-1])
            return ok, inner
    for pre in ('Box<', '::std::boxed::Box<', 'std::boxed::Box<'):
        if t.startswith(pre) and t.endswith('>'):
            body = t[len(pre):-1].strip()
            if body.startswith('[') and body.endswith(']'):
                return True, body[1:-1].strip()
            return True, body
    if t.startswith('&'):
        body = t[1:].lstrip()
        if body.startswith("'"):
            body = body.split(None, 1)[1]
        if body.startswith('mut '):
            body = body[4:].lstrip()
        if body.startswith('[') and body.endswith(']'):
            return True, body[1:-1].strip()
        return True, body
    return False, t


def safe_level(t, aliases, depth=0):
    """Is this (inner) type itself a safe pointer level? aliases: name -> rendered target."""
    t = t.strip()
    if t.startswith('*'):
        return False
    if t.startswith(('&', '[', 'Box<', '::std::boxed::Box<', 'std::boxed::Box<')):
        return True
    if t.startswith(('Option<', '::std::option::Option<', 'core::option::Option<', 'std::option::Option<')):
        body = t[t.index('<') + 1:-1].strip()
        return safe_level(body, aliases, depth + 1)
    name = t.split('::')[-1]
    if name in aliases and depth < 5:
        return safe_level(aliases[name], aliases, depth + 1)
    return False


def tree_aliases(census, p):
    out = {}
    for f in glob.glob(f'{census}/emitted-trees/{p}/**/*.rs', recursive=True):
        for m in re.finditer(r'\btype\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([^;]+);', open(f, errors='replace').read()):
            out.setdefault(m.group(1), m.group(2).strip())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('census')
    ap.add_argument('solve')
    ap.add_argument('--r454', default=R454_DEFAULT)
    ap.add_argument('--out')
    ap.add_argument('--rows')
    a = ap.parse_args()
    C, S = a.census.rstrip('/'), a.solve.rstrip('/')
    excl = {(r['program'], r['owner'], r['binding']) for r in tsv(a.r454) if r['counts_toward_N'] == 'true'}
    progs = sorted(os.path.basename(f).split('.raw-boundary-subject-outcomes.tsv')[0]
                   for f in glob.glob(f'{C}/*.raw-boundary-subject-outcomes.tsv'))
    n = collections.Counter()
    brk = collections.Counter()
    rows = []
    for p in progs:
        model = model_of(S, p)
        subj = {r['subject_key']: r for r in tsv(f'{C}/{p}.raw-boundary-subjects.tsv')}
        # allocator-contract receivers (fn-short::binding)
        acr = collections.Counter()
        acp = f'{C}/{p}.raw-boundary-allocator-contract-receipt.tsv'
        if os.path.exists(acp):
            for r in tsv(acp):
                s = r.get('subject') or ''
                if '::' in s:
                    acr[tuple(s.split('::')[-2:])] += 1
        decls = collections.defaultdict(list)
        ddp = f'{C}/{p}.raw-boundary-delivery-declarations.json'
        if os.path.exists(ddp):
            for _f, x in json.load(open(ddp))['declarations']:
                decls[x['owner']].append(x)
        aliases = None
        for o in tsv(f'{C}/{p}.raw-boundary-subject-outcomes.tsv'):
            k = o['subject_key']
            s = subj.get(k, {})
            fam = s.get('family', o['family'])
            m = re.match(r'(.*)::([^:#]+)#(\d+)$', k)
            if not m:
                continue  # unmodeled `arg#K@d0` rows
            owner, name, local = m.group(1), m.group(2), m.group(3)
            if fam == 'unmodeled' or (p, o['owner_fn'], name) in excl or o['exclusion'].startswith('universe-exclusion'):
                continue
            dlv = o['delivery'] == 'realized-as-predicted'
            in_u = fam in SAFE or dlv or s.get('decision') in SAFE  # D6 (relay 138)
            # ---- owning --------------------------------------------------------------------------------
            own_dec = in_u and (fam == 'box' or (fam == 'raw' and dlv and o['emitted_form'] == 'box')
                                or (fam == 'raw' and not dlv and s.get('decision') == 'box'))  # D6
            reason = s.get('reason', '-')
            ev = []
            if s.get('model_kind') == 'owning':
                ev.append('model-owning')
            if own_dec:
                ev.append('decided-owning')
            if reason.startswith(ALLOC_REASON) or o['exclusion'].startswith(ALLOC_REASON):
                ev.append('alloc-reason')
            if acr.get((owner.split('::')[-1], name)):
                ev.append('allocator-contract-receipt')
            if ev:
                n['owning.cand'] += 1
                brk['owning.cand.' + ('+'.join(ev))] += 1
            if own_dec:
                n['owning.decided'] += 1
                n['owning.delivered'] += dlv
            # ---- depth (subjects) -------------------------------------------------------------------------
            if in_u and s.get('ptr_depth') == '2':
                inner = model.get(f'{owner}::_{local}@d1', 'not-in-model')
                n['depth.cand'] += 1
                n['depth.cand.subject'] += 1
                dec = inner in SAFE_KIND
                n['depth.decided'] += dec
                whole = False
                rt = '-'
                if dlv:
                    pre, last = owner.rsplit('::', 1) if '::' in owner else ('', owner)
                    twin = (pre + '::' if pre else '') + '__crat_safe_' + last
                    for ow in (twin, owner):
                        hit = [x for x in decls.get(ow, [])
                               if (s['arg_index'] != '-' and x['parameter_index'] is not None
                                   and str(x['parameter_index']) == s['arg_index'])
                               or (s['arg_index'] == '-' and x['parameter_index'] is None and x['binding'] == name)]
                        if hit:
                            rt = hit[0]['rendered_type']
                            break
                    if aliases is None:
                        aliases = tree_aliases(C, p)
                    ok, inner_t = split_type(rt) if rt != '-' else (False, '')
                    whole = ok and safe_level(inner_t, aliases)
                    n['depth.outer-delivered'] += 1
                    if rt == '-':
                        n['depth.outer-delivered.no-declaration-found'] += 1
                if whole:
                    n['depth.delivered'] += 1
                    if not dec:
                        n['depth.delivered.inner-model-not-safe'] += 1
                rows.append(['depth', p, k, fam, o['delivery'], inner, rt, 'whole-chain' if whole else
                             ('outer-only' if dlv else 'outer-not-delivered')])
            # ---- outparam: owning pointee behind a pointer formal (model) + out-param form (census vocabulary) --
            if s.get('arg_index', '-') != '-' and s.get('ptr_depth', '1') not in ('', '-', '1'):
                n['outparam.formals-depth2plus'] += 1
                if any(model.get(f'{owner}::_{local}@d{d}') == 'owning' for d in range(1, int(s['ptr_depth']))):
                    n['outparam.decided'] += 1
            if 'out' in (s.get('decision', '') + o['emitted_form']).lower():
                n['outparam.delivered'] += 1
        # ---- fields ----------------------------------------------------------------------------------------
        field_structs = set()
        for slot, kind in model.items():
            fm = FIELD_RE.match(slot)
            if not fm:
                continue
            field_structs.add(fm['owner'])
            struct = fm['owner'].split('::')[-1]
            if fm['depth'] == '0':
                n['fields.all-d0'] += 1
                if struct in LIBC_STRUCTS:
                    n['fields.libc-d0'] += 1
                    continue
                n['fields.cand'] += 1
                n['fields.decided'] += kind == 'owning'
                brk[f'fields.cand.{kind}'] += 1
            elif fm['depth'] == '1':
                d0 = model.get(slot[:-len('@d1')] + '@d0')
                if d0 in SAFE_KIND:
                    n['depth.cand'] += 1
                    n['depth.cand.field'] += 1
                    n['depth.decided'] += kind in SAFE_KIND
                rows.append(['depth-field', p, slot, '-', '-', kind, f'd0={d0}', '-'])
        for r in tsv(f'{C}/{p}.raw-boundary-field-transactions.tsv'):
            if r['status'] == 'applied' and r['revert_status'] == 'active':
                tag = 'struct' if r['struct'] in field_structs else 'function-local-array'
                brk[f'fields.applied-active.{tag}.{r["form"]}'] += 1
                if tag == 'struct' and 'box' in r['form']:
                    n['fields.delivered'] += 1
                    rows.append(['fields-delivered', p, f'{r["struct"]}.{r["field"]}', '-', 'applied/active', '-',
                                 r['form'], '-'])
        print(p, 'done', file=sys.stderr, flush=True)
    keys = ['owning.cand', 'owning.decided', 'owning.delivered', 'fields.cand', 'fields.decided', 'fields.delivered',
            'depth.cand', 'depth.decided', 'depth.delivered', 'outparam.decided', 'outparam.delivered']
    for k in keys:
        print(f'rq1.strata.{k}\t{n[k]}')
    print('# counters', dict(sorted(n.items())))
    print('# breakdown', dict(sorted(brk.items())))
    if a.out:
        with open(a.out, 'w') as w:
            w.write('key\tvalue\tprovenance\n')
            for k in keys:
                w.write(f'rq1.strata.{k}\t{n[k]}\tstrata.py {C} {S} (analysis-fanout r108 g3)\n')
    if a.rows:
        with open(a.rows, 'w') as w:
            w.write('stratum\tprogram\tidentity\tfamily\tdelivery\tinner_model_kind\temitted_type\tchain\n')
            for r in rows:
                w.write('\t'.join(map(str, r)) + '\n')


if __name__ == '__main__':
    main()
