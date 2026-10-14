#!/usr/bin/env python3
"""nbo_kinds.py <entries.tsv> <out.tsv> [prog...]: relay 067 item 4b -- NoOrigin by the kind of the origin-less value, at L01^13.

The forbidden set = each function's `no_borrow_origin` in the frame's model-cache entries (origin.functions[], streamed one
function at a time; never parsed whole). For each entry (function F, kind_slot S), a backward walk over F's occurrences
finds the values S may hold that have no origin (the leaves), following:
  * assignments tagged `transfer` (copies, casts, moves) to their source slots;
  * `borrow` (address-of): the address of a place reached through a pointer has that pointer's origins (walk the base);
    a base whose own value is a non-null constant is a static's address; the address of a local is not a leaf;
  * calls: a direct call to a program function G whose return slot is in G's no_borrow_origin -> walk G's return;
    Rust pointer methods (offset/add/cast/...) -> their first argument; a foreign C call -> `allocation` (malloc, calloc,
    realloc, strdup, strndup) or `foreign-call`; a call through a function pointer -> `indirect-call`;
  * for a field or deref slot behind a parameter: the stores into S in F, the callees G whose no_borrow_origin carries
    S too (walked in G), and, if neither explains it, an opaque call taking the parameter (`opaque-call-arg`).
Leaves `null` give nothing (null is not an origin-less value). A non-null constant is a `literal` when it is a string or
byte string, a `static-address` when it is the address of a static, else `nonnull-constant`; an `unrepresented` rvalue is
`computed`, an aggregate `aggregate`. An entry may have several leaf kinds; it is attributed to every kind it has and to
a single `primary` class: static-or-literal-only / call-or-allocation-only / mixed / other / unattributed."""
import collections, json, mmap, re, sys
sys.path.insert(0, 'scratch/analysis-fanout/r052')
from release_sites import items

C = 'worktrees/era5c-l01p13-night-solve/cache/era5b-model-cache-v1'
ALLOC = {'malloc', 'calloc', 'realloc', 'strdup', 'strndup', 'reallocarray', 'aligned_alloc'}
PTR_METHODS = re.compile(r'(offset|add|sub|wrapping_(add|sub|offset)|cast(_mut|_const)?|as_ptr|as_mut_ptr|byte_(add|sub|offset)|with_addr|map_addr)$')


def compress(o):
    sx = o.get('syntax') or {}
    e = sx.get('expression') or {}
    op = e.get('operand') or {}
    d = o.get('destination') or {}
    return (d.get('value') if d.get('state') == 'present' else None,
            o['kind'], sx.get('immediate_origin'), e.get('kind'),
            op.get('kind'), op.get('description'), op.get('zero'),
            [a['value'] for a in o.get('arguments', []) if a.get('state') == 'present'],
            (o.get('callee') or {}).get('kind'), (o.get('callee') or {}).get('target'),
            (e.get('place') or {}).get('local'), (e.get('place') or {}).get('projection'),
            (sx.get('destination') or {}).get('local'),
            [((x.get('place') or {}).get('local'), tuple(map(str, (x.get('place') or {}).get('projection') or [])))
             for x in (e.get('operands') or [])])


def const_kind(desc):
    d = desc or ''
    if re.search(r'b?"', d): return 'literal'
    if re.search(r'alloc\d|\{alloc|static|&', d): return 'static-address'
    return 'nonnull-constant'


def run(path):
    f = open(path, 'rb'); m = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    prog = re.search(rb'"program": *"([^"]+)"', m[:400]).group(1).decode()
    j = m.find(b'"origin":'); k = m.find(b'"functions":', j)
    defs, nbo, calls, localdefs = {}, {}, {}, {}
    for fn in items(m, k + len(b'"functions":')):
        F = fn['function']
        if fn.get('no_borrow_origin'): nbo[F] = fn['no_borrow_origin']
        dd = collections.defaultdict(list); cl = []; ld = collections.defaultdict(list)
        for o in fn['occurrences']:
            c = compress(o)
            if c[0]: dd[c[0]].append(c)
            if c[1] == 'call': cl.append(c)
            if c[12] is not None: ld[c[12]].append(c)
        defs[F] = dd; calls[F] = cl; localdefs[F] = ld
    m.close(); f.close()
    nbo_slots = {F: {e['kind_slot'].get('value') for e in es} for F, es in nbo.items()}
    field_owners = collections.defaultdict(list)
    for F, ss in nbo_slots.items():
        for x in ss:
            if '::field' in (x or ''): field_owners[x].append(F)

    def copies_of(F, r):
        R = {r}; changed = True
        while changed:
            changed = False
            for loc, cs in localdefs.get(F, {}).items():
                if loc in R: continue
                for c in cs:
                    srcs = [re.match(re.escape(F) + r'::_(\d+)@d0$', a) for a in c[7]]
                    if c[1] == 'assignment' and c[2] == 'transfer' and c[4] in ('copy', 'move') and srcs and all(m and int(m.group(1)) in R for m in srcs):
                        R.add(loc); changed = True; break
        return R

    def base_const(F, local):
        for c in localdefs.get(F, {}).get(local, []):
            if c[4] == 'constant' and c[6] is False: return const_kind(c[5])
        return None

    def walk(F, slot, seen, ex):
        if (F, slot) in seen or len(seen) > 400: return set()
        seen.add((F, slot)); out = set()
        for c in defs.get(F, {}).get(slot, []):
            dest, kind, imm, ek, opk, desc, zero, args, ck, tgt, plocal, pproj, dlocal, opnds = c
            if kind == 'call':
                if ck == 'foreign-c':
                    lab = 'allocation' if tgt in ALLOC else 'foreign-call'
                    out.add(lab); ex.setdefault(lab, (F, slot, tgt))
                elif ck == 'indirect':
                    out.add('indirect-call'); ex.setdefault('indirect-call', (F, slot, tgt))
                elif ck == 'local':
                    G = tgt; r = f'{G}::_0@d0'
                    if r in nbo_slots.get(G, ()): out |= walk(G, r, seen, ex)
                elif ck == 'rust-library':
                    if args and PTR_METHODS.search(tgt or ''): out |= walk(F, args[0], seen, ex)
                    else: out.add('library-call'); ex.setdefault('library-call', (F, slot, tgt))
                else:
                    out.add('call:' + str(ck))
            elif imm == 'null':
                continue
            elif imm == 'unknown':
                if opk == 'constant':
                    if zero: continue
                    lab = const_kind(desc); out.add(lab); ex.setdefault(lab, (F, slot, desc))
                elif ek == 'unrepresented': out.add('computed'); ex.setdefault('computed', (F, slot, desc))
                elif ek == 'aggregate': out.add('aggregate')
                elif ek == 'cast' and args:
                    sub = set()
                    for a in args: sub |= walk(F, a, seen, ex)
                    out |= (sub or {'cast'}); ex.setdefault('cast', (F, slot, 'unknown cast of ' + ','.join(args)))
                else: out.add('unknown:' + str(ek)); ex.setdefault('unknown:' + str(ek), (F, slot, desc))
            elif imm == 'borrow':
                if pproj and pproj[0] == 'Deref' and plocal is not None:
                    bc = base_const(F, plocal)
                    if bc: out.add(bc); ex.setdefault(bc, (F, slot, 'deref of const local _%d' % plocal))
                    else: out |= walk(F, f'{F}::_{plocal}@d0', seen, ex)
                # the address of a local: neither origin-less nor an origin
            else:
                for a in args: out |= walk(F, a, seen, ex)
                if not args and opk == 'constant' and not zero:
                    lab = const_kind(desc); out.add(lab); ex.setdefault(lab, (F, slot, desc))
        # a slot behind a parameter, stored in a callee that carries the same origin-less slot
        if not out:
            for c in calls.get(F, []):
                if c[8] == 'local' and slot in nbo_slots.get(c[9], ()) and c[9] != F:
                    out |= walk(c[9], slot, seen, ex)
        if not out and not defs.get(F, {}).get(slot):
            mm = re.match(r'(.*)::_(\d+)@d(\d+)$', slot)
            if mm and mm.group(1) == F and int(mm.group(3)) > 0:
                # a slot behind parameter _r: a callee that receives _r stores into its own slot
                r, dpt = int(mm.group(2)), mm.group(3)
                R = copies_of(F, r)
                for c in calls.get(F, []):
                    if c[8] != 'local': continue
                    for i, (loc, proj) in enumerate(c[13]):
                        if loc in R and not proj:
                            g = f'{c[9]}::_{i + 1}@d{dpt}'
                            if g in nbo_slots.get(c[9], ()): out |= walk(c[9], g, seen, ex)
            elif '::field' in slot:
                for G in field_owners.get(slot, ()):
                    if G != F: out |= walk(G, slot, seen, ex)
        return out

    rows = []
    for F, es in nbo.items():
        for e in es:
            S = e['kind_slot'].get('value'); ex = {}
            leaves = walk(F, S, set(), ex)
            if not leaves and e['root_dereferences'] > 0:
                root_local = e['root']; rl = re.match(r'.*::_(\d+)@d0$', root_local)
                for c in calls.get(F, []):
                    if c[8] in ('foreign-c', 'indirect') and (root_local in c[7] or (rl and any(loc in copies_of(F, int(rl.group(1))) for loc, _ in c[13]))):
                        leaves.add('opaque-call-arg'); ex.setdefault('opaque-call-arg', (F, S, c[9])); break
            rows.append((prog, F, S, e['root'], e['root_dereferences'], e.get('field') or '-', sorted(leaves), ex))
    return prog, rows


SL = {'static-address', 'literal'}
CA = {'allocation', 'foreign-call', 'indirect-call', 'library-call', 'opaque-call-arg'}
SL_OK = {'cast'}


def primary(leaves):
    s = set(leaves)
    if not s: return 'unattributed'
    if s <= SL | SL_OK and s & SL: return 'static-or-literal-only'
    if s <= CA: return 'call-or-allocation-only'
    if s & SL and s & CA: return 'mixed-static/literal+call'
    if s & SL: return 'static/literal+other'
    if s & CA: return 'call+other'
    return 'other-only'


if __name__ == '__main__':
    ent, out = sys.argv[1:3]; want = set(sys.argv[3:])
    w = open(out, 'w')
    w.write('program\tfunction\tslot\troot\troot_dereferences\tfield\tleaves\tprimary\texamples\n')
    for l in open(ent):
        p, size, fn = l.rstrip('\n').split('\t')
        if want and p not in want: continue
        prog, rows = run(f'{C}/{fn}')
        for r in rows:
            w.write('\t'.join(map(str, r[:6])) + '\t' + ','.join(r[6]) + '\t' + primary(r[6]) + '\t' + json.dumps(r[7])[:600] + '\n')
        w.flush()
        print(prog, len(rows), dict(collections.Counter(primary(r[6]) for r in rows)), file=sys.stderr, flush=True)
