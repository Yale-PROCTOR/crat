"""r130/t5: CROWN's declaration test (R945-1) over the typed counter's positions.tsv.

CROWN's binary (crown-artifact/src/bin/evaluation.rs:80-124): per top-level fn item not named
borrow/borrow_mut/owned_as_ref/owned_as_mut/option_to_raw/_ref_eq/_ref_ne/main, per MIR local that
is a user variable (param or let binding) whose OWN type is a raw pointer (is_unsafe_ptr = the outermost
constructor is RawPtr), count one if the input JSON's [0] qualifiers (looked up by fn path + name) are Mut and Ptr.
The 'after' column runs the same count on the emitted program with the INPUT's JSON; made safe = before - after.
So a binding that is gone, re-typed to a non-pointer, Option<*mut>, [*mut; N], NonNull, &mut *mut ... is not counted.

Here: one counted binding = one positions.tsv row with kind in {param, local}, depth 0, layer 0, the declared
(typeck) type's printed form starting with '*' (RawPtr outermost), and fn::name in the universe U (CROWN's
2,414 fn_data d0 Mut∩Ptr keys). Shadowed bindings count once each (per MIR local, as CROWN's binary).
A binding with no pointer layer produces no row (pos_counter t1: rows only when layers non-empty) and so is not
counted, as CROWN's binary does not count it."""
import csv, os
csv.field_size_limit(10**9)
SKIP = {'borrow', 'borrow_mut', 'owned_as_ref', 'owned_as_mut', 'option_to_raw', '_ref_eq', '_ref_ne', 'main'}
TWIN = '__crat_safe_'


def strip(k):
    return k[5:] if k.startswith('src::') else k


def rows(path):
    return list(csv.DictReader(open(path), delimiter='\t'))


def detwin(owner):
    head, _, last = owner.rpartition('::')
    if last.startswith(TWIN):
        return (head + '::' if head else '') + last[len(TWIN):], True
    return owner, False


def twin_rows(rs):
    """pos_census.twin_rows verbatim: __crat_safe_<f>'s rows read as <f>'s, the C-named wrapper's dropped."""
    twinned = {detwin(r['owner'])[0] for r in rs if detwin(r['owner'])[1]}
    out = []
    for r in rs:
        o, is_twin = detwin(r['owner'])
        if r['kind'] in ('param', 'return', 'local') and o in twinned and not is_twin:
            continue
        out.append(dict(r, owner=o))
    return out


def depth0(rs, U, flat=False, twin=False, asemitted=False):
    """{key: [(binding id, form, ctx, type)]} for every param/local binding at depth 0 layer 0 whose key is in U."""
    if twin:
        rs = twin_rows(rs)
    elif asemitted:
        rs = asemitted_rows(rs)
    out = {}
    for r in rs:
        if r['kind'] not in ('param', 'local') or r['depth'] != '0' or r['layer'] != '0':
            continue
        if r['owner'].rpartition('::')[2] in SKIP:
            continue
        k = f"{r['owner']}::{r['name']}"
        k = strip(k) if flat else k
        if k in U:
            out.setdefault(k, []).append(((r['kind'], r['owner'], r['name'], r['idx']), r['form'], r['ctx'], r['type']))
    return out


def is_raw_outer(ty):
    return ty.startswith('*mut ') or ty.startswith('*const ')


def crown_count(d0):
    """CROWN's per-MIR-local count: the bindings whose outermost constructor is a raw pointer."""
    return {k: sum(1 for b in v if is_raw_outer(b[3])) for k, v in d0.items()}


def shape(b):
    """The item-2 shapes of a non-raw-outermost binding (which Table 4 would still read raw)."""
    _, form, ctx, ty = b
    if form.startswith('opt-raw'):
        return 'option-raw'
    if form in ('nonnull', 'opt-nonnull'):
        return 'nonnull'
    if form.startswith('raw') and ctx == 'elem':
        return 'array-raw'
    if form.startswith('raw') and not is_raw_outer(ty):
        return 'other-container-raw'   # tuple / generic arg with a raw layer at depth 0
    return None


def asemitted_rows(rs):
    """The as-emitted reading of a twinned function f (the C-named raw wrapper + __crat_safe_f): its PARAMETERS are
    the wrapper's (the C signature as emitted); its LOCALS are the twin's (the body moved there; a local moved into
    the twin has a counterpart in the emitted tree and is not 'removed'). Functions without a twin are unchanged."""
    twinned = {detwin(r['owner'])[0] for r in rs if detwin(r['owner'])[1]}
    out = []
    for r in rs:
        o, is_twin = detwin(r['owner'])
        if o in twinned:
            if is_twin and r['kind'] == 'local':
                out.append(dict(r, owner=o))
            elif not is_twin and r['kind'] != 'local':
                out.append(r)
            continue
        out.append(r)
    return out
