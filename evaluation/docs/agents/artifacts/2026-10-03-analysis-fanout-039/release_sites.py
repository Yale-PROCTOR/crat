#!/usr/bin/env python3
"""release_sites.py: relay 059 item 1 (era-5c 127 §1, read independently by analysis-fanout 039).

From each of the L01^13 frame's twenty model-cache entries (mmap, windowed decode of the two members needed):
  * release sites  = the distinct `role: sink` endpoints of the `demand-evidence` export (every `free` and the old pointer of
                     every `realloc` with a site assumption), keyed by (function, block, statement, operand, realloc_outcome);
  * retracted      = those in the `dropped` set of the LAST final selection of the LAST construction;
  * the operand's origins, by a backward walk over `origin.functions[].occurrences`: from the released local through
    assignments (copy / move / cast of a whole local), through Rust library pointer methods (`offset`, `add`, `cast`, ...:
    their first argument) and into a local callee's return; it ends at a boundary allocator (malloc / calloc / realloc /
    strdup), another foreign C function ('foreign'), an indirect call ('indirect'), a parameter, a load (a field or `*p`),
    a null / constant, or 'unresolved'.
  'opaque-origin' = a retracted release one of whose origins is 'indirect' or 'foreign'."""
import collections, glob, json, mmap, re, sys

C = 'worktrees/era5c-l01p13-night-solve/cache/era5b-model-cache-v1'
DEC = json.JSONDecoder()
ALLOC = {'malloc', 'calloc', 'realloc', 'strdup'}


def value_at(m, pos, window=1 << 22):
    while True:
        chunk = m[pos:pos + window].decode('utf-8', 'replace')
        try:
            return DEC.raw_decode(chunk)[0]
        except json.JSONDecodeError:
            if pos + window >= len(m): raise
            window *= 4


def items(m, pos):
    """yield (value) of a JSON array starting at pos, decoding one element at a time."""
    assert m[pos:pos + 1] == b'['
    p = pos + 1
    while True:
        while m[p:p + 1] in (b' ', b'\n', b','): p += 1
        if m[p:p + 1] == b']': return
        w = 1 << 20
        while True:
            chunk = m[p:p + w].decode('utf-8', 'replace')
            try:
                v, end = DEC.raw_decode(chunk); break
            except json.JSONDecodeError:
                if p + w >= len(m): raise
                w *= 4
        yield v
        p += len(chunk[:end].encode('utf-8'))


def key(e):
    return (e['function'], e['block'], e['statement'], json.dumps(e['operand'], sort_keys=True), json.dumps(e.get('realloc_outcome')))


def local_of(slot, fn):
    m = re.match(re.escape(fn) + r'::_(\d+)@d0$', slot or '')
    return int(m.group(1)) if m else None


def run(path):
    f = open(path, 'rb'); m = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
    prog = re.search(rb'"program": *"([^"]+)"', m[:400]).group(1).decode()
    i = m.find(b'"demand-evidence":')
    de = value_at(m, i + len(b'"demand-evidence":'))
    sinks, dropped = {}, set()
    cons = [c for r in de.get('records', []) for c in r['fields'].get('constructions', [])]
    for c in cons:
        for e in c['endpoints']:
            if e['identity']['role'] == 'sink': sinks[key(e['identity'])] = e['identity']
    if cons:
        last = cons[-1]['final_selections'][-1] if cons[-1]['final_selections'] else {'dropped': []}
        dropped = {key(e) for e in last['dropped'] if e['role'] == 'sink'}
    # origin occurrences, keyed by function -> destination local -> [occurrence]
    j = m.find(b'"origin":')
    k = m.find(b'"functions":', j)
    defs = collections.defaultdict(lambda: collections.defaultdict(list))
    params = {}
    for fn in items(m, k + len(b'"functions":')):
        name = fn['function']
        for o in fn['occurrences']:
            d = o['syntax'].get('destination') if o.get('syntax') else None
            if d and d.get('projection') == []:
                defs[name][d['local']].append(o)
        params[name] = {int(x['value'].split('::_')[1].split('@')[0]) for x in fn.get('signature_slots', []) if isinstance(x, dict) and x.get('value', '').count('::_')} if False else None
    m.close(); f.close()

    def walk(fn, loc, seen, depth=0):
        if (fn, loc) in seen or depth > 40: return set()
        seen.add((fn, loc))
        occ = defs.get(fn, {}).get(loc)
        if not occ:
            return {'parameter-or-unresolved'}
        out = set()
        for o in occ:
            ex = o['syntax'].get('expression', {})
            if o['kind'] == 'call':
                cal = o.get('callee') or {}
                kind, tgt = cal.get('kind'), cal.get('target')
                ops = ex.get('operands', [])
                if kind == 'foreign-c':
                    out.add('allocator' if tgt in ALLOC else 'foreign')
                elif kind == 'indirect':
                    out.add('indirect')
                elif kind == 'local':
                    out |= walk(tgt, 0, seen, depth + 1)
                elif kind == 'rust-library':
                    if ops and ops[0].get('kind') in ('copy', 'move') and ops[0]['place']['projection'] == []:
                        out |= walk(fn, ops[0]['place']['local'], seen, depth + 1)
                    else:
                        out.add('load' if ops else 'unresolved')
                else:
                    out.add('unresolved')
            else:
                op = ex.get('operand') if ex.get('kind') in ('value', 'cast') else None
                if op and op.get('kind') in ('copy', 'move'):
                    if op['place']['projection'] == []:
                        out |= walk(fn, op['place']['local'], seen, depth + 1)
                    else:
                        out.add('load')
                elif op and op.get('kind') == 'constant':
                    out.add('null-or-constant')
                else:
                    out.add('unresolved:' + str(ex.get('kind')))
        return out

    rows = []
    for kk, e in sinks.items():
        op = e['operand']
        loc = op.get('local') if op.get('projections') in ([], None) else None
        orig = walk(e['function'], loc, set()) if loc is not None else {'load'}
        rows.append((prog, e['function'], e['block'], e['statement'], kk in dropped, sorted(orig)))
    return prog, rows


def main():
    allrows = []
    for p in sorted(glob.glob(C + '/*.json')):
        prog, rows = run(p)
        allrows += rows
        print(prog, 'sites', len(rows), 'retracted', sum(r[4] for r in rows), file=sys.stderr, flush=True)
    tot = len(allrows); ret = [r for r in allrows if r[4]]
    opq = [r for r in ret if {'indirect', 'foreign'} & set(r[5])]
    kept_opq = [r for r in allrows if not r[4] and {'indirect', 'foreign'} & set(r[5])]
    print(f'release sites {tot}; retracted {len(ret)}; opaque-origin (retracted) {len(opq)} in {len({r[0] for r in opq})} programs; kept with such an origin {len(kept_opq)}')
    print('retracted by origin class (a site may have several):', dict(collections.Counter(c for r in ret for c in r[5])))
    print('by program:', dict(collections.Counter(r[0] for r in allrows)))
    for r in opq + kept_opq:
        print('OPAQUE' if r[4] else 'KEPT-OPAQUE', *r)
    foreign = [r for r in allrows if 'foreign' in r[5]]
    print('releases with an unmodeled foreign-function origin:', len(foreign))
    for r in foreign: print('  ', *r)


if __name__ == '__main__':
    main()
