#!/usr/bin/env python3
"""layers_d6.py (analysis-fanout 112, relay 138: copy of r133 layers.py; ONLY changes: D6 -- the in-scope set also admits a subject
whose census decision is a safe form whatever its outcome, so layer1.decided-raw leaves such a subject out; and SOLVE_DIR = `-`
skips the solve side (census keys only; no cache entry is read))
r108 / g1-e: the census-layer keys of appendix E (tab:layers-full, tab:waivers-report).

usage: nice -n 10 python3 layers.py CENSUS_DIR SOLVE_DIR [OUT_TSV]
  CENSUS_DIR  e.g. scratch/main/frame14   (L01^14u: .../frame14u)
  SOLVE_DIR   e.g. worktrees/era5c-l01p14-restored-solve
              (L01^14u: worktrees/era5c-l01p14u-solve)
Writes key<TAB>value<TAB>provenance (default OUT_TSV = ./layers-<basename CENSUS_DIR>.tsv).

READ ONLY. Census side: census-receipt.txt, <p>.raw-boundary-subject-outcomes.tsv,
<p>.raw-boundary-subjects.tsv. Solve side: workers/<p>.json (small receipts), and from each
program's cache entry ONLY (i) the head (universe + model) via model_head.read_head (bounded
prefix, 256 MiB cap) and (ii) the `demand-evidence` value, located by a chunked prefix scan
(it sits in the first ~1 % of the entry; hard cap 4 GiB of prefix) and decoded alone.
No entry is ever json.load-ed or read whole.

R709-1 in-scope set (the denominator of rq1.frame-safe-decisions): family in
{ref, slice, optional, box, cursor} or delivery == realized-as-predicted, less the 36 R454
already-reference bindings (agents/artifacts/2026-09-18-universe-exclusion-r454/
ref-mut-bindings-51.tsv rows with counts_toward_N == true, copied here as
r454-ref-mut-bindings-51.tsv; joined on owner::binding#*).
"""
import collections, csv, glob, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from model_head import read_head  # noqa: E402  (copy of r100/keymap/model_head.py)

SAFE = {'ref', 'slice', 'optional', 'box', 'cursor'}
CHUNK = 16 << 20
PREFIX_CAP = 4 << 30
VALUE_CAP = 1 << 30


def tsv(path):
    with open(path, newline='') as f:
        return list(csv.DictReader(f, delimiter='\t'))


def receipt(census):
    kv = {}
    for line in open(os.path.join(census, 'census-receipt.txt')):
        line = line.strip()
        if '=' in line and ' ' not in line.split('=', 1)[0]:
            k, v = line.split('=', 1)
            kv.setdefault(k, v)
    return kv


def r454_keys():
    keys = set()
    for r in tsv(os.path.join(HERE, 'r454-ref-mut-bindings-51.tsv')):
        if r['counts_toward_N'] == 'true':
            keys.add((r['program'], r['owner'], r['binding']))
    assert len(keys) == 36, len(keys)
    return keys


def demand_evidence(path):
    """Return the decoded `demand-evidence` value of a cache entry without reading it whole."""
    needle = b'"demand-evidence":'
    dec = json.JSONDecoder()
    with open(path, 'rb') as f:
        buf, base = b'', 0
        while True:
            i = buf.find(needle)
            if i >= 0:
                start = base + i + len(needle)
                break
            if base + len(buf) > PREFIX_CAP:
                raise RuntimeError(f'{path}: demand-evidence not within {PREFIX_CAP} bytes')
            chunk = f.read(CHUNK)
            if not chunk:
                raise RuntimeError(f'{path}: no demand-evidence')
            keep = buf[-len(needle):]
            base += len(buf) - len(keep)
            buf = keep + chunk
        w = 4 << 20
        while True:
            f.seek(start)
            data = f.read(w)
            try:
                v, _ = dec.raw_decode(data.decode('utf-8'))
                return v
            except (json.JSONDecodeError, UnicodeDecodeError):
                if len(data) < w or w >= VALUE_CAP:
                    raise
                w *= 4


def ekey(e):
    e = dict(e)
    e.pop('construction', None)
    return json.dumps(e, sort_keys=True)


def site_assumptions(entry):
    de = demand_evidence(entry)
    cons = [c for r in de.get('records', []) for c in r['fields'].get('constructions', [])]
    if not cons:
        return 0, 0, 'no-construction'
    last = cons[-1]  # the precise run (construction 1); construction 0 = baseline
    eps = {ekey(e['identity']) for e in last['endpoints']}
    assert len(eps) == len(last['endpoints'])
    fs = last['final_selections'][-1] if last['final_selections'] else None
    if fs is None:
        return len(eps), 0, 'no-final-selection'
    state = (fs.get('outcome') or {}).get('state') if isinstance(fs.get('outcome'), dict) else fs.get('outcome')
    dropped = fs.get('dropped')
    if dropped is None:
        raise RuntimeError(f'{entry}: last final selection has no dropped set (outcome {fs.get("outcome")})')
    dk = {ekey(e) for e in dropped}
    assert dk <= eps, 'dropped endpoint not in the construction'
    roles = collections.Counter(json.loads(k)['role'] for k in eps)
    droles = collections.Counter(json.loads(k)['role'] for k in dk)
    return len(eps), len(dk), f'constructions={len(cons)} src={roles["source"]} sink={roles["sink"]} dropped_src={droles["source"]} dropped_sink={droles["sink"]} state={state}'


def main():
    sys.path.insert(0, 'scratch/analysis-fanout/r146/census/work')
    import frame146  # r141: FRAME=58pp (control) | s39; census + solve from the frame, delivered BY THE EMITTED TREE
    census, solve = sys.argv[1].rstrip('/'), sys.argv[2].rstrip('/')
    if census != frame146.C or solve not in ('-', frame146.SOLVE):
        raise SystemExit('layers141: census/solve do not match FRAME')
    for r_ in []: pass
    out = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, f'layers-{os.path.basename(census)}.tsv')
    rows = []

    def put(k, v, prov):
        rows.append((k, str(v), prov))
        print(f'{k}\t{v}', file=sys.stderr, flush=True)

    rc = receipt(census)
    if 'programs_degraded' not in rc:  # r141: a complete-with-typed-failure receipt omits these; read per-program.kv instead
        kv = [dict(t.split('=', 1) for t in l.split()[1:] if '=' in t) for l in open(os.path.join(census, 'per-program.kv')) if l.strip()]
        ok = [x.get('raw_boundary_outcome_kind') for x in kv]
        rc['programs_emitted'] = str(ok.count('emitted')) + ' (per-program.kv raw_boundary_outcome_kind=emitted)'
        rc['programs_degraded'] = str(sum(1 for x in ok if x != 'emitted'))
        hits = [x.get('raw_boundary_cache_status') for x in kv]
        rc['cache_hits'] = f"{hits.count('hit')}/{len(hits)} (per-program.kv raw_boundary_cache_status)"
    head = f'census {census} (status={rc.get("status")} data={rc.get("data")} delivery={rc.get("delivery")} programs={rc.get("programs")} cache_hits={rc.get("cache_hits")})'
    put('census.data-flag', rc['data'], f'{head}: census-receipt.txt line data=')
    put('census.delivery-flag', rc['delivery'], f'{head}: census-receipt.txt line delivery=')
    put('layer2.programs-degraded', rc['programs_degraded'],
        f'{head}: census-receipt.txt programs_degraded= (= delivery-summary.tsv programs_degraded; programs_emitted={rc.get("programs_emitted")})')

    oc = []
    for f in sorted(glob.glob(os.path.join(census, '*.raw-boundary-subject-outcomes.tsv'))):
        oc += tsv(f)
    for r in oc:  # r141: a ledger-only custody row (raw in the emitted tree) is not delivered
        if r['delivery'] == 'realized-as-predicted' and not frame146.delivered(r['program'], r['subject_key'], r['delivery']):
            r['delivery'] = 'ledger-only-raw-in-tree'
    sj = {}
    for f in sorted(glob.glob(os.path.join(census, '*.raw-boundary-subjects.tsv'))):
        for r in tsv(f):
            sj[(r['program'], r['subject_key'])] = r
    assert len(sj) == len(oc), (len(sj), len(oc))
    r454 = r454_keys()

    def is_r454(r):
        m = re.match(r'^(.*)::([^:#]+)#\d+$', r['subject_key'])
        return bool(m) and (r['program'], m.group(1), m.group(2)) in r454

    fam = collections.Counter(r['family'] for r in oc)
    def d6(r):  # D6 (relay 138)
        return sj[(r['program'], r['subject_key'])]['decision'] in SAFE
    scope0 = [r for r in oc if r['family'] in SAFE or r['delivery'] == 'realized-as-predicted' or d6(r)]
    hits = [r for r in scope0 if is_r454(r)]
    assert len(hits) == 36 and all(r['delivery'] != 'realized-as-predicted' for r in hits), len(hits)
    scope = [r for r in scope0 if not is_r454(r)]
    deliv = sum(r['delivery'] == 'realized-as-predicted' for r in scope)
    rev = sum(r['delivery'] == 'reverted' for r in scope)
    notpl = [r for r in scope if r['delivery'] not in ('realized-as-predicted', 'reverted')]
    raw_und = [r for r in oc if r['family'] == 'raw' and r['delivery'] != 'realized-as-predicted' and not d6(r)]
    excl = [r for r in oc if r['family'] == 'unmodeled']
    exk = collections.Counter(r['exclusion'] for r in excl)
    base = (f'{head}; subjects = glob <p>.raw-boundary-subject-outcomes.tsv ({len(oc)} rows; family '
            + ', '.join(f'{k} {v}' for k, v in sorted(fam.items())) + f'); R709-1 in-scope = family in '
            f'{{ref,slice,optional,box,cursor}} or delivery==realized-as-predicted ({len(scope0)}) less R454 36 = {len(scope)} '
            f'(delivered {deliv}, reverted {rev}, other {len(notpl)})')
    put('layer1.declarations', len(oc), base + '; this key: every subject row (pointer locals with a name + pointer formals); '
        f'partition: in-scope {len(scope)} + raw-family undelivered {len(raw_und)} + foreign/impl {len(excl)} + R454 bindings 36 = {len(scope) + len(raw_und) + len(excl) + 36}')
    put('layer1.decided-raw', len(raw_und), base + f'; this key: family == raw and delivery != realized-as-predicted (raw family {fam["raw"]} less the {fam["raw"] - len(raw_und)} the rewriter delivers anyway, which R709-1 counts as safe decisions)')
    put('layer1.excluded-items', len(excl), base + '; this key: family == unmodeled, delivery typed-excluded (' + ', '.join(f'{k} {v}' for k, v in sorted(exk.items())) + ')')
    put('layer2.reverted', rev, base + '; this key: in-scope delivery == reverted (revert_scope function); = rq5.form.total.reverted')
    put('layer2.not-placed', len(notpl), base + '; this key: in-scope subjects neither delivered nor reverted (delivery degraded, placed=0; each with a typed reason in <p>.raw-boundary-subjects.tsv reason); = decided safe - delivered - reverted')

    def held(label, safe_only=True):
        xs = [r for r in (scope if safe_only else oc) if sj[(r['program'], r['subject_key'])]['reason'] == label]
        return xs, collections.Counter(r['program'] for r in xs)
    for key, label in (('layer2.held-stream', 'held:io-domain:type'), ('hold.void-pointee', 'held:void-pointee'),
                       ('hold.thin-extent', 'held:thin-extent')):
        xs, byp = held(label)
        allx, _ = held(label, False)
        put(key, len(xs), base + f'; this key: in-scope subjects whose <p>.raw-boundary-subjects.tsv reason == {label} '
            f'(all families: {len(allx)}); by program ' + ', '.join(f'{k} {v}' for k, v in sorted(byp.items())))

    # ---- solve side ----
    if solve == '-':
        with open(out, 'w') as f:
            f.write('key\tvalue\tprovenance\n')
            for r in rows:
                f.write('\t'.join(r) + '\n')
        print('wrote (census side only)', out, file=sys.stderr)
        return
    workers = sorted(glob.glob(os.path.join(solve, 'workers', '*.json')))
    ok, kinds, nslots, sa_tot, sa_ret, per = [], collections.Counter(), 0, 0, 0, []
    for w in workers:
        d = json.load(open(w))  # small worker receipt (~1.4 KB), not a cache entry
        if d.get('status') != 'complete' or d.get('failure') is not None or not d.get('completed'):
            per.append(f'{d.get("program")}:NOT-COMPLETE')
            continue
        p, entry = d['program'], d['completed']['cache_entry']
        if not os.path.exists(entry):  # r141: the S39 row's host-b ten
            entry = os.path.join(solve, 'cache/era5b-model-cache-v1', os.path.basename(entry))
        ok.append(p)
        prog, uni, model, _ = read_head(entry)
        assert prog in (None, p) and len(uni) == len(model), (p, prog, len(uni), len(model))
        nslots += len(model)
        kinds.update(model.values())
        t, k, det = site_assumptions(entry)
        sa_tot += t
        sa_ret += k
        per.append(f'{p}:{t}/{k}')
        print(f'  {p} slots={len(model)} sites={t} retracted={k} {det}', file=sys.stderr, flush=True)
    sprov = (f'solve {solve}: workers/<p>.json status complete ({len(ok)} of {len(workers)}), each completed.cache_entry read by '
             'model_head.read_head (bounded head: universe + model; |universe| == |model| asserted)')
    put('layer1.programs-accepted', len(ok), f'solve {solve}: workers/<p>.json with status complete, failure null, a completed cache entry '
        f'({len(ok)} of {len(workers)}); census receipt cache_hits={rc.get("cache_hits")}, programs_emitted={rc.get("programs_emitted")}')
    put('layer1.slots', nslots, sprov + '; this key: model map entries summed over programs (locals and fields, all depths)')
    unk = set(kinds) - {'ref', 'owning', 'raw'}
    assert not unk, unk
    for k in ('ref', 'raw', 'owning'):
        put(f'layer1.{k}', kinds[k], sprov + f'; this key: model kind == {k}')
    dprov = (f'solve {solve}: each cache entry\'s demand-evidence value (located by a chunked prefix scan, decoded alone): '
             'site assumptions = endpoints (role source = allocation, role sink = release) of the last construction (the precise run); '
             'retracted = the dropped set of its last final selection; active = total - retracted; per program total/retracted: ' + ' '.join(per))
    put('layer1.site-assumptions', sa_tot, dprov)
    put('layer1.site-retracted', sa_ret, dprov)
    put('layer1.site-active', sa_tot - sa_ret, dprov)

    with open(out, 'w') as f:
        f.write('key\tvalue\tprovenance\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('wrote', out, file=sys.stderr)


if __name__ == '__main__':
    main()
