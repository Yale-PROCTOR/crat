#!/usr/bin/env python3
"""Python port of fold_caller::return_port_owning (crates/pointer_replacer/src/analyses/borrow_ownership/
licensing/fold_caller.rs:1169-1339 at 4a47f16f7), run over a recorded licensing snapshot
(origin.licensing[i] of an era5b-model-cache-v1 entry): metadata = the Facts (snapshot.rs:297-321),
value_origins = ValueOrigins::build(facts) (snapshot.rs:43, checked equal to build_metadata at :632),
which is exactly what mod.rs:556-557 computes at emission.
Admitted keys are then filtered by facts.slot_refs (mod.rs:559) = metadata.slot_keys."""
import json

def K(x): return json.dumps(x, sort_keys=True)

def run(snap):
    md = snap['metadata']
    vo = {}
    for node, atoms in snap['value_origins']['values']:
        vo[(node['construction'], node['var'])] = atoms
    def at(c, v):
        return vo.get((c, v), [{'Unknown': {'construction': c, 'var': v}}])
    def fresh_ids(atoms):
        return [K(a['Fresh']) for a in atoms if isinstance(a, dict) and 'Fresh' in a]
    admitted = set(); holds = {}
    def hold(keys, reason):
        for k in keys: holds.setdefault(k, reason)
    stores = md['field_support_inputs'].get('stores', [])
    for roster in md['bodies']:
        function = roster['point'].get('function')
        if function is None: continue
        c = roster['point']['construction']
        ports = []
        for row in md['boundaries']:
            if row['role'] == 'exit-return' and row['point']['construction'] == c and row['point'].get('function') == function:
                for pair in row['matched']:
                    f = pair['formal']
                    if f['kind'] == 'single': ports.append(f['var'])
        if not ports: continue
        atoms = [a for p in ports for a in at(c, p)]
        frame_heads = [h['slot_key'] for h in md['raw_pointer_heads'] if h['function'] == function]
        if not all((isinstance(a, dict) and 'Fresh' in a) or a == 'Null' for a in atoms):
            hold(frame_heads, 'PortNotFreshOrNull'); continue
        returned = set(fresh_ids(atoms))
        if not returned: continue
        if any(q['point']['construction'] == c and q['point'].get('function') == function and q.get('endpoint') and q['endpoint'].get('callee') == 'free' for q in md['equations']):
            hold(frame_heads, 'ReturnSiteDeliveryUnknown'); continue
        fcons = [x for x in md['consumes'] if x['point']['construction'] == c and x['point'].get('function') == function]
        def at_place(block, stmt, place):
            out = []
            for x in fcons:
                if x['point'].get('block') == block and x['point'].get('statement') == stmt and x['local'] == place['local'] and K(x['projection']) == K(place['projection']):
                    pr = x['projected']
                    if pr['state'] == 'present' and pr['value']['use_start'] != pr['value']['use_end']:
                        out.append(pr['value']['use_start'])
            return out
        def escapes(src):
            for s in stores:
                if s['site']['function'] == function and isinstance(s['value'], dict) and 'Value' in s['value']:
                    for n in at_place(s['site']['block'], s['site']['statement'], s['value']['Value']):
                        if src in fresh_ids(at(c, n)): return True
            for row in md['boundaries']:
                if row['role'] == 'call-argument' and row['point']['construction'] == c and row['point'].get('function') == function:
                    for pair in row['matched']:
                        a = pair['actual']
                        v = a['var'] if a['kind'] == 'single' else a['use_var']
                        if src in fresh_ids(at(c, v)): return True
            return False
        for head in md['raw_pointer_heads']:
            if head['function'] != function: continue
            reaches = None
            for x in fcons:
                if x['local'] != head['local']: continue
                pr = x['projected']
                if pr['state'] != 'present': continue
                for var in (pr['value']['use_start'], pr['value']['def_start']):
                    for fid in fresh_ids(at(c, var)):
                        if fid in returned: reaches = fid
            if reaches is not None:
                if escapes(reaches): hold([head['slot_key']], 'StoredIntoField')
                else: admitted.add(head['slot_key'])
    holds = {k: v for k, v in holds.items() if k not in admitted}
    slot_keys = set(md['slot_keys'])
    emitted = sorted(k for k in admitted if k in slot_keys)
    return sorted(admitted), emitted, holds
