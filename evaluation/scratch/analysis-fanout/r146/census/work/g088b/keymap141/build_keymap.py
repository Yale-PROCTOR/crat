#!/usr/bin/env python3
"""relay 100 key map: frame-14 census subject identities <-> L01^14 model slot keys.

READ-ONLY. Inputs:
  census  scratch/main/frame14/<p>.raw-boundary-subjects.tsv
          (+ subject-outcomes, field-transactions, return-certificate-receipts)
  model   worktrees/era5c-l01p14-restored-solve/cache/era5b-model-cache-v1/
          <entry>.json HEAD ONLY (universe + model, bounded prefix read: model_head.py)
          and <p>.raw-cause-ledger.tsv (the Raw slots, cross-check)
  source  benchmarks/rs-crown-derived/<p>/{lib.rs,c2rust-lib.rs} (struct field order -> field index)
  trees   frame14/emitted-trees/<p>/ (return-type check of admitted return certificates)
Slot spelling = crates/pointer_replacer/src/analyses/borrow_ownership/slot_key.rs @4a47f16f7:
  locals `{def_path}::_{local}@d{depth}`, fields `{def_path}::field{index}[::element]@d{depth}`
= the keys of the cache entry's `model` map = rq3-inator's per-slot names (row-compare read_model / model.<p>.tsv).
Census identity = decision/mod.rs Subject::identity_key: `{owner}::{name|<unnamed>}#{mir_local}`;
census model_kind = mod.rs e1_subject_model_kind = model at (fn, local, depth 0).
"""
import collections, csv, glob, json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model_head import read_head
from rs_structs import scan
import rq3_mir
MIR = rq3_mir.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rq3-017', 'mir2'))


def mir_cols(prog, owner, local):
    """(slot_kind_class_rq3, mir_name) from rq3-inator 017's MIR dumps (18 programs; not brotli / lil)."""
    if prog not in MIR:
        return 'no-mir-dump', 'no-mir-dump'
    info = MIR[prog].get(owner)
    if info is None:
        return 'no-mir-for-fn', 'no-mir-for-fn'
    name = ('formal' if 1 <= local <= info['args'] else 'return place' if local == 0
            else 'named' if local in info['named'] else 'unnamed')
    return rq3_mir.classify(info, local), name

sys.path.insert(0, 'scratch/analysis-fanout/r146/census/work')
import frame146  # r141: FRAME=58pp (control) | s39
F14 = frame146.C
SOLVE = frame146.SOLVE
CACHE = frame146.CACHE
SRC = 'crat/benchmarks/rs-crown-derived'
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), frame146.FRAME)  # r141
os.makedirs(OUT, exist_ok=True)
BOX_FORMS = {'box', 'opt-box-slice', 'box-slice'}
PROGRAMS = sorted(os.path.basename(f).split('.raw-boundary-subjects.tsv')[0]
                  for f in glob.glob(f'{F14}/*.raw-boundary-subjects.tsv'))
csv.field_size_limit(1 << 30)


def rows(path):
    with open(path, newline='') as f:
        return list(csv.DictReader(f, delimiter='\t', quoting=csv.QUOTE_NONE))


SLOT_RE = re.compile(r'^(?P<owner>.+)::(?:_(?P<local>\d+)|field(?P<field>\d+)(?P<elem>::element)?)@d(?P<depth>\d+)$')


def local_key(owner, local, depth):
    return f'{owner}::_{local}@d{depth}'


def ret_sig_ok(tree_dir, fn_path, output):
    name = fn_path.split('::')[-1]
    hits = 0
    for path in glob.glob(f'{tree_dir}/**/*.rs', recursive=True):
        text = open(path, encoding='utf-8', errors='replace').read()
        for m in re.finditer(r'\bfn\s+' + re.escape(name) + r'\s*\(', text):
            sig = text[m.end():text.find('{', m.end())]
            if '->' in sig and output.replace(' ', '') in sig.split('->', 1)[1].replace(' ', '').replace('\n', ''):
                hits += 1
    return hits


keymap, extra, reverse, checks = [], [], [], collections.OrderedDict()


def extra_row(prog, ident, owner, family, delivery, form, box, slots, model, ledger, cls, rq3cls='-', mirname='-'):
    slots = sorted(slots, key=lambda k: int(SLOT_RE.match(k)['depth']))
    d0 = slots[0] if slots else '-'
    return dict(row_source=family, program=prog, subject_key=ident, owner_fn=owner, mir_local='-', arg_index='-',
                ptr_depth=len(slots) or '-', family=family, delivery=delivery, emitted_form=form,
                delivered_box_family=box, slot_key=d0, slot_in_model=int(d0 in model), slot_kind_class=cls if slots else '-',
                slot_kind_class_rq3=rq3cls if slots else '-', mir_name=mirname if slots else '-',
                model_kind_l01p14=model.get(d0, 'not-in-model' if slots else 'no-model-slot'), census_model_kind='-',
                raw_cause_verdict=ledger[d0]['verdict_class'] if d0 in ledger else '-',
                inner_slot_keys=','.join(slots[1:]) or '-', inner_model_kinds=','.join(model[x] for x in slots[1:]) or '-')
summary = collections.Counter()
for p in PROGRAMS:
    subj = {r['subject_key']: r for r in rows(f'{F14}/{p}.raw-boundary-subjects.tsv')}
    outc = {r['subject_key']: r for r in rows(f'{F14}/{p}.raw-boundary-subject-outcomes.tsv')}
    assert set(subj) == set(outc), p
    prog = next(iter(subj.values()))['program'] if subj else p
    entry = json.load(open(f'{SOLVE}/workers/{prog}.json'))['completed']['cache_entry']
    if not os.path.exists(entry):  # r141: A2's ten were solved on host-b and copied into the row's cache
        entry = f'{CACHE}/{os.path.basename(entry)}'
    eprog, universe, model, _ = read_head(entry)
    assert eprog == prog and set(universe) == set(model), (p, eprog)
    ledger = {r['slot_key']: r for r in rows(f'{CACHE}/{prog}.raw-cause-ledger.tsv')}
    assert set(ledger) == {k for k, v in model.items() if v == 'raw'}, f'{p}: ledger != model raw set'
    # struct fields
    srcf = [f for f in (f'{SRC}/{prog}/lib.rs', f'{SRC}/{prog}/c2rust-lib.rs') if os.path.exists(f)][0]
    structs = collections.defaultdict(list)
    for path, kind, fields, anon in scan(srcf):
        structs[path].append((kind, fields))
    aliases = {m.group(1) for m in re.finditer(r'\btype\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*\*\s*(?:mut|const)\b', open(srcf, encoding='utf-8').read())}
    def fields_of(spath):
        c = structs.get(spath, [])
        if len({tuple(f for f, _ in fl) for _, fl in c}) != 1:
            return None
        return c[0][1]
    # ---- subject side
    subj_by_local = {}
    delivered = collections.defaultdict(list)   # slot -> [(role, form, by)]
    for k, s in subj.items():
        o = outc[k]
        owner, local, depth = s['owner_fn'], int(s['mir_local']), int(s['ptr_depth'])
        subj_by_local[(owner, local)] = k
        is_param = s['arg_index'] != '-'
        cls = 'parameter' if is_param else 'named-local'
        d0 = local_key(owner, local, 0)
        inner = [local_key(owner, local, d) for d in range(1, depth)]
        in_model = d0 in model
        mk = model.get(d0, 'not-in-model')
        census_mk = s['model_kind']
        if census_mk != (mk if in_model else 'unmodeled'):
            summary[f'MISMATCH census model_kind vs entry'] += 1
            print('MISMATCH', p, k, census_mk, mk, file=sys.stderr)
        form = o['emitted_form']
        is_deliv = frame146.delivered(p, k, o['delivery'])  # r141: by the emitted tree
        box = int(is_deliv and form in BOX_FORMS)
        if is_deliv:
            delivered[d0].append(('subject-d0', form, k))
            for sk in inner:
                delivered[sk].append((f'subject-inner', form, k))
        rq3cls, mirname = mir_cols(prog, owner, local) if in_model else ('-', '-')
        keymap.append(dict(row_source='subject', program=prog, subject_key=k, owner_fn=owner, mir_local=local, arg_index=s['arg_index'],
                           ptr_depth=depth, family=s['family'], delivery=o['delivery'], emitted_form=form,
                           delivered_box_family=box, slot_key=d0, slot_in_model=int(in_model), slot_kind_class=cls,
                           slot_kind_class_rq3=rq3cls, mir_name=mirname,
                           model_kind_l01p14=mk, census_model_kind=census_mk,
                           raw_cause_verdict=ledger[d0]['verdict_class'] if d0 in ledger else '-',
                           inner_slot_keys=','.join(inner) or '-',
                           inner_model_kinds=','.join(model.get(x, 'not-in-model') for x in inner) or '-'))
        summary['subjects'] += 1
        summary[f'box_family_delivered'] += box
    # ---- field transactions (declarations of struct fields / function-local arrays)
    field_tx = []
    for r in rows(f'{F14}/{p}.raw-boundary-field-transactions.tsv'):
        fl = fields_of(r['struct'])
        idx = None
        if fl is not None:
            names = [f for f, _ in fl]
            idx = names.index(r['field']) if r['field'] in names else None
        slots = [k for k in model if (m := SLOT_RE.match(k)) and m['owner'] == r['struct'] and m['field'] is not None
                 and idx is not None and int(m['field']) == idx]
        field_tx.append((r, idx, slots))
        active = r['status'] == 'applied' and r['revert_status'] == 'active'
        extra.append(extra_row(prog, f"{r['struct']}.{r['field']}", r['struct'], 'field-transaction',
                               f"{r['status']}/{r['revert_status']}", r['form'], int(active and 'box' in r['form']),
                               slots, model, ledger, 'field', 'field'))
        if r['status'] == 'applied':
            summary['field_tx_applied'] += 1
            if r['revert_status'] != 'active':
                summary['field_tx_applied_withdrawn'] += 1
                continue
            if not slots:
                summary['field_tx_applied_no_model_slot'] += 1
                checks.setdefault('field_tx_no_slot', []).append(f"{prog} {r['struct']}.{r['field']} {r['form']} (owner is {'a struct' if r['struct'] in structs else 'NOT a struct: function-local array declaration'})")
            for sk in slots:
                delivered[sk].append(('field', r['form'], f"{r['struct']}.{r['field']}"))
    # ---- admitted return certificates (signature return declarations)
    for r in rows(f'{F14}/{p}.return-certificate-receipts.tsv'):
        if r['kind'] == 'admitted' and r['detail'].startswith('return-certificate '):
            out = re.search(r'output=(\S+)', r['detail']).group(1)
            ok = ret_sig_ok(f'{F14}/emitted-trees/{prog}', r['callee'], out)
            sk = local_key(r['callee'], 0, 0)
            summary['return_cert_admitted'] += 1
            summary['return_cert_in_tree'] += int(ok > 0)
            rc, mn = mir_cols(prog, r['callee'], 0)
            extra.append(extra_row(prog, f"{r['callee']}::<return>", r['callee'], 'return-certificate',
                                   'admitted/in-tree' if ok else 'admitted/NOT-in-tree', out, int(bool(ok) and 'Box<' in out),
                                   [sk] if sk in model else [], model, ledger, 'return-place', rc, mn))
            if ok:
                delivered[sk].append(('return', out, r['callee']))
            else:
                checks.setdefault('return_not_in_tree', []).append(f"{prog} {r['callee']} {out}")
    # ---- reverse index over the whole slot universe (+ subject slots outside the model)
    all_slots = list(model) + [km['slot_key'] for km in keymap if km['program'] == prog and not km['slot_in_model']]
    for sk in all_slots:
        m = SLOT_RE.match(sk)
        owner, depth = m['owner'], int(m['depth'])
        if m['field'] is not None:
            fl = fields_of(owner)
            i = int(m['field'])
            fname = fl[i][0] if fl and i < len(fl) else '?'
            ftype = fl[i][1] if fl and i < len(fl) else '?'
            if fl is None or i >= len(fl) or not (('*' in ftype) or ftype.startswith('[') or ftype.split('::')[-1] in aliases):
                summary['field_slot_unverified_type'] += 1
                checks.setdefault('field_slot_unverified', []).append(f'{prog} {sk} -> {fname}: {ftype}')
            cls, loc, skey = 'field', f"field{i}{m['elem'] or ''}", '-'
            rq3cls, mirname = 'field', '-'
        else:
            local = int(m['local'])
            skey = subj_by_local.get((owner, local), '-')
            fname = '-'
            if skey != '-':
                cls = 'parameter' if subj[skey]['arg_index'] != '-' else 'named-local'
            elif local == 0:
                cls = 'return-place'
            else:
                cls = 'compiler-temporary'
            loc = f'_{local}'
            rq3cls, mirname = mir_cols(prog, owner, local) if sk in model else ('-', '-')
        roles = delivered.get(sk, [])
        boxy = int(any((role.startswith('subject') and role == 'subject-d0' and form in BOX_FORMS)
                       or (role == 'field' and 'box' in form) or (role == 'return' and 'Box<' in form)
                       for role, form, _ in roles))
        reverse.append(dict(program=prog, slot_key=sk, owner=owner, owner_kind='field' if m['field'] is not None else 'local',
                            local_or_field=loc, field_name=fname, depth=depth, slot_kind_class=cls,
                            slot_kind_class_rq3=rq3cls, mir_name=mirname,
                            model_kind_l01p14=model.get(sk, 'not-in-model'),
                            raw_cause_verdict=ledger[sk]['verdict_class'] if sk in ledger else '-',
                            subject_key=skey, behind_delivered=int(bool(roles)), behind_delivered_box=boxy,
                            delivered_roles=';'.join(f'{r}:{f}' for r, f, _ in roles) or '-',
                            delivered_by=';'.join(b for _, _, b in roles) or '-'))
        summary[f'rev_slots'] += 1
        summary[f'rev_{cls}'] += 1
    print(p, 'subjects', len(subj), 'model', len(model), dict(collections.Counter(model.values())), file=sys.stderr)


def write(name, recs):
    with open(f'{OUT}/{name}', 'w', newline='') as f:
        w = csv.DictWriter(f, list(recs[0]), delimiter='\t', lineterminator='\n', quoting=csv.QUOTE_NONE, escapechar='\\')
        w.writeheader(); w.writerows(recs)


write('keymap.tsv', keymap + extra)
write('reverse-index.tsv', reverse)
with open(f'{OUT}/build-summary.txt', 'w') as f:
    for k, v in sorted(summary.items()):
        f.write(f'{k}\t{v}\n')
    for k, v in checks.items():
        f.write(f'## {k} ({len(v)})\n' + ''.join(f'  {x}\n' for x in v))
print(open(f'{OUT}/build-summary.txt').read())
