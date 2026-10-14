#!/usr/bin/env python3
"""relay 111 (S21): model-Owning formals at L01^14u, their delivery / hold reason, and the fatness fact (array use).
Inputs: the L01^14u slot index (r110/p5 keymap14u, = r100's build on main/frame14u + era5c-l01p14u-solve),
the streamed QualifierFacts of every slot (r110/p4 cand/qfacts-l01p14u.tsv), the census's subject reasons."""
import csv, sys, collections
R = 'scratch/analysis-fanout/r110/'
CEN = sys.argv[1] if len(sys.argv) > 1 else 'scratch/main/batch58'
csv.field_size_limit(10**9)
fat = {}
import sys as _s141; _s141.path.insert(0, 'scratch/analysis-fanout/r146/census/work'); import frame146  # r141: FRAME=58pp (control) | s39
QF141 = {'s39': 'scratch/analysis-fanout/r146/census/cache/qfacts/qfacts-s39.tsv',  # r146
         '60sp': 'scratch/analysis-fanout/r146/census/cache/qfacts/qfacts-60sp.tsv'}[frame146.FRAME]
for r in csv.DictReader(open(QF141), delimiter='\t'):
    fat[(r['program'], r['slot'])] = (r['fatness_state'], r['fatness_value'])
reason = {}
import glob, os
for f in glob.glob(CEN + '/*.raw-boundary-subjects.tsv'):
    p = os.path.basename(f).split('.raw-boundary')[0]
    for r in csv.DictReader(open(f), delimiter='\t'):
        reason[(p, r['subject_identity'] if 'subject_identity' in r else r.get('subject_key'))] = r.get('reason', '-')
# r122 g089: the keymap's subject columns (delivery, emitted_form, family, arg_index) were read from frame14u's census;
# take them from CEN's census instead, and check the subject set and census model_kind against the keymap.
c56 = {}
for f in glob.glob(CEN + '/*.raw-boundary-subjects.tsv'):
    p = os.path.basename(f).split('.raw-boundary')[0]
    for r in csv.DictReader(open(f), delimiter='\t', quoting=csv.QUOTE_NONE):
        c56[(r['program'], r['subject_key'])] = dict(arg_index=r['arg_index'], family=r['family'], model_kind=r['model_kind'])
    for r in csv.DictReader(open(CEN + '/' + p + '.raw-boundary-subject-outcomes.tsv'), delimiter='\t', quoting=csv.QUOTE_NONE):
        c56[(r['program'], r['subject_key'])].update(delivery=r['delivery'], emitted_form=r['emitted_form'])
km_subj = set(); chk = collections.Counter()
out = []
allslots = collections.Counter()
for r in csv.DictReader(open('%s/g088b/keymap141/' % 'scratch/analysis-fanout/r146/census/work' + frame146.FRAME + '/keymap.tsv'), delimiter='\t'):  # r141
    if r['row_source'] != 'subject':
        continue
    km_subj.add((r['program'], r['subject_key']))
    c = c56[(r['program'], r['subject_key'])]
    chk['model_kind ' + ('same' if c['model_kind'] == r['census_model_kind'] else 'DIFF')] += 1
    for col in ('delivery', 'emitted_form', 'family', 'arg_index'):
        if c[col] != r[col]:
            chk['changed ' + col] += 1; print('CHANGED', r['program'], r['subject_key'], col, r[col], '->', c[col])
        r[col] = c[col]
    if r['arg_index'] in ('-', ''):
        continue
    # every depth of the formal: d0 slot plus inner slots
    slots = [r['slot_key']] + [s for s in r['inner_slot_keys'].split(',') if s and s != '-']
    kinds = [r['model_kind_l01p14']] + [k for k in r['inner_model_kinds'].split(',') if k and k != '-']
    for d, (s, k) in enumerate(zip(slots, kinds)):
        allslots[k] += 1
        if k != 'owning':
            continue
        fs, fv = fat.get((r['program'], s), ('?', '?'))
        out.append((r['program'], r['subject_key'], d, s, r['family'], r['delivery'], r['emitted_form'], fs, fv,
                    reason.get((r['program'], r['subject_key']), '?')))
cols = ['program', 'subject', 'depth', 'slot', 'family', 'delivery', 'emitted_form', 'fatness_state', 'fatness', 'census_reason']
w = csv.writer(open('owning-formals-batch58pp.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(cols)
for o in sorted(out):
    w.writerow(o)
print('formal slots by model kind (all depths):', dict(allslots))
print('model-Owning formal slots:', len(out))
print('  by fatness:', collections.Counter(o[8] for o in out))
print('  by depth:', collections.Counter(o[2] for o in out))
print('  delivered:', sum(o[5] == 'realized-as-predicted' for o in out), collections.Counter(o[6] for o in out if o[5] == 'realized-as-predicted'))
print('  held:', collections.Counter(o[9] for o in out if o[5] != 'realized-as-predicted'))
for o in sorted(out): print('   ', *o[:2], o[4:])
print('subject sets keymap(frame14u) vs CEN:', 'IDENTICAL' if km_subj == set(c56) else ('DIFF', len(km_subj ^ set(c56))))
print('checks:', dict(chk))
# box.param.chain-slice: pointer formals delivered in a slice Box form whose model kind is not Owning
cs = sorted((p, k, v['model_kind'], v['emitted_form']) for (p, k), v in c56.items() if v['arg_index'] != '-'
            and v['delivery'] == 'realized-as-predicted' and v['emitted_form'] in ('box-slice', 'opt-box-slice') and v['model_kind'] != 'owning')
print('chain-slice (formal, delivered, box-slice/opt-box-slice, model kind not owning):', len(cs)); [print('   ', *x) for x in cs]
bx = sorted((p, k, v['model_kind'], v['emitted_form']) for (p, k), v in c56.items() if v['arg_index'] != '-'
            and v['delivery'] == 'realized-as-predicted' and v['emitted_form'] in ('box', 'box-slice', 'opt-box-slice'))
print('all delivered formals in a Box form:', len(bx)); [print('   ', *x) for x in bx]
