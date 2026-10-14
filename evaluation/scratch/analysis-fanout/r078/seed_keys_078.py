#!/usr/bin/env python3
"""relay 078 item 2: prepare the L01^14 frame's keys EMPTY in paper/numbers-of-record.md (no value is entered)."""
import sys
P = sys.argv[1]
L = open(P).read().split('\n')
def idx(prefix):
    hits = [i for i, l in enumerate(L) if l.startswith('| ' + prefix + ' |')]
    assert len(hits) == 1, (prefix, hits)
    return hits[0]
def row(key, layer, unit, prov):
    return f'| {key} |  | pending | {layer} | {unit} | {prov} |'

F14 = ('EMPTY until L01^14\'s census of record (R822-1, USER 2026-10-05: the copy-lend arm is adopted and the frame of record becomes L01^14, '
       'solved on the restored substrate; seal d09892164, analyses 0cede10fd, fingerprint 1681ec8d, identity era5c-l01p14-v1; '
       'main reads its census by identity against 55\'s census and era-5c 144 §3\'s list of 24 pairs; the frame lands on the user\'s word with the count). '
       'Same definition as the rate of record (R709-1): realized-as-predicted subjects over the same census\'s in-scope safe decisions, less the 36 R454 bindings. '
       'On the landing, rq1.frame-delivered / rq1.frame-safe-decisions / rq1.frame-realization-rate take these values. ')
new_frame = [
    row('rq1.frame14.delivered', 'delivered', 'count', F14 + 'This key: the numerator (delivered).'),
    row('rq1.frame14.safe-decisions', 'decided', 'count', F14 + 'This key: the denominator (the frame\'s own in-scope safe decisions).'),
    row('rq1.frame14.realization-rate', 'delivered', 'percent', F14 + 'This key: delivered / safe decisions.'),
]
ARM = ('EMPTY until L01^14\'s census of record (R822-1). The copy-lend arm\'s own row: CRAT_ERA5C_COPY_LEND=on under era-5c\'s guard (fa92b5935: '
       'lend only an owner the function makes or releases). Provenance only, NOT a value: the second host\'s comparison of L01^14\'s solve against L01^13 on the same inputs '
       '(rq3-inator 014a / 014c / 014d; era-5c 144 §3 lists the pairs by function and local): 24 pairs, each one function in which one local goes ref -> raw and another raw -> ref '
       '(brotli 20, binn 3 -- all in binn_is_valid --, heman 1 -- kmQuaternionToAxisAngle); 0 owners created; the arm-off control equals L01^13 (014d). '
       'These are model slots; their delivery at the census may move differently (era-5c 144 §3). ')
new_arm = [
    row('analysis.copy-lend.swaps', 'decided', 'count', ARM + 'This key: the paired swaps on the twenty.'),
    row('analysis.copy-lend.swaps.brotli', 'decided', 'count', ARM + 'This key: brotli\'s.'),
    row('analysis.copy-lend.swaps.binn', 'decided', 'count', ARM + 'This key: binn\'s.'),
    row('analysis.copy-lend.swaps.heman', 'decided', 'count', ARM + 'This key: heman\'s.'),
    row('analysis.copy-lend.owners-created', 'decided', 'count', ARM + 'This key: slots the arm makes Owning that are not Owning with it off.'),
    row('analysis.copy-lend.guard-dropped', 'decided', 'count', ARM + 'This key: copy pairs that pass every other eligibility clause and the guard drops '
        '(era-5c 133 §1.1 at L01^13\'s model, eligibility only: 16,013 pairs, 911 eligible before the guard, 803 dropped, 108 eligible; per program in 133 §1.1).'),
]
LEND = ('EMPTY until L01^14\'s census of record (R822-1): the counts of the Lending subsection\'s cases (sec:analysis:lending), as era-5c gives them for the frame. '
        'Provenance only, NOT a value: era-5c 124 §1 at L01^13 ')
new_lend = [
    row('analysis.lend.field-read.candidates', 'decided', 'count', LEND + '(§1.3: the reader arm at an exact load q = s->f inside a function that only reads): 38 candidate sites in six programs '
        '(bst 2, avl 4, quadtree 26, json.h 4, heman 1, lil 1). This key: the candidate sites of case 1.'),
    row('analysis.lend.field-read.taken', 'decided', 'count', LEND + '(§1.3): taken at 2 of the 38 (bst\'s and avl\'s minValueNode; the other 36: 4 Owning/Owning, 17 Ref/Ref, 15 Raw/Raw). '
        'This key: the sites where the read lends.'),
    row('analysis.lend.call.lendable-params', 'decided', 'count', LEND + '(§1.1: the lendable certificate, a greatest fixpoint before solving; the pointer\'s own level only): '
        '3,810 lendable parameters over the twenty. This key: lendable parameters (case 2).'),
    row('analysis.lend.call.lendable-params.ref', 'decided', 'count', LEND + '(§1.1): of the 3,810, Ref 3,137. This key: lendable parameters the model makes Ref.'),
    row('analysis.lend.call.lendable-params.raw', 'decided', 'count', LEND + '(§1.1): of the 3,810, Raw 673 (Raw for other reasons: arithmetic, casts, the access-path rule). '
        'This key: lendable parameters the model makes Raw.'),
    row('analysis.lend.call.lendable-params.owning', 'decided', 'count', LEND + '(§1.1): of the 3,810, Owning 0 (a lent parameter is never Owning). '
        'This key: lendable parameters the model makes Owning.'),
    row('analysis.lend.call.reader-params', 'decided', 'count', LEND + '(§1.2: a reader\'s parameter, the whole argument lent): 222 reader functions with 252 parameters, all Ref. '
        'This key: reader parameters. Case 3 (a copy between locals) = analysis.copy-lend.* (eligible = the guarded count at L01^14).'),
]
# frame keys after the record-frame block
i = idx('rq1.record-frame.realization-rate.amended')
L[i+1:i+1] = new_frame
# arm + lend keys after the copy-lend block
i = idx('analysis.copy-lend.raw-raw')
L[i+1:i+1] = new_arm + new_lend
# pointers on the three keys of record
for k in ['rq1.frame-realization-rate', 'rq1.frame-delivered', 'rq1.frame-safe-decisions']:
    j = idx(k)
    assert L[j].endswith(' |')
    L[j] = L[j][:-2] + ' AT L01^14\'s LANDING (R822-1): this key takes rq1.frame14.*\'s value (prepared empty, analysis-fanout 058). |'
# the guarded count on .eligible
j = idx('analysis.copy-lend.eligible')
L[j] = L[j][:-2] + ' At L01^14 the eligibility includes era-5c\'s guard: era-5c 133 §1.1 gives 108 guarded-eligible of 911 on the twenty at L01^13\'s model (analysis-fanout 058). |'
open(P, 'w').write('\n'.join(L))
print('added', len(new_frame) + len(new_arm) + len(new_lend))
