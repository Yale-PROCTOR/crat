#!/usr/bin/env python3
"""analysis-fanout 088 (relay 110, part rq5): RQ5's row-level cause of record (R777-2) at the L01^14u frame census.
Base = the L01^14 row-level file of record (r095/stage/rq5/verifier/rows-final.verified.tsv: 069's audit + the
verifier's one correction, ReadHuffmanCode::s#5 -> undefined). Every frame14u row whose (program, subject_key, label,
family) equals L01^14's keeps L01^14's cause; the rows that are new or relabelled since L01^14 take the audit below
(read on frame14u's subjects / subject-outcomes / pairs tables and emitted trees). Five of the eight are rows that
return to their exact 54' state (key, label, family, root) and take 54''s verified row-level cause (049's
rows-final-r069.tsv); the three others are pair-raw-view rows on an a5-not-proven-disjoint pair.
Writes rows-final.tsv, audit-frame14u.tsv, left-frame14u.tsv, totals-final.tsv."""
import csv, collections
csv.field_size_limit(10**9)
S = 'scratch/analysis-fanout/r095/stage/rq5'
C = 'scratch/main/frame14u'
rd = lambda f: list(csv.DictReader(open(f), delimiter='\t'))
key = lambda r: (r['program'], r['subject_key'])
old = {key(r): r for r in rd(f'{S}/verifier/rows-final.verified.tsv')}
oldm = {key(r): r for r in rd(f'{S}/rows-frame14-main.tsv')}
newm = {key(r): r for r in rd('rows-frame14u-main.tsv')}
b54 = {key(r): r for r in rd('rows-final-54p.tsv')}  # 049 rows-final-r069.tsv (54' of record)
m54 = {key(r): r for r in rd('scratch/analysis-fanout/r052/rows54p-main.tsv')}
rows = rd('map14u/rows.tsv')
SC, UD = 'side-condition', 'undefined'
A = {}
def a(p, n, cause, sub, ev): A[(p, n)] = (cause, sub, ev)
# (i) rows back in their exact 54' state: 54''s verified row-level cause
for p, n, ev in [
    ('binn', 'src::binn::binn_is_valid::pcount#3',
     'swap with psize#4 (the copy-lend pair binn_is_valid #3/#4; psize#4 is model-Raw at frame14u): subjects.tsv reason aliased-storage-withdrawn, '
     'reason_detail binn_load@lib.rs:477:16: 478:44 (the same site as L01^14 psize#4); R575-6 storage-root overlap not excluded; 54\' side-condition, L01^14 psize#4 side-condition'),
    ('brotli', 'src::dec::decode::SafeReadBlockLength::s#1',
     'model Ref again (L01^14 model-Raw): excl terminal-not-applied:dropped-site:missing-required-site;seam-site-overlap; emitted lib.rs:112321 / 114075 '
     'SafeReadBlockLength(s, &mut *((*s).block_length).as_mut_ptr().offset(..), .., br): container beside a written member (the callee writes *result); 54\' undefined (verified)'),
    ('brotli', 'src::enc::encode::EncodeData::output#5',
     'swap with out_size#4 (model-Raw at frame14u): excl terminal-not-applied:dropped-site:seam-site-overlap; emitted lib.rs:180094 / 180302 EncodeData(s, .., &mut (*s).available_out_, &mut (*s).next_out_): '
     'a member beside its container, no A5 overlap-proof row; 54\' side-condition (verified), L01^14 out_size#4 side-condition'),
    ('binn', 'src::binn::AdvanceDataPos::plimit#2',
     'relabelled ptr-comparison -> dependency-class-held and family optional -> cursor (the model decides a cursor, which represents the one-past-the-end operand p.offset(size), so the L01^14 undefined reading for a reference no longer applies); '
     'cascade of class 149 rooted at binn_list_next, root_reason dropped-site:seam-positive-retention (output-storage certificate absent); 54\' side-condition (same family, label and root)'),
    ('brotli', 'src::dec::decode::SafeReadBlockLength::br#4',
     'relabelled pair-raw-view -> missing-required-site (s#1 is model Ref again, the 54\' shape): br = &mut (*s).br beside s, no disjoint-access proof; '
     'excl terminal-not-applied:dropped-site:missing-required-site;seam-site-overlap; 54\' side-condition (verified), L01^14 side-condition'),
]:
    o = b54[(p, n)]
    assert m54[(p, n)]['label'] == newm[(p, n)]['label'] and m54[(p, n)]['family'] == newm[(p, n)]['family'], n
    a(p, n, o['cause'], o['sub'] + ' (54\' row-level cause)', ev)
# (ii) pair-raw-view rows on a not-proven pair (swaps with a now model-Raw or delivered side)
a('binn', 'src::binn::binn_read_next_pair::pid#3', SC, 'pair-raw-view',
  'pairs.tsv binn_map_next -> binn_read_next_pair arg 2 raw-view 1/2->2/3 overlapping:a5-not-proven-disjoint:recorded-risky; iter#2 (54\'/L01^14 seam-positive-retention) is model-Raw at frame14u; 54\' pkey#4 precedent (pair-raw-view, side-condition)')
a('brotli', 'src::dec::decode::ProcessSingleCodeLength::repeat#3', SC, 'pair-raw-view',
  'swap with prev_code_len#5 (model-Raw at frame14u): pairs.tsv SafeReadSymbolCodeLengths -> ProcessSingleCodeLength arg 2 raw-view, 2/5->3/6 overlapping:a5-not-proven-disjoint (the peer symbol_lists, the same peer as L01^14 prev_code_len#5 4/5->5/6); emitted lib.rs:111787 passes &mut (*h).repeat; disjoint fields in fact, not proven; L01^14 prev_code_len#5 side-condition')
a('brotli', 'src::enc::encode::InjectFlushOrPushOutput::total_out#4', SC, 'pair-raw-view',
  'swap with s#1 (delivered at L01^14, model-Raw at frame14u): pairs.tsv BrotliEncoderCompressStream -> InjectFlushOrPushOutput arg 3 raw-view 1/3->2/4 and 2/3->3/4 overlapping:a5-not-proven-disjoint (total_out with available_out / next_out, the caller\'s own formals); label default side-condition')
out, audited = [], []
for r in rows:
    k = key(r); o = old.get(k)
    if o and o['label'] == r['label'] and oldm[k]['family'] == newm[k]['family']:
        out.append([r['program'], r['subject_key'], r['group'], r['label'], o['cause'], o['sub'], o['evidence']]); continue
    kind = 'new' if not o else ('relabelled' if o['label'] != r['label'] else 'family-changed')
    c, s, e = A[k]
    out.append([r['program'], r['subject_key'], r['group'], r['label'], c, s, e])
    audited.append([kind, r['program'], r['subject_key'], newm[k]['family'], r['label'], o['label'] if o else '-', o['cause'] if o else '-', r['cause'], c, s, e])
assert len(audited) == 8 and len(out) == 907, (len(audited), len(out))
# rows of L01^14 that left the undelivered-safe set, with their frame14u state
here = {key(r) for r in rows}
def tab(p, t):
    return {r['subject_key']: r for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-{t}.tsv'), delimiter='\t')}
left = []
for k in sorted(old):
    if k in here: continue
    sj, so = tab(k[0], 'subjects')[k[1]], tab(k[0], 'subject-outcomes')[k[1]]
    state = 'delivered (' + so['emitted_form'] + ')' if so['delivery'] == 'realized-as-predicted' else f"model-{sj['model_kind']} (family {sj['family']}, reason {sj['reason']}): out of the safe set"
    left.append([k[0], k[1], old[k]['label'], old[k]['cause'], state])
CAUSES = ['held', 'no-safe-form', 'undefined', 'type-system', 'side-condition', 'form-fact', 'generator']
w = csv.writer(open('rows-final.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program', 'subject_key', 'group', 'label', 'cause', 'sub', 'evidence']); w.writerows(out)
w = csv.writer(open('audit-frame14u.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['kind', 'program', 'subject_key', 'family', 'label', 'l01p14_label', 'l01p14_cause', 'label_default', 'cause', 'sub', 'evidence']); w.writerows(sorted(audited))
w = csv.writer(open('left-frame14u.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program', 'subject_key', 'l01p14_label', 'l01p14_cause', 'frame14u_state']); w.writerows(left)
per = collections.defaultdict(collections.Counter); tot = collections.Counter()
for x in out: per[x[0]][x[4]] += 1; tot[x[4]] += 1
w = csv.writer(open('totals-final.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program'] + CAUSES + ['total'])
for p in sorted(per): w.writerow([p] + [per[p][c] for c in CAUSES] + [sum(per[p].values())])
w.writerow(['total'] + [tot[c] for c in CAUSES] + [sum(tot.values())])
o14 = collections.Counter(r['cause'] for r in old.values())
print('cause\tL01^14\tL01^14u'); [print(f'{c}\t{o14[c]}\t{tot[c]}') for c in CAUSES]; print('total', sum(o14.values()), sum(tot.values()))
print('audit', collections.Counter((x[6], x[8]) for x in audited))
print('left', collections.Counter((x[3], x[4].split(' ')[0]) for x in left))
