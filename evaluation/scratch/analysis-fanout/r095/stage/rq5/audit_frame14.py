#!/usr/bin/env python3
"""analysis-fanout r095 (relay 095 item 1, part rq5): RQ5's row-level cause of record at the L01^14 frame census.
Every row whose (program, subject_key, label, family) equals 54''s keeps 54''s row-level cause (map54p/rows-final.tsv);
the 46 rows that are new (29), relabelled (14) or family-changed (3) take the audit below (read on frame14's tables
and emitted trees). Writes rows-final.tsv, row-causes-final.tsv, totals-final.tsv, per-cause.tsv."""
import csv, collections, sys
csv.field_size_limit(10**9)
R052 = 'scratch/analysis-fanout/r052'
BASE = 'docs/agents/artifacts/2026-10-04-analysis-fanout-049/rq5-refile/rows-final-r069.tsv'  # 54' row-level of record: 045's audit + 049's re-file of 17
old = {(r['program'], r['subject_key']): r for r in csv.DictReader(open(BASE), delimiter='\t')}
oldm = {(r['program'], r['subject_key']): r for r in csv.DictReader(open(f'{R052}/rows54p-main.tsv'), delimiter='\t')}
newm = {(r['program'], r['subject_key']): r for r in csv.DictReader(open('rows-frame14-main.tsv'), delimiter='\t')}
rows = list(csv.DictReader(open('map14/rows.tsv'), delimiter='\t'))
SC, UD, GEN = 'side-condition', 'undefined', 'generator'
RA = ('side-condition', 'retained alias, stop-gap (R796-1: receipt held:retained-alias / observed:<run>, side-condition; R788-3 the audit reads the label as side-condition)')
A = {}
def a(p, names, cause, sub, ev):
    for n in names: A[(p, n)] = (cause, sub, ev)
B = 'brotli'
a(B, ['src::enc::brotli_bit_stream::BuildAndStoreBlockSplitCode::tree#5', 'src::enc::brotli_bit_stream::BuildAndStoreHuffmanTree::tree#4',
      'src::enc::brotli_bit_stream::EncodeContextMap::tree#5'], SC, 'pair-raw-view (family slice -> ref only)',
  'pairs.tsv: raw-view sites a5-fallback-raw-view-role with a5-not-proven-disjoint:recorded-risky positions; same label and cause as 54\'')
a('binn', ['src::binn::binn_is_valid::psize#4'], SC, 'aliased-storage-withdrawn',
  'subjects.tsv reason_detail binn_load@lib.rs:477; R575-6 storage-root overlap not excluded; 54\'s pcount#3 read the same (pcount left the safe set with the copy-lend pair binn_is_valid #3/#4)')
a(B, ['src::dec::decode::DecodeVarLenUint8::value#3'], SC, 'aliased-storage-withdrawn (member beside container)',
  'value = &mut (*s).num_block_types[..] beside s (BrotliDecoderDecompressStream lib.rs:114027); the callee writes (*s).substate_decode_uint8 only, a disjoint field: disjoint in fact, not proven (lodepng_memcpy::dst precedent)')
a(B, ['src::dec::decode::ReadHuffmanCode::s#5'], SC, 'aliased-storage-withdrawn (was pair-raw-view)',
  'reason_detail BrotliDecoderDecompressStream@lib.rs:114058/114080; storage-root overlap not excluded; 54\' side-condition under pair-raw-view')
a(B, ['src::dec::decode::ProcessSingleCodeLength::prev_code_len#5'], SC, 'pair-raw-view',
  'pairs.tsv: position 4/5->5/6 overlapping:a5-not-proven-disjoint:recorded-risky')
a(B, ['src::dec::decode::SafeReadBlockLength::br#4'], SC, 'pair-raw-view (was missing-required-site)',
  'pairs.tsv pair-t2-same-object over 1/3->2/4 a5-not-proven-disjoint; br = &mut (*s).br beside s; 54\' read the same row side-condition')
a(B, ['src::enc::compress_fragment::BrotliCompressFragmentFastImpl::cmd_bits#8', 'src::enc::compress_fragment::BrotliCompressFragmentFastImpl::cmd_depth#7'],
  SC, 'pair-raw-view (was slice-use-unsupported)',
  'pairs.tsv: raw-view position 1/3->2/4 overlapping:a5-not-proven-disjoint; the 54\' generator gap (slice-use-unsupported) is closed, the pair is the blocker')
a(B, [f'src::enc::compress_fragment::BrotliCompressFragmentFastImpl{i}::input#2' for i in (9, 11, 13, 15)], GEN,
  'slice-use-unsupported (was held:local-callee-access-extent)', 'both labels generator; the use rendering is missing, no absent fact')
a(B, ['src::enc::encode::ChooseHasher::params#1'], UD, 'container beside member',
  'the only call ChooseHasher(params, &mut (*params).hasher) (emitted lib.rs:175944); the callee writes (*hparams).type_0 inside *params while params would be a protected shared reference; 54\' SafeReadBlockLength::s / DecodeVarLenUint8::s precedent; argument only')
a(B, ['src::enc::encode::EncodeData::out_size#4'], SC, 'seam-site-overlap = aliased storage (member beside container)',
  'calls pass &mut (*s).available_out_ beside s (ProcessMetadata, BrotliEncoderCompressStream); no A5 overlap-proof row for EncodeData in adapters.tsv; 54\' EncodeData::output#5 precedent')
a(B, ['src::enc::metablock::InitBlockSplitterDistance::histograms#8', 'src::enc::metablock::InitBlockSplitterDistance::m#1'], GEN,
  'root-granular-twin-check', 'adapters.tsv overlap-proof a5-site-proof-clear / all-peers-clear at positions 0, 6, 7, 8 (bb12:s47); the seam drops anyway; 54\' InitContextBlockSplitter precedent (same shape)')
a(B, ['src::enc::metablock::InitBlockSplitterDistance::new_array#41', 'src::enc::metablock::InitBlockSplitterDistance::new_array_0#98'], GEN,
  'cascade (root-granular-twin-check)', 'box-withdrawn-at-emission: signature-class-held:dropped-site:seam-site-overlap; 54\' InitContextBlockSplitter::new_array precedent')
a(B, ['src::enc::metablock::BrotliBuildMetaBlockGreedyInternal::mb#12'], SC, 'retention (was borrowed-into-raw-param)',
  'retention.tsv: arg 11 retains (positive-retention) via InitBlockSplitterDistance arg6, whose body stores split = &mut (*mb).distance_split into (*self_0).split_ of the splitter local, read after the call (ContextBlockSplitterAddSymbol); R476 frame-bounded discharge not established; 54\' generator (missing template) is no longer the blocker')
a(B, [f'src::enc::metablock::BrotliBuildMetaBlockGreedyInternal::{n}' for n in ('commands#10', 'm#1', 'ringbuffer#2', 'static_context_map#9')], SC,
  'cascade of mb#12 (retention)', 'exclusion terminal-not-applied:dropped-site:seam-positive-retention (the class drop); own args no-retain in retention.tsv')
a('binn', ['src::binn::AdvanceDataPos::plimit#2'], UD, 'one-past-the-end operand (was dependency-class-held)',
  'ptr-comparison; callers binn_is_valid_ex and binn_list_get_value (emitted lib.rs:1546 / 1784) pass plimit = p.offset(size) (lines 1532 / 1780), one past the end: a reference there is UB at creation (R774-1)')
a('lil', ['src::lil::lil_get_var_or::var#5'], GEN, 'return-not-adapted', 'a local; the return adapter is missing; no absent fact')
C = 'scratch/main/frame14'
for k, r in newm.items():
    if r['label'] == 'held:retained-alias':
        sj = {x['subject_key']: x for x in csv.DictReader(open(f'{C}/{k[0]}.raw-boundary-subjects.tsv'), delimiter='\t')}
        A[k] = RA + ('subjects.tsv reason=held:retained-alias reason_detail=' + sj[k[1]]['reason_detail'] + '; one of the stop-gap table\'s 19 (main 179b: withdrawn by the retained-access check 19)',)
out, audited = [], []
for r in rows:
    k = (r['program'], r['subject_key'])
    o = old.get(k)
    if o and o['label'] == r['label'] and oldm[k]['family'] == newm[k]['family']:
        out.append([r['program'], r['subject_key'], r['group'], r['label'], o['cause'], o['sub'], o['evidence']])
        continue
    kind = 'new' if not o else ('relabelled' if o['label'] != r['label'] else 'family-changed')
    c, s, e = A[k]
    out.append([r['program'], r['subject_key'], r['group'], r['label'], c, s, e])
    audited.append([kind, r['program'], r['subject_key'], newm[k]['family'], r['label'], o['label'] if o else '-', o['cause'] if o else '-', c, s, e])
assert len(audited) == 46 and len(out) == 914, (len(audited), len(out))
CAUSES = ['held', 'no-safe-form', 'undefined', 'type-system', 'side-condition', 'form-fact', 'generator']
w = csv.writer(open('rows-final.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program', 'subject_key', 'group', 'label', 'cause', 'sub', 'evidence']); w.writerows(out)
csv.writer(open('row-causes-final.tsv', 'w'), delimiter='\t', lineterminator='\n').writerows([x[0], x[1], x[4]] for x in out)
w = csv.writer(open('audit-frame14.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['kind', 'program', 'subject_key', 'family', 'label', 'b54p_label', 'b54p_cause', 'cause', 'sub', 'evidence']); w.writerows(sorted(audited))
per = collections.defaultdict(collections.Counter); tot = collections.Counter()
for x in out: per[x[0]][x[4]] += 1; tot[x[4]] += 1
w = csv.writer(open('totals-final.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program'] + CAUSES + ['total'])
for p in sorted(per): w.writerow([p] + [per[p][c] for c in CAUSES] + [sum(per[p].values())])
w.writerow(['total'] + [tot[c] for c in CAUSES] + [sum(tot.values())])
o54 = collections.Counter(r['cause'] for r in old.values())
print('cause\t54p\tframe14'); [print(f'{c}\t{o54[c]}\t{tot[c]}') for c in CAUSES]; print('total', sum(o54.values()), sum(tot.values()))
print('audit', collections.Counter((x[6], x[7]) for x in audited))
