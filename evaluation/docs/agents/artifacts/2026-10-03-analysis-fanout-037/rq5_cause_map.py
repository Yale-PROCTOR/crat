#!/usr/bin/env python3
"""rq5_cause_map.py <rq5-rows.tsv> <out-dir> <census-dir> -- analysis-fanout 035 (relays 050 / 051 / 053): the cause of record
for every undelivered decided-safe row, under R772's split of `analysis` into `side-condition` and `form-fact`.

Input: main's per-row table (agents/tools/rq5_columns.py, main 155: program, subject_key, family, delivery, group,
label, cause, root, root_reason, diag). Output:
  label-defaults.tsv   label -> default cause (what a later census prints for a row with no override)
  rows.tsv             every row: program, subject_key, group, label, cause, sub, evidence
  totals.tsv           cause x program
A row's cause is its label's default unless an override below names it; every override is the frame-13 audit's
row-level reading (analysis-fanout 035 §2, workflow wf_3f86719f-934: classify + adversarial verify per group), and
carries its evidence (the census receipt / the validity rule / a lane's fault run)."""
import collections, csv, os, sys

ROWS, OUT = sys.argv[1], sys.argv[2]

# --- label defaults (R770-1 / R772-1 / R774-1) ---------------------------------------------------------------
D = {
    # group C
    'held:io-domain:type': ('held', 'stream (the I/O pass)'),
    'held:void-pointee': ('no-safe-form', 'void pointee used as a handle; R608-1 (wave-6b 028)'),
    'ptr-comparison': ('undefined', 'a reference at a cursor / past-the-end operand is UB at creation (wave-6a 122 §2, R774-1)'),
    # group B: R772 starting point and R774-1 (escape / aliased-storage labels are side-condition)
    'pair-raw-view': ('side-condition', 'A5 does not prove the pair disjoint (pairs.tsv a5-not-proven-disjoint)'),
    'seam-positive-retention': ('side-condition', 'no output-storage / retention certificate at the seam'),
    'a5-site-proof-reclassified': ('side-condition', 'A5 non-proof on a raw-from-raw argument (adapters.tsv)'),
    'aliased-storage-withdrawn': ('side-condition', 'R575-6 aliased-storage gate: storage-root overlap not excluded'),
    'escapes-via-field-store': ('side-condition', 'the value escapes into raw storage (a field); no escape proof'),
    'escapes-via-foreign-arg': ('side-condition', 'write-through-shared-view at a foreign callee (no returned-child permission)'),
    'escapes-via-return': ('side-condition', 'the value escapes through the return'),
    'pending-sibling-overlap': ('side-condition', 'pending sibling overlap not excluded'),
    'contract-allocation:use': ('side-condition', 'call-argument-not-a-lend: the callee is not proven a lend'),
    'flows-into-raw-param': ('side-condition', 'raw flow (R774-1 label default)'),
    'borrowed-into-raw-param': ('side-condition', 'raw flow (R774-1 label default)'),
    'arg-null-literal': ('generator', 'the null-literal fact exists (option_ops.rs param_receives_null_literal); the family did not take it'),
    'seam-shared-to-mut': ('generator', 'no census receipt names an absent fact (strict evidence standard)'),
    'contract-allocation:overwrite': ('generator', 'allocator_contract.rs peel_casts does not peel a Block (a shape)'),
    # group A: form facts (R772-1 item 1) -- the audit moves most rows of these labels to generator (overrides)
    'held:local-callee-access-extent': ('generator', 'the extent is supplied (R481-1 fallback); the lift declines on a generator shape (licensed-lifts receipt)'),
    'slice-neg-or-unknown-offset': ('generator', 'the cursor route was planned and withdrawn by family exclusion (additive-family-fallbacks.json)'),
    'box-param-caller-unknown': ('generator', 'prior label; heman generator dependency cycle (548/549); native Missing(NativeIdentity)'),
    'held:thin-extent': ('generator', 'a fat rendering exists (R481-1 / NUL-contract); no absent fact'),
    'return-lifetime-permit-absent': ('form-fact', 'the returned reference\'s origin permit is absent (lifetime.rs return_permit)'),
    'held:address-observation-only': ('side-condition', 'the address is interior on every UB-free run but no in-bounds fact establishes it'),
    'box-param-indirect-callers': ('no-safe-form', 'type-erased allocator callback (fn-pointer signature, void pointee)'),
    'return-certificate-indirect-callers': ('no-safe-form', 'type-erased allocator callback (fn-pointer signature, void pointee)'),
    # group D / X: a cascade inherits its root's cause; unrecorded roots are generator by default (R774-1 item 2)
    'verify-reverted': ('generator', 'class reverted at planning or verify; root per final-reverts'),
    'dependency-class-held': ('generator', 'cascade; root per final-reverts'),
}
GEN = 'generator'

def ov(prog, names, cause, sub, ev):
    return {(prog, n): (cause, sub, ev) for n in names}

O = {}
# ---- group A ---------------------------------------------------------------------------------------------------
O.update(ov('brotli', [f'BrotliCompressFragmentTwoPassImpl{i}::input' for i in range(8, 18)] +
            ['WriteMetaBlockInternal::dist_cache', 'WriteMetaBlockInternal::saved_dist_cache', 'WriteMetaBlockInternal::storage',
             'DecideOverLiteralContextModeling::input', 'WriteMetaBlockInternal::literal_context_lut'],
            'side-condition', 'write-through-shared-view',
            'evidence-missing:raw-boundary-returned-child-permission:ordinary-argument-permission:write-through-shared-view (own receipt or class 2424)'))
O.update(ov('lil', ['lil_get_var_or::name', 'lil_find_var::lil', 'lil_find_var::env', 'lil_get_var_or::lil'],
            'side-condition', 'write-through-shared-view', 'write-through-shared-view at hir:208:118 (lil_get_var_or::name), class 208/202'))
O.update(ov('lil', ['lil_list_append::list'], 'side-condition', 'escape', 'blocked-subject:escapes-via-field-store at class 194'))
O.update(ov('lil', [f'fnc_{f}::r' for f in ('downeval', 'enveval', 'eval', 'if', 'jaileval', 'source', 'topeval', 'upeval')],
            'side-condition', 'negative-write', 'evidence-missing:option-raw-return:shared-to-mut-held (option_ops.rs:257)'))
O.update(ov('binn', ['compress_int::pvalue'], 'side-condition', 'negative-write', 'evidence-missing:option-address-view:shared-to-mut-cast (option_ops.rs:366-371)'))
O.update(ov('libtree', ['recurse::bold_color', 'recurse::bold_color_0', 'recurse::regular_color', 'recurse::regular_color_0'],
            'side-condition', 'read-only-literal', 'slice-construction-receipt: evidence-missing:literal-is-read-only (mutability mut)'))
O.update(ov('heman', ['kmVec2Scale::pOut', 'kmVec3Scale::pOut', 'kmMat4Multiply::pM1', 'kmMat4Multiply::pM2', 'kmMat4Multiply::m2'],
            'undefined', 'aliased-by-own-program', 'in-program callers pass one object twice (heman lib.rs:192 kmVec2Scale(pOut, pOut, ..); :2084 kmMat4Multiply(pOut, pOut, ..)); protected-reference rule; argument only'))
O.update(ov('brotli', ['SafeReadBlockLength::s'], 'undefined', 'container-beside-member', 'DecodeBlockTypeAndLength passes s with &mut (*s).field; a callee write through the member into a protected &mut s; argument only'))
O.update(ov('brotli', ['SafeReadBlockLength::br', 'EncodeData::output', 'EncodeData::new_commands'], 'side-condition', 'aliased-storage',
            'R575-6 aliased_storage_twin; no A5 overlap-proof row for the call (adapters.tsv)'))
O.update(ov('brotli', ['InitBlockSplitterCommand::histograms', 'InitBlockSplitterCommand::m', 'InitBlockSplitterLiteral::histograms',
                       'InitBlockSplitterLiteral::m', 'InitContextBlockSplitter::histograms', 'InitContextBlockSplitter::m',
                       'InitBlockSplitterCommand::new_array', 'InitBlockSplitterCommand::new_array_0', 'InitBlockSplitterLiteral::new_array',
                       'InitBlockSplitterLiteral::new_array_0', 'InitContextBlockSplitter::new_array', 'InitContextBlockSplitter::new_array_0'],
            GEN, 'root-granular-twin-check', 'A5 overlap-proof a5-site-proof-clear / all-peers-clear at every position; counted_void aliased_storage_twin ignores it'))
O.update(ov('brotli', ['ProcessRepeatedCodeLength::symbol_lists', 'ProcessSingleCodeLength::symbol_lists', 'BrotliBuildHuffmanTable::symbol_lists',
                       'BrotliSetDepth::depth', 'BrotliCompressFragmentFast::input', 'BrotliCreateHuffmanTree::depth'],
            'form-fact', 'sign / backward extent', 'never cursor-planned; Err(LoadedIndexBelowEntry) or the sign reason'))
O.update(ov('bzip2', ['mainSort::quadrant'], 'form-fact', 'sign of a loaded index', 'Err(LoadedIndexBelowEntry)'))
O.update(ov('heman', ['horizon_scan::convex_hull'], GEN, 'stale census row', 'emitted &mut [kmVec3] at heman/lib.rs:7983 (the census reads degraded)'))
O.update(ov('brotli', ['ShannonEntropy::population_end', 'EmitUncompressedMetaBlock::end', 'CreateCommands::ip_end'],
            'undefined', 'one-past-the-end', 'a reference at an end sentinel is UB at creation (emitability.rs:1806-1810); 3 population_end rows render as an index'))
O.update(ov('lodepng', ['lodepng_strlen::orig'], GEN, 'copy of a delivered slice start', 'audit A-holds'))
O.update(ov('buffer', ['buffer_new_with_string::str', 'buffer_new_with_string_length::str'], 'undefined', 'retained / freed through it',
            'the subject is stored and later freed through the structure (validity rule; argument only)'))
O.update(ov('bzip2', ['default_bzfree::addr'], 'no-safe-form', 'allocator callback', 'type-erased allocator callback'))
# R776-2 STOP 2: the tier-2 retention waiver (R481-2) covers a callee's retention at an outbound call bridge, not the
# subject's own store into a field: the 7 field-store retention-positive rows are undefined
O.update(ov('brotli', ['InitBlockEncoder::block_lengths'], 'undefined', 'stored into a field (R776-2)',
            'site-cause=positive-retention at the store into the encoder struct; R481-2 does not cover a field store (R776-2 STOP 2)'))
O.update(ov('bzip2', ['BZ2_bzCompressInit::strm', 'BZ2_bzDecompressInit::strm'], 'undefined', 'stored into a field (R776-2)',
            '(*s).strm = strm into the heap EState; R481-2 does not cover a field store (R776-2 STOP 2)'))
O.update(ov('bzip2', ['BZ2_bzBuffToBuffCompress::dest', 'BZ2_bzBuffToBuffCompress::source', 'BZ2_bzBuffToBuffDecompress::dest',
                      'BZ2_bzBuffToBuffDecompress::source'], 'side-condition', 'stored into a frame-local field (R777-2)',
            'strm.next_in / next_out = <subject> into the frame-local bz_stream; R476-1 frame-bounded discharge not established (its third condition fails), so the condition is unproved (R777-2 STOP 1)'))
# ---- group B ---------------------------------------------------------------------------------------------------
O.update(ov('libzahl', ['zadd::b', 'zdiv::b', 'zmod::b', 'zsub::b', 'zsub_unsigned::b'], 'undefined', 'identical argument twice',
            'every raw-view site passes one object twice (pair-t2-same-object, both written); seat fixture agents/artifacts/2026-10-03-seat-r772-pair-tb (ac7f288); wave-6o 095 STOP 2 (zsub(a, a, _1): TB "conflicted Reserved")'))
O.update(ov('brotli', ['HasherSetup::m', 'HasherSetup::hasher', 'HasherSetup::data', 'CompressFile::s'], 'undefined', 'inbound retention',
            'inbound seam at a positively retaining formal (seam.rs:4151-4190); R481-2 covers the outbound bridge only; argument only'))
O.update(ov('heman', ['kmPlaneNormalize::pP', 'kmQuaternionNormalize::pIn', 'kmVec2Normalize::pOut', 'kmVec3Normalize::pOut'], 'undefined',
            'identical argument twice', 'kmVec3Normalize(pOut, pOut) etc.; protected-reference rule; argument only'))
O.update(ov('lodepng', ['unfilter::in_0'], 'undefined', 'identical argument twice', 'lodepng 7889 / 7913 in place; argument only'))
O.update(ov('brotli', ['DecodeVarLenUint8::s'], 'undefined', 'container-beside-member', 'peer &mut (*s).num_block_types[..] lies inside *s and the callee writes it'))
O.update(ov('lodepng', ['ucvector_init::buffer'], 'undefined', 'retained / freed through it', 'deallocation through a reference\'s provenance; argument only'))
O.update(ov('brotli', ['BrotliCompressBufferQuality10::commands', 'BrotliCompressBufferQuality10::new_commands'], GEN, 'contract shape',
            'allocator_contract.rs moved-in-only / copied-into-local'))
O.update(ov('brotli', ['BrotliEncoderCompressStream::next_out', 'BrotliBuildMetaBlockGreedyInternal::mb', 'EnsureInitialized::s'], GEN, 'missing template',
            'depth2-storage-shape-held (raw_boundary.rs:6005-6010) / writable-carrier-unavailable (raw_boundary.rs:6318-6327); the retaining positions are T2 under R481-2'))
O.update(ov('brotli', ['BrotliBuildMetaBlockGreedyInternal::commands', 'BrotliBuildMetaBlockGreedyInternal::m', 'BrotliBuildMetaBlockGreedyInternal::ringbuffer'], GEN, 'cascade',
            'blocked-subject cascade of class 2772, root mb#12 (depth2-storage-shape-held)'))
O.update(ov('libzahl', ['zrsh::b'], GEN, 'missing template', 'memcpy#1 writable-carrier-unavailable'))
# ---- group C ---------------------------------------------------------------------------------------------------
O.update(ov('bzip2', ['BZ2_bzwrite::b'], 'held', 'stream handle', 'BZFILE wraps FILE (io-domain-identities row 72)'))
O.update(ov('bzip2', ['BZ2_bzRead::buf', 'BZ2_bzReadGetUnused::unused', 'BZ2_bzWrite::buf', 'BZ2_bzwrite::buf'], 'undefined', 'retained past the frame',
            'stored into (*bzf).strm.next_{in,out}; R608-1 STOP 2 (known retention outside R481-2)'))
O.update(ov('binn', ['copy_raw_value::psource', 'copy_value::psource', 'binn_value::pvalue', 'binn_set_blob::ptr', 'binn_new::pointer'], 'undefined',
            'retained past the call', 'binn-payload-retained (wave-6b 028, R608-1)'))
O.update(ov('binn', ['IsValidBinnHeader::pbuf'], 'side-condition', 'pair not proven disjoint', 'held at GetValue seam-site-overlap (wave-6b 028)'))
O.update(ov('lodepng', ['lodepng_memcpy::dst'], 'side-condition', 'pair not proven disjoint', 'memcpy(data+start, data+backward, n): disjoint in fact, not proven'))
O.update(ov('binn', ['AddValue::pvalue', 'binn_list_get::pvalue', 'binn_map_get::pvalue', 'binn_object_get::pvalue', 'copy_value::pdest',
                     'binn_add_value::pvalue', 'binn_list_add_raw::pvalue', 'binn_map_set_raw::pvalue', 'binn_object_set_raw::pvalue',
                     'compress_int::psource'], 'form-fact', 'extent chosen by a type tag at run time',
            'binn-typed-payload read/write (wave-6b 028); the write/read terminals are model-Raw (kind-raw)'))
O.update(ov('binn', ['binn_memdup::dest', 'GetWriteConvertedData::ppvalue'], GEN, 'allocation family unbuilt', 'wave-6b relay 031'))
O.update(ov('binn', ['CheckAllocation::ptr'], GEN, 'allocation family unbuilt', 'wave-6b relay 031 (also stored into a raw field: weak)'))
O.update(ov('libcsv', ['csv_increase_buffer::vp'], GEN, 'allocation family unbuilt', 'wave-6b relay 031 (also stored into a raw field: weak)'))
O.update(ov('libzahl', ['zabs::b', 'zadd_unsigned::b', 'zdivmod::c', 'zlsh::b', 'zsub_unsigned::c', 'zabs::a', 'zdivmod::b', 'zsub_unsigned::a'],
            'undefined', 'aliased written partner', 'in-program calls alias the compared operand with a written partner (zadd(b_low, b_low, ..) :1556 etc.)'))
O.update(ov('libzahl', ['zmul::c', 'zadd_unsigned::c'], GEN, 'identity comparison, no written alias', 'ptr::eq renders it; no aliasing with a written partner in lib.rs or CROWN test.c'))
# ---- group D / X: roots -------------------------------------------------------------------------------------------
ROOT_CAUSE = {  # final-reverts roots, audit C-D-X
    'InitOrStitchToPreviousBlock': ('undefined', 'cascade of HasherSetup (inbound retention)'),
}
X_SIDE = {'AdvanceDataPos::plimit', 'binn_list_value::ptr', 'binn_list_value::value', 'binn_map_value::ptr', 'binn_map_value::value'}

def short(k):
    # src::a::b::fn::name#N -> fn::name
    k = k.split('#')[0]
    return '::'.join(k.split('::')[-2:])

rows = list(csv.DictReader(open(ROWS), delimiter='\t'))
csv.field_size_limit(10**9)
FR = {x['identity']: x for x in csv.DictReader(open(sys.argv[3] + '/brotli.raw-boundary-final-reverts.tsv'), delimiter='\t') if x['kind'] == 'function'}
os.makedirs(OUT, exist_ok=True)
out = []
for r in rows:
    if r['group'] == 'R454':
        continue
    p, lab, s = r['program'], r['label'], short(r['subject_key'])
    cause, sub, ev = D.get(lab, (GEN, 'default', 'no absent fact named (050 default)'))[0], lab, D.get(lab, (GEN, 'no absent fact named (R770-1 default: generator)'))[1]
    if (p, s) in O and r['group'] != 'D':
        cause, sub, ev = O[(p, s)]
    if r['group'] == 'D':
        fn = s.split('::')[0]
        if fn in ROOT_CAUSE:
            cause, ev = ROOT_CAUSE[fn]; sub = 'cascade'
        elif r['program'] == 'brotli':
            f = FR.get(r['subject_key'].split('#')[0].rsplit('::', 1)[0], {})
            seed, pr = f.get('interface_seed') or '-', f.get('partition_root') or '-'
            if seed == 'class#2445' or 'class=2452' in pr:
                sub, ev = 'root class 2452 (via interface_seed class#2445)', 'BrotliEncoderCompressStream: total_out#7 arg-null-literal + next_out#6 depth2-storage-shape-held (generator)'
            elif 'InitBlockEncoder' in seed or s.startswith('InitBlockEncoder::'):
                sub, ev = 'root unrecorded (InitBlockEncoder seed; partition_root -)', 'generator by default until 55 records the root (R774-1 item 2)'
            elif 'BrotliBuildMetaBlockGreedyInternal' in seed:
                sub, ev = 'root mb#12 (class 2772)', 'depth2-storage-shape-held (generator)'
            elif f.get('attribution') == 'graft-held:c9':
                sub, ev = 'graft-held:c9 (ProcessRepeatedCodeLength)', 'graft hold (generator)'
    if r['group'] == 'X' and s in X_SIDE:
        cause, sub, ev = 'side-condition', 'cascade', 'class 139/140/149 held:dropped-site:seam-positive-retention (output-storage certificate absent)'
    out.append([p, r['subject_key'], r['group'], lab, cause, sub, ev])
w = csv.writer(open(f'{OUT}/rows.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program', 'subject_key', 'group', 'label', 'cause', 'sub', 'evidence'])
w.writerows(out)
w = csv.writer(open(f'{OUT}/label-defaults.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['label', 'default_cause', 'rule'])
for k, (c, e) in sorted(D.items()):
    w.writerow([k, c, e])
w.writerow(['(any other label)', 'generator', 'R770-1: the default'])
tot = collections.Counter(x[4] for x in out)
per = collections.defaultdict(collections.Counter)
lab = collections.defaultdict(collections.Counter)
for x in out:
    per[x[0]][x[4]] += 1; lab[x[3]][x[4]] += 1
CAUSES = ['held', 'no-safe-form', 'undefined', 'type-system', 'side-condition', 'form-fact', 'generator']
w = csv.writer(open(f'{OUT}/totals.tsv', 'w'), delimiter='\t', lineterminator='\n')
w.writerow(['program'] + CAUSES + ['total'])
for p in sorted(per):
    w.writerow([p] + [per[p][c] for c in CAUSES] + [sum(per[p].values())])
w.writerow(['total'] + [tot[c] for c in CAUSES] + [sum(tot.values())])
print('rows', len(out), dict(tot))
for l in sorted(lab, key=lambda l: -sum(lab[l].values())):
    print(f'{sum(lab[l].values()):4d} {l:40s}', dict(lab[l]))
used = {k for k in O if any((x[0], short(x[1])) == k for x in out)}
print('overrides not matched:', sorted(set(O) - used))
