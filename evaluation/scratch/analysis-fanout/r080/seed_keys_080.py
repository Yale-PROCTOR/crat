#!/usr/bin/env python3
"""relays 080 (R824) and 081 (R826): Q7/Q8 keys at 54' and the labels of three user decisions, in paper/numbers-of-record.md.
Usage: seed_keys_080.py <numbers-of-record.md> <release.json>   (release.json: the syntax-tree counts, task C)"""
import sys, json
P = sys.argv[1]; REL = json.load(open(sys.argv[2]))
L = open(P).read().split('\n')
def idx(k):
    h = [i for i, l in enumerate(L) if l.startswith('| ' + k + ' |')]
    assert len(h) == 1, (k, h); return h[0]
def cells(i): return [x.strip() for x in L[i].strip().split('|', 6)]
REC = ("provisional: analysis-fanout 061 (relays 080/081), the census of record 54' (batch 54' landed 2b196a2ed, census head 5948d74f6, "
       "scratch/main/b54p, frame L01^13), scripts agents/artifacts/2026-10-05-analysis-fanout-061/; re-seeded at each census of record. ")
def row(k, v, layer, unit, prov): return f'| {k} | {v} | pending | {layer} | {unit} | {prov} |'
def append_prov(k, text):
    i = idx(k); assert L[i].endswith(' |'), k
    L[i] = L[i][:-2].rstrip() + ' ' + text + ' |'
new = []
def add(k, v, layer, unit, prov): new.append(row(k, v, layer, unit, REC + prov))
# ---- Q8: units kept whole in their original form before any compile
FR = "raw-boundary-final-reverts.tsv rows with attribution held:* (a unit = one function kept in its original form because an edit it requires could not be produced; before any compile). "
SO = "Declarations = raw-boundary-subject-outcomes.tsv rows whose exclusion is terminal-not-applied:*, all inside a held unit (14 held units carry none). "
add('verify.held-units', 60, 'delivered', 'count', FR + "brotli 27, binn 10, libzahl 7, lodepng 7, heman 5, quadtree 2, libtree 1, robotfindskitten 1.")
add('verify.held-units.programs', 8, 'delivered', 'count', FR + "Programs with a held unit.")
add('verify.held-units.declarations', 87, 'delivered', 'count', SO + "brotli 53, binn 16, heman 7, lodepng 4, libzahl 3, quadtree 3, robotfindskitten 1.")
for head, u, d in [('dropped-site', 31, 64), ('blocked-subject', 23, 14), ('dependency-class-held', 4, 8), ('a5-fallback-unrenderable', 1, 0), ('intra-class-interval-overlap', 1, 1)]:
    add(f'verify.held-units.{head}', u, 'delivered', 'count', FR + f"Reason head held:{head}.")
    add(f'verify.held-units.{head}.declarations', d, 'delivered', 'count', SO + f"In units with reason head held:{head}.")
add('verify.held-units.callee-retains', 13, 'delivered', 'count', FR + "Units held because a callee keeps a pointer passed from them: held:dropped-site:seam-positive-retention (9) and held:dropped-site:a5-site-proof-reclassified:seam-positive-retention (4); binn 8, brotli 5 (no heman unit).")
add('verify.held-units.callee-retains.declarations', 25, 'delivered', 'count', SO + "In the 13 callee-retains units (exclusion ...seam-positive-retention 18 + ...a5-site-proof-reclassified 7).")
# ---- Q8: the verification loop
PK = "per-program.kv (raw_boundary_verify_rounds, raw_boundary_bisect_probes / class_bisect_probes, raw_boundary_outcome_kind, raw_boundary_atom_*). "
add('verify.first-check-passed.programs', 19, 'delivered', 'count', PK + "Programs with verify_rounds = 1 (all but libzahl).")
add('verify.rounds.max', 2, 'delivered', 'count', PK + "The most rounds in a program (libzahl).")
add('verify.search.programs', 0, 'delivered', 'count', PK + "Programs with bisect_probes > 0 or class_bisect_probes > 0.")
add('verify.unchanged-output.programs', 0, 'delivered', 'count', PK + "Programs whose outcome_kind is not emitted (all twenty: emitted).")
add('verify.atom-takeback.declarations', 0, 'delivered', 'count', PK + "Declarations taken back alone by the one bounded step: atom_successes 0 in every program; its one attempt, libzahl's atom_ambiguous = 1, fell back to the whole unit. brotli and lil print no atom counters.")
add('verify.planning-reverted.graft-held', 3, 'delivered', 'count', "raw-boundary-final-reverts.tsv graft-held:c9, brotli ProcessRepeatedCodeLength (3 declarations reverted: code_length_histo, prev_code_len, symbol); the unit whose edit could not be placed. Part of verify.planning-reverted = 7. " + REC)
add('verify.planning-reverted.closure', 4, 'delivered', 'count', "raw-boundary-final-reverts.tsv closure:partition, brotli BuildAndStoreBlockSwitchEntropyCodes (4 declarations: self_0, storage, storage_ix, tree); the unit that depended on a held unit. Part of verify.planning-reverted = 7. " + REC)
add('verify.dependency-only.units', 5, 'delivered', 'count', "Units that keep their original form only because a unit they depend on does: held:dependency-class-held 4 (binn AdvanceDataPos, brotli BrotliCreateBackwardReferences and ChooseHasher, quadtree find_) + closure:partition 1 (brotli BuildAndStoreBlockSwitchEntropyCodes). " + REC)
# ---- the release (syntax tree)
SY = "Counted on the syntax tree (syn 2) of the emitted trees and their derived inputs, function by function (agents/artifacts/2026-10-05-analysis-fanout-061/release-tool/). "
add('codegen.release.functions-differ', REL['functions_differ'], 'delivered', 'count', SY + "Functions where the input's free calls differ from the output's free + drop calls, with each exposure wrapper's __crat_safe_X body folded into X (12 functions differ under a plain name match -- lil 5, tulipindicators 1 pair -- all because the body, with its free, moved into __crat_safe_X). Input 185 free = output 166 free + 19 drop; BrotliFree 133 = 133, lodepng_free 69 = 69, and 25 other program release functions equal per program.")
add('codegen.rewrite.forget.sites', REL['forget'], 'delivered', 'count', SY + "mem::forget, ManuallyDrop and Box::leak occurrences in the outputs.")
add('codegen.rewrite.box-into-raw.sites', REL['into_raw'], 'delivered', 'count', SY + REL['into_raw_note'])
add('codegen.rewrite.box-from-raw.sites', REL['from_raw'], 'delivered', 'count', SY + REL['from_raw_note'])
i = idx('verify.planning-reverted'); L[i+1:i+1] = new
# waiver.recursive-leak: the manuscript's key
i = idx('waiver.recursive-leak'); c = cells(i); assert c[2] == '', c
L[i] = row('waiver.recursive-leak', REL['forget'], c[4], c[5], REC + SY + "The forget(replace(..)) leak of an overwritten recursive owner; 0 forget / ManuallyDrop / Box::leak in the outputs at 54'.")
# ---- 081 R826-1: the (E) check
E = ("R826-1 (USER 2026-10-05 ~09:25Z): the retained-access check is (E), the evident shapes held by rule, with the named condition P9 RetainedAccessFreedom for the rest; "
     "in the tree from batch 57; EMPTY until then. Provisional, NOT FOR PRINT: era-5c 143a at 54' N 647 / d 357 -> 3,018 / 3,623 = 83.30 % (old definition 3,018 / 4,270 = 70.7 %); record line (L01^11) N 617 / d 352 -> 81.89 %.")
for k in ['rq1.frame-safe-decisions.amended', 'rq1.frame-withdrawn.retained-access', 'rq1.frame-realization-rate.amended', 'rq1.frame-realization-rate.old-definition',
          'rq1.record-frame.withdrawn.retained-access', 'rq1.record-frame.withdrawn.retained-access.delivered', 'rq1.record-frame.realization-rate.amended']:
    append_prov(k, E)
PROGS = ['avl','binn','brotli','bst','buffer','bzip2','genann','heman','ht','jsonh','libcsv','libtree','libzahl','lil','lodepng','quadtree','rgba','robotfindskitten','tulipindicators','urlparser']
enew = [f"| rq1.frame-withdrawn.retained-access.delivered |  | pending | delivered | count | {E} This key: d, the delivered among the withdrawn. |"]
for rule, what in [('derived-store', 'a declaration whose referent has a pointer derived from it stored by the program'), ('self-container', 'a referent reached through an object that points into itself or to its container')]:
    enew.append(f"| rq1.frame-withdrawn.retained-access.{rule} |  | pending | decided | count | {E} This key: N for the rule '{what}'. |")
    enew.append(f"| rq1.frame-withdrawn.retained-access.{rule}.delivered |  | pending | delivered | count | {E} This key: d for that rule. |")
for p in PROGS:
    enew.append(f"| rq1.frame-withdrawn.retained-access.{p} |  | pending | decided | count | {E} This key: N in {p}. |")
    enew.append(f"| rq1.frame-withdrawn.retained-access.{p}.delivered |  | pending | delivered | count | {E} This key: d in {p}. |")
i = idx('rq1.frame-withdrawn.retained-access'); L[i+1:i+1] = enew
# ---- 081 R826-3: RQ6 baseline
RQ6 = "R826-3 (USER): RQ6's priority is lowered; no rows against L01^14. Measured at L01^13; the lending case at a copy between two locals changes no total (rq3-inator 015)."
n6 = 0
for i, l in enumerate(L):
    if l.startswith('| rq6.') and l.endswith(' |'):
        L[i] = l[:-2].rstrip() + ' ' + RQ6 + ' |'; n6 += 1
NF = "NOT TO BE FILLED (R826-3, relay 081): no row is measured against L01^14; the second host's figures stay in this provenance as information."
for k in ['analysis.copy-lend.swaps', 'analysis.copy-lend.swaps.brotli', 'analysis.copy-lend.swaps.binn', 'analysis.copy-lend.swaps.heman', 'analysis.copy-lend.owners-created', 'analysis.copy-lend.guard-dropped']:
    append_prov(k, NF)
# ---- 081 R826-2 and 080 item 4
append_prov('waiver.sibling-sites', "Temporary waiver (2026-09-08), decision pending (R826-2): the user decides between making it permanent and holding the rows.")
for k in ['waiver.sibling-parameters', 'waiver.sibling-unknown']:
    append_prov(k, "The seat recommends that the paper drop this key (its note of 2026-10-05 08:39Z, part C item 6); it stays empty (relay 080 item 4).")
open(P, 'w').write('\n'.join(L))
print('added', len(new), '+', len(enew), '(E) keys; rq6 rows marked', n6)
# ======== relay 082 (R827-1): the length keys ========
L = open(P).read().split('\n')
LEN56 = ("EMPTY until the first census of record that carries the array-length bound analysis of the code generator (callee_bound.rs, field_count.rs; "
         "R827-1, rides batch 56; the seat's note of 2026-10-05 09:38Z). ")
lnew = []
for cls, what in [('constant', 'a constant index p[c] gives c + 1'), ('loop', 'an access p[i] under while (i < X) gives X'), ('call', "a callee's own bound, instantiated at the call")]:
    for m, mw in [('must', "every access runs on every call (evidence; receipt len-callee-bound:must:<expr>)"),
                  ('may', "on the paths that read (inferred, path-conditional; under the slice-extent waiver, R707-1; receipt len-callee-bound:may:<expr>); printed beside waiver.fallback-extent, never added to the lengths with evidence without that qualifier")]:
        lnew.append(f"| codegen.length.callee-bound.{cls}.{m} |  | pending | delivered | count | {LEN56}Slices whose length is inferred from the callee's accesses, class '{what}', {mw}. |")
for m in ['must', 'may']:
    lnew.append(f"| codegen.length.callee-bound.{m} |  | pending | delivered | count | {LEN56}All classes, {m}. |")
lnew.append(f"| codegen.length.len-field-count |  | pending | delivered | count | {LEN56}Slices over a pointer field F whose length is the count field C paired with it, proved from the program (field_count.rs; holds on every path). |")
EV = ("Lengths with evidence at the census of record 54' (relay 082 item 2): bridge receipts (raw-boundary-bridge-receipts.tsv) with extent_kind evidence(...), stage terminal, state applied, "
      "distinct site_key, multi-line cells rejoined; the slice-construction receipts' 101 evidence rows are the same sites as the bridge's slice-local-construction rows and are not added. "
      "1,445 evidence-labelled sites = 908 with evidence + 537 whose length rests on a fallback extent underneath (separate keys). analysis-fanout 061. ")
for k, v, w in [('slice-length', 95, "an existing slice's own length (runtime-binding-length, delivered-parameter-slice, derived-cursor-base, sealed-contract array-field-reborrow / computed-suffix-copy); brotli 49, binn 20, bzip2 19, heman 7. Relative to that slice: if it was itself built with the fallback, the receipt says so only for table rows"),
                ('array-or-constant', 188, "an array type or a constant (an integer, a nested descriptor array, a byte-literal's size, a type's size, sealed array-length) outside C library calls; tulipindicators 131, brotli 43, lodepng 6, json.h 4, urlparser 2, buffer 1, libtree 1"),
                ('count-argument', 76, "a count passed beside the pointer (associated-argument; counted-void read alias); tulipindicators 73, libcsv 3"),
                ('libc-contract-count', 527, "the count that a C library contract names (bridges into C library calls, arm c: memcpy / memset / fread / fwrite / snprintf ... count arguments, constant or expression); brotli 177, bzip2 85, lodepng 81, genann 56, binn 43, buffer 30, tulipindicators 24, urlparser 17, lil 6, heman 5, rgba 2, libtree 1"),
                ('c-string', 22, "a C string's length (CStr::from_ptr(..).to_bytes().len() + 1, at a NUL-terminated contract position); urlparser 13, binn 3, rgba 2, brotli, ht, libtree, lil 1 each")]:
    lnew.append(f"| codegen.length.evidence.{k} | {v} | pending | delivered | count | provisional: {EV}This key: {w}. |")
lnew.append(f"| codegen.length.evidence | 908 | pending | delivered | count | provisional: {EV}This key: the five sources together. |")
lnew.append(f"| codegen.length.fallback-inherited | 537 | pending | delivered | count | provisional: {EV}This key: receipts labelled evidence whose length rests on a fallback extent: 511 tulipindicators table rows (runtime-binding-length;outer-table-element:extent-fallback-receipted -- the rows are built with FALLBACK_SLICE_EXTENT, e.g. ti_adosc's wrapper) + 26 fallback-base:extent-receipted-at-constructor (tulipindicators 13, genann 10, json.h 3). NOT lengths with evidence. |")
lnew.append("| codegen.length.constant-bound.record | 67 | pending | delivered | count | provisional: wave-4 report 080 (relay 096; the logging variant exc-small-0575b61b4 on the eighteen at 54'): the R677-6 arm already in the tree -- a constant bound proved by accesses that run on every call, at call arguments; 67 distinct sites, at each of which the bound analysis gives len-callee-bound:must with the same N (the analysis subsumes it). The census tables do not label these sites apart (they are among the constant / contract evidence above). Brotli and lil not in the 67. |")
FB55 = {'avl':0,'binn':13,'brotli':404,'bst':0,'buffer':17,'bzip2':11,'genann':26,'heman':49,'ht':2,'jsonh':3,'libcsv':0,'libtree':10,'libzahl':0,'lil':41,'lodepng':99,'quadtree':0,'rgba':0,'robotfindskitten':0,'tulipindicators':324,'urlparser':24}
lnew.append("| waiver.fallback-extent.before | 1023 | pending | delivered | count | provisional: the uses of FALLBACK_SLICE_EXTENT at the census of record 54' (055's method), kept as the BEFORE of the bound analysis (relay 082 item 1); waiver.fallback-extent is the AFTER once the census that carries the line is of record. analysis-fanout 061. |")
for p, v in FB55.items():
    lnew.append(f"| waiver.fallback-extent.before.{p} | {v} | pending | delivered | count | provisional: uses at 54' in {p} (055's method; agents/artifacts/2026-10-04-analysis-fanout-055/fallback-uses-b54p.txt). The BEFORE (relay 082). |")
    lnew.append(f"| waiver.fallback-extent.{p} |  | pending | delivered | count | {LEN56}The AFTER in {p}: uses of FALLBACK_SLICE_EXTENT at that census, 055's method. |")
i = idx('waiver.fallback-extent'); L[i+1:i+1] = lnew
open(P, 'w').write('\n'.join(L)); print('082 keys added', len(lnew))
