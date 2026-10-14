# notes146.py: per-key remarks appended to the cause by assemble146.py (exec'd there; NOTE is its dict; V / DET / M / O / HEAD in scope).
# Every number written here is re-checked against the 60s' measurement below (fail closed).
def need(c, m):
    if not c: raise SystemExit('notes146: ' + m)
v = V['batch60sp']
need(v['waiver.fallback-extent'] == '816' and v['waiver.entry-pairs'] == '59' and v['waiver.entry-static'] == '54', 'tree/entry values')
need(v['codegen.pairs.overlapping'] == '149' and v['codegen.pairs.overlapping.raw-view'] == '54' and v['codegen.pairs.overlapping.same-object'] == '28'
     and v['codegen.pairs.overlapping.held'] == '15' and v['codegen.pairs.overlapping.proof-accepted'] == '0', 'pair split')
need(v['codegen.pair-cert.total'] == '3195', 'cert total')
need(v['verify.held-units'] == '87' and v['verify.planning-reverted.closure'] == '1' and v['codegen.rewrite.function-revert.sites'] == '88', 'verify')
need(v['(info) free-drop'] == '185 158 27', 'free/drop')
need(v['codegen.rewrite.box-into-raw.sites'] == '127' and v['codegen.rewrite.box-from-raw.sites'] == '110', 'box')
need(v['waiver.waived-bridges'] == '325' and v['waiver.waived-bridges.tier-2'] == '0', 'waived')
need(v['waiver.exported-producer'] == '14', 'producer')
need(v['(info) lend-sites'] == V['batch58pps39']['(info) lend-sites'], 'lend site set moved')
p11 = open(f'{O}/p11-batch60sp.txt').read()
need('R486-2 StaticVsEntryWaived: rows 54, sites 54 (libzahl 54/54)' in p11, 'p11')
need("tier2_bridge_rows=1050" in open(f'{M}/batch60sp/census-receipt.txt').read(), 'tier2 receipt line')
need("tier2_bridge_rows" not in open(f'{M}/batch58pps39/census-receipt.txt').read(), 'tier2 line at 58ppp')
NOTE.update({
 'waiver.fallback-extent': "unit = uses of FALLBACK_SLICE_EXTENT in the emitted trees (055), +3 in tulipindicators (313 -> 316); main's section-77 figure (batch60sp-waivers.txt: 216) is a different unit, reproduced here: rows (plan + terminal) of slice-construction-receipt under waiver slice-extent-out-of-scope@addendum-77 = 108 sites x 2, 104 terminal applied (rows brotli 42, buffer 2, genann 4, heman 68, libtree 4, libzahl 2, lil 2, lodepng 6, tulipindicators 86; 102 applied on main/batch58pps39)",
 'waiver.fallback-extent.programs': "the same fourteen programs as on main/batch58pps39",
 'waiver.entry-pairs': "same unit as main's R462 figure (batch60sp-waivers.txt: exported-entry:same-pointee-mut-pair 59), reproduced: rows of raw-boundary-exported-entry-pairs; the +1 is libzahl (0 -> 1)",
 'waiver.entry-static': "the record's unit (distinct argument pairs of the sibling-predicate audit certified pair-disjoint:static-vs-entry:exported-entry-static-waiver: libzahl 42, brotli 8, heman 4); main's R486-2 unit (main/p11count.py: raw-boundary-pairs rows whose peer_receipts name the waiver) reads 54 rows / 54 sites, all libzahl, reproduced -- equal numbers, different units",
 'codegen.pair-cert.static-vs-entry-waived': "see waiver.entry-static: main's R486-2 54 (all libzahl) counts raw-boundary-pairs rows, this key counts audit pairs",
 'waiver.waived-bridges.tier-2': "derived from the per-program bridge receipts (waiver_id retention-waiver:tier-2@2026-09-21, terminal applied): 0 applied, 1 planned and dropped (bzip2); the census receipt now carries tier2_bridge_rows=1050 (absent on main/batch58pps39), a different unit: bo_c1.rs counts there the exclusion-artifact rows of subkinds flows-into-raw-param/retention-unknown-local, arg-stays-raw/raw-caller-boundary and class-collateral/*, not bridges applied under the tier-2 waiver",
 'waiver.waived-bridges': "all 325 under c-aliasing-semantics-at-unsafe-bridges/v1, tier-2 0; the +4 is tulipindicators",
 'waiver.lend-indirect-call.sites': "the identical 77-site set on the S39 cache and the 60-KINDORDER cache",
 'codegen.pairs.overlapping': "a fifth reason not in the record's split: pair-not-shown-disjoint 52 rows (role blocked, the R833 pair hold: brotli 20, libzahl 20, lodepng 9, bzip2 2, heman 1); 149 = raw-view 54 + proof-accepted 0 + same-object 28 + held 15 + not-shown-disjoint 52",
 'codegen.pair-cert.total': "includes two kinds the record's list has no key for: pair-disjoint:allocator-contract-free 28 (brotli; = P11's premise=allocator-contract 28 rows) and pair-disjoint:caller-parameter-pair 17 (brotli); the eleven named kinds sum to 3150",
 'codegen.rewrite.reborrow-mut.sites': "the key is SUPERSEDED (relay 083) by codegen.rewrite.deref-mut.*; measured anyway by 054's text count (emitted minus input &mut *)",
 'codegen.rewrite.reborrow-mut.programs': "superseded key (relay 083)",
 'codegen.rewrite.reborrow-shared.sites': "the key is SUPERSEDED (relay 083) by codegen.rewrite.deref-shared.*; measured anyway by 054's text count",
 'codegen.rewrite.reborrow-shared.programs': "superseded key (relay 083)",
 'codegen.rewrite.arg-order-hoist.sites': f"by 054's tree method no `let __crat_hoist_<lo>_<index>` remains in any tree; the provenance says these keys come from a raw-boundary-hoists receipt table from batch 56 on, but {M}/batch60sp has no such table, so the tree count is staged",
 'codegen.rewrite.arg-order-hoist.programs': "see .sites: tree count, no raw-boundary-hoists table in the census",
 'codegen.rewrite.field-read-hoist.sites': "tree count (no raw-boundary-hoists table in the census)",
 'rq4.pair.sites': "NOT FOR THE PAPER (R817-1); the mapping step alone gives instrumented 80 / unchecked 17; the record's split comes after a type-check round of the instrumented copy (a build), not run here",
 'verify.search.programs': "no program has bisect or class-bisect probes",
 'verify.rounds.max': "every program's raw_boundary_verify_rounds is 1",
 'verify.first-check-passed.programs': "all twenty pass the first check (brotli and tulipindicators needed 2 and 3 rounds on main/batch58pps39)",
 'verify.planning-reverted.closure': "one closure:partition unit of one declaration: brotli BuildAndStoreBlockSwitchEntropyCodes (tulipindicators ti_find_indicator is gone with smoke::get_array's revert)",
 'verify.dependency-only.units': "held:dependency-class-held 3 (brotli BrotliBuildHuffmanTable, BrotliConvertBitDepthsToSymbols; quadtree find_) + closure 1 (brotli BuildAndStoreBlockSwitchEntropyCodes)",
 'verify.held-units': "brotli 42 -> 34 (all dropped-site), libzahl 15 -> 14 (blocked-subject)",
 'codegen.rewrite.function-revert.sites': "= 87 held units + 1 closure, no verify-reverted unit; by program vs main/batch58pps39: brotli -9, tulipindicators -2, libzahl -1",
 'codegen.rewrite.function-revert.programs': "tulipindicators leaves the set",
 'design.libc-contract-callees': f"raw_boundary_contracts.rs is identical at {HEAD[:9]} and 3eaf5228d (git diff empty)",
 'codegen.release.functions-differ': "input 185 free = output 158 free + 27 drop",
 'codegen.rewrite.drop.sites': "the release tool's drop calls agree: heman 19, bst 2, ht 2, quadtree 2, buffer 1, tulipindicators 1",
 'codegen.rewrite.box-into-raw.sites': "Box::into_raw calls brotli 98 -> 102 and tulipindicators 0 -> 1; heman's 6 and quadtree's 5 value paths unchanged",
 'codegen.rewrite.box-from-raw.sites': "Box::from_raw calls brotli 98 -> 102 and tulipindicators 1 -> 2",
 'waiver.exported-producer': "the 8 new rows are heman's kmAABB2Initialize, kmAABB3Initialize, kmMat3Multiply, kmMat3Transpose, kmPlaneFromPoints, kmQuaternionMultiply, kmVec2MidPointBetween, kmVec3TransformCoord",
 'codegen.rewrite.bridge.applied.sites': "by program vs main/batch58pps39: brotli +77, tulipindicators +58, heman +45, libzahl +4",
 'codegen.rewrite.bridge.sites': "by program vs main/batch58pps39: heman +45, brotli -11, libzahl -9, tulipindicators -2",
 'codegen.rewrite.mechanical-obligation.sites': "by program vs main/batch58pps39: tulipindicators +31, brotli +10",
 'codegen.rewrite.option-presentation.sites': "the +22 is tulipindicators",
 'codegen.rewrite.as-deref-mut.sites': "by program vs main/batch58pps39: heman +25, brotli +4, tulipindicators +1",
})
