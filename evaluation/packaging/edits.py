#!/usr/bin/env python3
"""The string edits of relays 001 s4, 003 and 005 (applied AFTER the rename, on jobcrat-form text): host names, process ids and
label strings become neutral. Exact strings; the two name-bearing edits are patterns. A missing string is reported, not fatal."""
import os, sys
W = os.environ['W'].rstrip('/') + '/crates/pointer_replacer/src/'
EDITS = [
 # 001 s4: the worker host names (a pattern; see PATTERNS)
 # relay 003 item 4a: the prelude's five comment lines
 ('bo_rewriter/slice_cursor_prelude.rs', """    // ---- BO addendum (slicecursor lane, relay 009; the legacy text above is
    // preserved verbatim). An ADDRESS view of the cursor's position, used only
    // for orderings and differences: it never indexes, so a position past the
    // window (a C address computed before a clamp) is a value, not a panic.
    // `pos()` is the index the R394-1 form names.
""", ''),
 # relay 003 items 4c/4d
 ('analyses/borrow_ownership/borrow_engine/conflicts.rs', '"verdict=NO-CENSUS"', '"verdict=NO-RECORD"'),
 ('bo_rewriter/decision/option.rs', '"handoff-return:later-return-or-sink-wave"', '"handoff-return:later-return-or-sink"'),
 ('bo_rewriter/mod.rs', '"{}:later-return-or-sink-wave"', '"{}:later-return-or-sink"'),
 ('bo_rewriter/decision/slice_use.rs', '"raw-pointer-movement;separate-cursor-wave"', '"raw-pointer-movement;separate-cursor"'),
 ('bo_rewriter/decision/ownership_fields_native.rs', 'owner-untouched-while-lent=analysis-window+borrow-checker (R805-3, relay 213)"', 'owner-untouched-while-lent=analysis-window+borrow-checker"'),
 ('bo_rewriter/decision/ownership_fields_native.rs', 'owner-live-while-lent=borrow-checker (R805-3)"', 'owner-live-while-lent=borrow-checker"'),
 ('bo_rewriter/decision/ownership_fields_native.rs', 'runtime-checked=slice-start-and-index(R394-1)', 'runtime-checked=slice-start-and-index'),
 ('analyses/borrow_ownership/licensing/stack_export.rs', '", premise=typed-release@R604-1)"', '", premise=typed-release)"'),
 ('analyses/borrow_ownership/licensing/stack_export.rs', '", premise=typed-release@R604-1, containment=sole-type)"', '", premise=typed-release, containment=sole-type)"'),
 ('analyses/borrow_ownership/retirement.rs', '", premise=realloc-nonzero@R684-1"', '", premise=realloc-nonzero"'),
 ('analyses/borrow_ownership/retirement.rs', 'premise=typed-release@R604-1{})"', 'premise=typed-release{})"'),
 ('bo_rewriter/bridge_receipt.rs', '"fallback(mask+1@addendum-77:{source})"', '"fallback(mask+1@fallback-extent:{source})"'),
 ('bo_rewriter/decision/binn_counted.rs', '"width:fallback-extent(R457-5)"', '"width:fallback-extent"'),
 ('bo_rewriter/decision/global_or_integer.rs', 'expected globals-and-integers or integers-only (R944-1)"', 'expected globals-and-integers or integers-only"'),
 ('bo_rewriter/decision/licensed_lift.rs', '"fallback(extent-lift@addendum-77:{}:{index})"', '"fallback(extent-lift@fallback-extent:{}:{index})"'),
 ('bo_rewriter/decision/raw_boundary.rs', '"Tier-2 retention waiver (user ruling 2026-09-21, addendum 130). At a receipted site', '"Tier-2 retention waiver. At a receipted site'),
 ('bo_rewriter/decision/seam.rs', '"mask-plus-one@addendum-77"', '"mask-plus-one@fallback-extent"'),
 ('bo_rewriter/decision/seam.rs', '"fallback-sibling-by-position@addendum-77"', '"fallback-sibling-by-position@fallback-extent"'),
 ('bo_rewriter/mechanical_receipt.rs', '"slice-extent-out-of-scope@addendum-77"', '"slice-extent-out-of-scope@fallback-extent"'),
 ('bo_rewriter/mechanical_receipt.rs', '"fabricated-extent:slice-extent-out-of-scope@addendum-77:FALLBACK_SLICE_EXTENT={}"', '"fabricated-extent:slice-extent-out-of-scope@fallback-extent:FALLBACK_SLICE_EXTENT={}"'),
 # report 005 / 006: initials, dated ids, lower-case ruling ids, observer labels, frame key
 ('analyses/borrow_ownership/licensing/lend.rs', '"retention-waiver:tier-2@2026-09-21"', '"retention-waiver:tier-2"'),
 ('bo_rewriter/decision/raw_boundary.rs', '"retention-waiver:tier-2@2026-09-21"', '"retention-waiver:tier-2"'),
 ('bo_rewriter/bridge_receipt.rs', '"c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01"', '"c-aliasing-semantics-at-unsafe-bridges/v1"'),
 ('bo_rewriter/decision/raw_boundary.rs', '"c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01"', '"c-aliasing-semantics-at-unsafe-bridges/v1"'),
 ('bo_rewriter/decision/allocator_contract.rs', '"allocator-contract:brotli-memory-manager/v1@2026-09-15"', '"allocator-contract:brotli-memory-manager/v1"'),
 ('bo_rewriter/decision/allocator_contract.rs', '"allocator-contract:libc/v1@2026-09-17"', '"allocator-contract:libc/v1"'),
 ('analyses/borrow_ownership/mod.rs', '"r377-return-port"', '"return-port"'),
 ('analyses/borrow_ownership/model_cache.rs', '"r245-ref-inner-demote-realloc-site-hold-v1"', '"ref-inner-demote-realloc-site-hold-v1"'),
 ('analyses/borrow_ownership/model_cache.rs', '"r253-three-dispositions-v1"', '"three-dispositions-v1"'),
 ('analyses/borrow_ownership/model_cache.rs', '"r253-inventory-complete-l2-result-propagation-v1"', '"inventory-complete-l2-result-propagation-v1"'),
 ('analyses/borrow_ownership/model_cache.rs', '"r243-field-test-fallback-both-v1"', '"field-test-fallback-both-v1"'),
 ('analyses/borrow_ownership/solver.rs', '"s23-force",', '"force-own",'),
 ('analyses/borrow_ownership/solver.rs', '"r385-force",', '"force-ref",'),
 ('analyses/borrow_ownership/solver.rs', 'format!("s23-force-own({slot:?})")', 'format!("force-own({slot:?})")'),
 ('analyses/borrow_ownership/solver.rs', 'format!("r385-force-ref({slot:?})")', 'format!("force-ref({slot:?})")'),
 ('bo_rewriter/decision/overlapping_pairs/observer.rs', '"wave5p-observer-program:{error}"', '"observer-program:{error}"'),
 ('bo_rewriter/decision/overlapping_pairs/observer.rs', '"wave5p-observer-invalid-program"', '"observer-invalid-program"'),
 ('bo_rewriter/decision/overlapping_pairs/observer.rs', '"wave5p-observer-directory:{error}"', '"observer-directory:{error}"'),
 ('bo_rewriter/decision/overlapping_pairs/observer.rs', '"wave5p-observer-create:{error}"', '"observer-create:{error}"'),
 ('bo_rewriter/decision/overlapping_pairs/observer.rs', '"wave5p-observer-write:{error}"', '"observer-write:{error}"'),
 ('analyses/borrow_ownership/model_cache.rs', 'ANALYSIS_FRAME: &str = "era5c-l01p14-v1"', 'ANALYSIS_FRAME: &str = "frame-v1"'),
]
PATTERNS = [
 # 001 s4: the two worker host names of the model cache become neutral
 ('analyses/borrow_ownership/model_cache.rs', r'(const WORKER_HOSTS: \[&str; 2\] = )\[[^\]]*\];', r'\1["worker-a", "worker-b"];', 1),
 # report 005: a person's initials in two tripwire labels
 ('analyses/borrow_ownership/borrow_engine/loan_liveness.rs', r'"\S+-PORT subset tripwire: ported (loan_liveness|requires) holds', r'"ported-subset tripwire: ported \1 holds', 2),
]
applied = missing = 0
for rel, old, new in EDITS:
    p = W + rel
    try: s = open(p).read()
    except FileNotFoundError: print(f'MISSING-FILE\t{rel}'); missing += 1; continue
    c = s.count(old)
    if c == 1: open(p, 'w').write(s.replace(old, new)); applied += 1
    else: print(f'UNAPPLIED({c})\t{rel}\t{old[:70]!r}'); missing += 1
import re
for rel, pat, rep, expected in PATTERNS:
    p = W + rel
    try: s = open(p).read()
    except FileNotFoundError: print(f'MISSING-FILE\t{rel}'); missing += 1; continue
    s2, c = re.subn(pat, rep, s)
    if c == expected: open(p, 'w').write(s2); applied += 1
    else: print(f'UNAPPLIED({c} of {expected})\t{rel}\t{pat[:70]!r}'); missing += 1
print(f'#EDITS applied={applied} unapplied={missing} of {len(EDITS) + len(PATTERNS)}')
