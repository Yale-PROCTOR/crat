
### §39 addendum 118 — USER DIRECTION banked: the ADDRESS-OBSERVATION emission arm (comparisons/diffs from safe forms, no demote); two-layer disposition (rewriter arm now-eligible; §29 evidence narrowing = era-priced user item); the no-round-trip guard (2026-09-01)

USER DIRECTION: for arithmetic-class uses — especially
COMPARISON — do not demote the subject; emit an explicit
address-taking operation at the use site, since we do not claim
those semantics anyway. SEAT ANALYSIS, adopted:

THE ARM (better than proposed — mostly SAFE Rust, no unsafe):
for VALUE-OBSERVING pointer uses only —
equality (`ptr::eq`), ordering (`from_ref(p) < from_ref(end)`,
address comparison is defined behavior in Rust), difference
(usize subtraction / size_of division, integer math), and
ptr-to-int observations — the subject KEEPS its safe form and
the use site extracts an address explicitly. Soundness legs:
(1) the emitted forms introduce NO UB — address extraction and
comparison on references are safe, defined Rust; (2)
same-allocation results are preserved (relative addresses within
one allocation survive the rewrite — C's defined case); (3)
cross-allocation result fidelity is discharged by §28 (C's
cross-object comparison/difference was already UB). Receipts:
every address-observation site typed and counted (the waiver
discipline). LOOP NOTE: the idiomatic `p < a+n` loop family
prefers index/cursor rewriting (cursor-wave) — the
address-observation arm is the fallback for irregular shapes.

THE GUARD (load-bearing): the arm covers value-observing uses
ONLY. Any int-to-ptr ROUND-TRIP — an observed address flowing
back into pointer construction or memory ACCESS — is out of the
arm's scope (provenance-losing direction); such sites stay in
the slice/cursor/index families or stay raw. Address values must
be sinks, never sources.

TWO-LAYER DISPOSITION:
- **Layer 1 (rewriter-only, cheap, chartered NOW)**: the arm
  serves the rewriter-side walls — `ptr-comparison` 88 directly,
  plus the value-observing subset of `raw-pointer-operation` 454
  (that wave's census must SPLIT value-observing vs
  access-producing arithmetic before claiming a market). Design
  home: the raw-operation/cursor wave family (harvest banks
  LW-21–LW-25/LW-32–LW-36 adjacent). No analysis thaw needed.
- **Layer 2 (analysis-side, ERA-PRICED, user-level)**: today
  comparison/arithmetic EVIDENCE also drives the MODEL to Raw
  (part of kind-raw 1,245, minted in the solver). Harvesting
  that mass means narrowing §29's "genuinely raw evidence" list
  (comparisons out = kind-neutral) — a CONSTITUTIONAL amendment
  to §29 plus an acceptance-changing analysis edit that re-keys
  the cache (20 re-solves). Registered for the post-Item-E
  analysis batch (ONE-batch/ONE-re-measure rule); the user
  decides when.

No lane order now — E2-FN census r3 is in flight. After E2-FN
closes, the routing menu gains this arm as a strong cheap
candidate alongside the raw-boundary bridge/contract pair.
