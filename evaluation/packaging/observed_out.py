#!/usr/bin/env python3
"""R1257-1: the zip's source carries no retained_alias_observed, the per-program table of formals a Miri run had shown
retained. Applied to the head's text before the test cut: the module and its tests are deleted; decision/mod.rs loses
the two module declarations, the doc line naming the table and the call that held a listed formal raw.
DegradeReason::RetainedAlias stays (the retained-access rule uses it). Exact strings, each applied exactly once, or
the derivation stops."""
import os, sys
D = os.environ['W'].rstrip('/') + '/crates/pointer_replacer/src/bo_rewriter/decision/'
GONE = ['retained_alias_observed.rs']
ALSO = ['retained_alias_observed_tests.rs']  # gone already when the removals' *_tests.rs rule ran first
EDITS = [
 ('pub(crate) mod retained_alias_observed;\n#[cfg(test)]\nmod retained_alias_observed_tests;\n', ''),
 ("    /// `observed:<run>` ([`retained_alias_observed`]).\n",
  "    /// the retained-access rule's receipt (the kept access it found).\n"),
 ("""    // Wave-6o relay 146 (R796-1): the retained-alias stop-gap. A listed formal
    // the ladder would deliver (or leaves at the gate mode's
    // `call-site-not-adapted`) is held raw. So is one the ladder leaves raw
    // (R800-2, slicecursor 103): a pass that degrades it `ptr-comparison` or
    // `opt-use-unsupported` is one the cursor family selects, so a formal that
    // kept its own reason came back as a cursor (bzip2 `BZ2_bzDecompress::strm`).
    if let Some(detail) = retained_alias_observed::held(ctx.tcx, subject) {
        return degrade(
            subject,
            EmitabilityFacts::site(ctx.tcx, subject.attribution_span()),
            DegradeReason::RetainedAlias { detail },
        );
    }
""", ''),
]
bad = 0
for f in GONE:
    if os.path.exists(D + f): os.remove(D + f)
    else: print(f'   MISSING-FILE\tdecision/{f}'); bad += 1
for f in ALSO:
    if os.path.exists(D + f): os.remove(D + f)
p = D + 'mod.rs'; s = open(p).read()
for old, new in EDITS:
    c = s.count(old)
    if c == 1: s = s.replace(old, new)
    else: print(f'   UNAPPLIED({c})\tdecision/mod.rs\t{old[:70]!r}'); bad += 1
open(p, 'w').write(s)
left = s.count('retained_alias_observed')
print(f'   retained_alias_observed out: {len(GONE) + len(ALSO)} files gone, {len(EDITS)} edits in decision/mod.rs, '
      f'{left} mentions left there, {bad} failed')
sys.exit(1 if bad or left else 0)
