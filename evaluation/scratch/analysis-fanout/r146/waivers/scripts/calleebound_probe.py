#!/usr/bin/env python3
"""calleebound_probe.py <census-dir>: for codegen.length.constant-bound.record's cause -- the callee-bound labels in the census
tables (bridge receipts, mechanical obligations, slice-construction receipts): rows carrying one, occurrences, programs, and
whether any R677-6 / must label appears. Rejoined reader."""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import load_rejoin
B = sys.argv[1]; rows = 0; occ = 0; per = collections.Counter(); labels = collections.Counter(); bridge_rows = 0; bp = collections.Counter()
for t in ('raw-boundary-bridge-receipts', 'raw-boundary-mechanical-obligations', 'slice-construction-receipt'):
    tr = to = 0
    for r in load_rejoin(B, t):
        line = '\t'.join(r.values()); f = re.findall(r'callee-bound(?::[\w:-]*)?', line)
        if f:
            rows += 1; tr += 1; occ += len(f); to += len(f); labels.update(f); per[(t, r.get('program'))] += 1
            if t == 'raw-boundary-bridge-receipts': bridge_rows += 1; bp[r.get('program')] += 1
    print(f'{t}\trows {tr}\toccurrences {to}')
print(f'TOTAL rows {rows} occurrences {occ}; bridge rows {bridge_rows} ({dict(bp)}); labels {dict(labels)}; R677-6 or must labels {sum(v for k, v in labels.items() if "must" in k or "677" in k)}')
