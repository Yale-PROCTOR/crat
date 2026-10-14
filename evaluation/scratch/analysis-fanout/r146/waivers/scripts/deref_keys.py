#!/usr/bin/env python3
"""deref_keys.py <rows.tsv>: the codegen.rewrite.deref-{mut,shared}.* keys from deref-tool rows with analysis-fanout 062's
classify.py classes (imported verbatim); value = occurrences in the outputs (side out). ref-operand = b1 rows whose operand
deref-tool types as a reference (`ref-mut`); ref-reborrow = class e less the type positions."""
import collections, sys, importlib.util, os
rows = [l.rstrip('\n').split('\t') for l in open(sys.argv[1])]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'deref_classify.py')).read()
ns = {}; exec(src.split("form = sys.argv[1]")[0].replace("rows = [l.rstrip('\\n').split('\\t') for l in open('rows.tsv')]", 'rows = ROWS'), {'ROWS': rows, **ns}, ns)
cls = ns['cls']
D = [r for r in rows if r[0] in ('DEREF', 'TYPE') and r[1] == 'out']
for form in ('mut', 'shared'):
    C = collections.Counter(); S = collections.Counter(); ok = collections.Counter(); P = collections.defaultdict(collections.Counter); PD = collections.defaultdict(collections.Counter)
    for r in D:
        if r[5] != form: continue
        c, s = cls(r); C[c] += 1; S[s] += 1; P[c][r[2]] += 1; PD[s[:2]][r[2]] += 1
        if s.startswith('b1'): ok[r[10]] += 1
    tp = sum(v for s, v in S.items() if s.startswith('e-type-position'))
    pp = lambda c: ', '.join(f'{p} {n}' for p, n in sorted(P[c].items(), key=lambda x: -x[1]))
    print(f'deref-{form}.raw-bridge\t{C["a"]}\t{pp("a")}')
    print(f'deref-{form}.raw-view\t{C["b"]}\t{dict((s, v) for s, v in S.items() if s.startswith("b"))}')
    if form == 'mut': print(f'deref-{form}.raw-view.ref-operand\t{ok["ref-mut"]}\tb1 operand kinds {dict(ok)}')
    print(f'deref-{form}.return-reborrow\t{C["c"]}\t{dict((s, v) for s, v in S.items() if s.startswith("c"))}')
    ppd = lambda c: ', '.join(f'{p} {n}' for p, n in sorted(PD[c].items(), key=lambda x: -x[1]))
    print(f'deref-{form}.owner-lend.box\t{sum(v for s, v in S.items() if s.startswith("d1"))}\t{ppd("d1")} (option-box: {ppd("d2") or "none"})')
    print(f'deref-{form}.owner-lend.option-box\t{sum(v for s, v in S.items() if s.startswith("d2"))}\t{ppd("d2")}')
    print(f'deref-{form}.ref-reborrow\t{C["e"] - tp}\t{dict((s, v) for s, v in S.items() if s.startswith("e") and not s.startswith("e-type"))}')
    print(f'deref-{form}.type-position\t{tp}\t')
    print(f'deref-{form}.TOTAL\t{sum(C.values())}\t')
