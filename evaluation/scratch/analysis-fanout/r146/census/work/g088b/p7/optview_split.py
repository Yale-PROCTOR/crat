"""main 212's optview.py, split: the raw -> Option<&T> call-argument views by (program, callee, param_index, template).
param_index 18446744073709551615 (usize::MAX) is no formal. Read-only over <census>/*.raw-boundary-adapters.tsv."""
import glob, os, collections, sys
d = sys.argv[1]
T = {'optional', 'c-raw-option-mut', 'c-raw-option-shared'}
c = collections.Counter()
for f in sorted(glob.glob(os.path.join(d, '*.raw-boundary-adapters.tsv'))):
    p = os.path.basename(f).split('.raw-boundary')[0]
    L = open(f).read().splitlines(); h = L[0].split('\t'); ix = {k: i for i, k in enumerate(h)}
    for l in L[1:]:
        x = l.split('\t')
        if x[ix['kind']] != 'placed' or x[ix['context']] != 'call-argument' or x[ix['found_form']] != 'raw': continue
        if x[ix['template']] in T and x[ix['expected_form']].startswith('opt-ref'):
            c[(p, x[ix['owner_fn']], x[ix['param_index']], x[ix['template']])] += 1
tot = collections.Counter(); fm = collections.Counter()
for k, v in sorted(c.items()):
    print(v, *k, sep='\t')
    noformal = k[2] == '18446744073709551615'
    tot['no-formal' if noformal else 'formal'] += v
    fm['no-formal' if noformal else 'formal'] += 1
print('sites', dict(tot), 'formals(distinct callee,param)', dict(fm))
