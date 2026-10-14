"""r140: premise.allocator-contract.* (P5) re-implemented from analysis-fanout 045's printed method (alloc-contract-b54p.out; the script
itself is not in the artifact): admitted subjects = distinct `subject` of <p>.raw-boundary-allocator-contract-receipt.tsv rows of kind
`admitted`, joined to subject-outcomes by owner-short::binding; declarations = admitted AND realized-as-predicted (brotli; urlparser's
libc contract listed apart). pair rows = <p>.raw-boundary-pairs.tsv rows whose peer_receipts name distinct-roots:allocator-contract."""
import csv, glob, os, re, sys, collections
csv.field_size_limit(10**9)
C = sys.argv[1]
for f in sorted(glob.glob(C + '/*.raw-boundary-allocator-contract-receipt.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    rs = list(csv.DictReader(open(f), delimiter='\t'))
    kinds = collections.Counter(r['kind'] for r in rs)
    adm = {r['subject'] for r in rs if r['kind'] == 'admitted'}
    if not rs: continue
    oc = {}
    for r in csv.DictReader(open(f'{C}/{p}.raw-boundary-subject-outcomes.tsv'), delimiter='\t'):
        k = re.sub(r'#\d+$', '', r['subject_key']); fn, _, b = k.rpartition('::')
        oc.setdefault(fn.rsplit('::', 1)[-1] + '::' + b, []).append(r)
    st = collections.Counter(); forms = collections.Counter(); unj = []
    for s in adm:
        if s not in oc: unj.append(s); continue
        for r in oc[s]:
            st[(r['family'], r['delivery'])] += 1
            if r['delivery'] == 'realized-as-predicted': forms[r['emitted_form']] += 1
    print(p, 'receipt kinds', dict(kinds), 'admitted', len(adm), dict(st), 'delivered forms', dict(forms), 'unjoined', len(unj))
rows = recs = 0; sites = collections.Counter()
for f in sorted(glob.glob(C + '/*.raw-boundary-pairs.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    for r in csv.DictReader(open(f), delimiter='\t'):
        n = r['peer_receipts'].count('distinct-roots:allocator-contract')
        if n:
            rows += 1; recs += n; sites[(p, r['caller'], r['callee'], r['site'])] += 1
print('pair rows', rows, 'receipts', recs, 'distinct (caller,callee,site)', len(sites))
# pair sites: unordered argument pairs at one call (caller, callee, line of the argument span) whose receipt is
# clear:pair-disjoint:distinct-roots:allocator-contract (each pair appears on both arguments' rows; counted once)
ps = collections.Counter()
for f in sorted(glob.glob(C + '/*.raw-boundary-pairs.tsv')):
    p = os.path.basename(f).split('.raw-boundary')[0]
    for r in csv.DictReader(open(f), delimiter='\t'):
        line = r['site'].split(':')[1] if r['site'].count(':') >= 2 else r['site']
        for rc in r['peer_receipts'].split(';'):
            m = re.match(r'(\d+)/(\d+)->(\d+)/(\d+):clear:pair-disjoint:distinct-roots:allocator-contract', rc)
            if m:
                ps[(p, r['caller'], r['callee'], line, frozenset((m.group(1), m.group(2))))] += 1
print('pair sites (unordered argument pairs per call, deduplicated)', len(ps), dict(collections.Counter(k[0] for k in ps)))
