import glob,collections,sys,os
d=sys.argv[1]
T={'optional','c-raw-option-mut','c-raw-option-shared','c-raw-reborrow-mut','c-raw-reborrow-shared'}
sites=collections.Counter(); formals=collections.defaultdict(set); byprog=collections.defaultdict(collections.Counter)
for f in sorted(glob.glob(os.path.join(d,'*.raw-boundary-adapters.tsv'))):
    p=os.path.basename(f).split('.raw-boundary')[0]
    L=open(f).read().splitlines(); h=L[0].split('\t'); ix={k:i for i,k in enumerate(h)}
    for l in L[1:]:
        x=l.split('\t')
        if x[ix['kind']]!='placed' or x[ix['context']]!='call-argument' or x[ix['found_form']]!='raw': continue
        t=x[ix['template']]; e=x[ix['expected_form']]
        if t not in T: continue
        if t.startswith('c-raw-reborrow'): key='reborrow'
        elif e.startswith('opt-ref'): key='optional-thin'
        else: continue
        sites[key]+=1; formals[key].add((p,x[ix['owner_fn']],x[ix['param_index']])); byprog[key][p]+=1
for k in sites: print(k, 'sites', sites[k], 'formals', len(formals[k]), dict(byprog[k].most_common()))
