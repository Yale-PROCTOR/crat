import csv,glob,os,sys,collections
csv.field_size_limit(10**9)
for d in sys.argv[1:]:
    c=collections.Counter(); fam=collections.Counter()
    for f in glob.glob(d+'/*.raw-boundary-subject-outcomes.tsv'):
        p=os.path.basename(f).split('.raw-boundary')[0]
        for r in csv.DictReader(open(f),delimiter='\t'):
            if r['delivery']=='realized-as-predicted':
                fam[r['emitted_form']]+=1
                if 'box' in r['emitted_form']: c[p]+=1
    print(d, 'box', sum(c.values()), {k:v for k,v in fam.items() if 'box' in k}, dict(sorted(c.items())))
    print(d, 'forms', dict(fam))
