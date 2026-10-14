import csv,glob,os,collections,sys
csv.field_size_limit(10**9)
M='scratch/main/'
for b in sys.argv[1:]:
    tot=0; tot_casc=0; det=collections.Counter()
    for f in sorted(glob.glob(M+b+'/*.raw-boundary-subject-outcomes.tsv')):
        p=os.path.basename(f).split('.raw-boundary')[0]
        diagf=set(r['function'] for r in csv.DictReader(open(f'{M}{b}/{p}.raw-boundary-compiler-diagnostics.tsv'),delimiter='\t'))
        fr=list(csv.DictReader(open(f'{M}{b}/{p}.raw-boundary-final-reverts.tsv'),delimiter='\t'))
        cols=list(fr[0].keys()) if fr else []
        # class id column = 4th field after program: e.g. local-def-index
        idx={}
        for r in fr:
            v=list(r.values())[13:]
            idx.setdefault(v[3],set()).add(v[2])
        # functions whose class has a diagnostic
        fns=set(diagf)
        for cl,mem in idx.items():
            if mem & diagf: fns |= mem
        verif=set(list(r.values())[15] for r in fr if list(r.values())[17]=='verify-reverted') if fr else set()
        subj={r['subject_key']:r for r in csv.DictReader(open(f'{M}{b}/{p}.raw-boundary-subjects.tsv'),delimiter='\t')}
        for r in csv.DictReader(open(f),delimiter='\t'):
            if r['delivery']!='reverted': continue
            mk=subj[r['subject_key']]['model_kind']
            if mk not in('ref','owning'): continue
            if r["owner_fn"] in fns: tot+=1; det[(p,"class-joined")]+=1; print("ROW",b,p,r["subject_key"],mk,r["owner_fn"])
            tot_casc+=1; det[(p,'any-reverted-safe-model')]+=1
    print(b,'class-joined',tot,'all reverted safe-model',tot_casc,dict(det))
