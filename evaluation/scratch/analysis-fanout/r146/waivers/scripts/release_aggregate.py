import collections, sys
rows=[l.rstrip('\n').split('\t') for l in open('out.tsv')]
PROGS="avl binn brotli bst buffer bzip2 genann heman ht json.h libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser".split()
fns={s:collections.defaultdict(collections.Counter) for s in('input','output')}
defs={s:collections.defaultdict(list) for s in('input','output')}
occ=collections.defaultdict(list)  # (side,prog,key,cat)->lines
def last(n): return n.split('::')[-1]
for side,prog,key,kind,name,line,arg in rows:
    if kind=='fndef':
        defs[side][prog].append(key); continue
    L=last(name)
    if kind=='call' and L=='free': cat='free'
    elif kind=='call' and L=='drop': cat='drop'
    elif kind=='call' and L in('BrotliFree','lodepng_free'): cat=L
    elif name.endswith('Box::into_raw'): cat='into_raw.'+kind
    elif name.endswith('Box::from_raw'): cat='from_raw.'+kind
    elif name.endswith('Box::leak'): cat='leak.'+kind
    elif L=='forget': cat='forget.'+kind
    elif 'ManuallyDrop' in name: cat='ManuallyDrop.'+kind
    else: continue
    fns[side][(prog,key)][cat]+=1
    occ[(side,prog,key,cat)].append(int(line))
print('## duplicate fn keys (same key defined twice in one file)')
for s in defs:
    for p,ks in defs[s].items():
        d=[k for k,c in collections.Counter(ks).items() if c>1]
        if d: print(s,p,len(d),d[:5])
print('## unmatched fn keys')
for p in PROGS:
    i=set(defs['input'][p]); o=set(defs['output'][p])
    print(f"{p}\tinput_fns={len(i)}\toutput_fns={len(o)}\tinput_only={len(i-o)}\toutput_only={len(o-i)}")
    for k in sorted(i-o): print('   input-only',k)
    oo=sorted(o-i)
    # group output-only
    def grp(k):
        l=k.split('::')[-1]
        if k.startswith('slice_cursor::') or '::slice_cursor::' in k: return 'slice_cursor module'
        if l.startswith('__crat_safe_'): return '__crat_safe_* wrapper'
        if l.startswith('__crat_raw_'): return '__crat_raw_* twin'
        return 'other'
    g=collections.Counter(grp(k) for k in oo)
    print('   output-only groups',dict(g))
    for k in oo:
        if grp(k)=='other': print('   output-only(other)',k)
def tot(side,prog,cat):
    return sum(c[cat] for (p,k),c in fns[side].items() if p==prog)
print('## (1) per program free')
print('prog\tin_free\tout_free\tout_drop\tout_free+drop\tdelta')
T=[0]*4
for p in PROGS:
    a,b,c=tot('input',p,'free'),tot('output',p,'free'),tot('output',p,'drop')
    T=[T[0]+a,T[1]+b,T[2]+c,T[3]+b+c]
    print(f"{p}\t{a}\t{b}\t{c}\t{b+c}\t{b+c-a}")
print('TOTAL\t'+'\t'.join(map(str,T)))
print('## (1b) functions with input free != output free + drop')
keys=set(fns['input'])|set(fns['output'])
n=0
for (p,k) in sorted(keys):
    a=fns['input'].get((p,k),{}).get('free',0); b=fns['output'].get((p,k),{}).get('free',0); c=fns['output'].get((p,k),{}).get('drop',0)
    if a!=b+c: n+=1; print(p,k,a,b,c, 'in_lines',occ[('input',p,k,'free')],'out_lines',occ[('output',p,k,'free')])
print('mismatch functions:',n)
print('## (1c) input drop calls (should be 0)', sum(tot('input',p,'drop') for p in PROGS))
print('## (2) output drop calls')
for (p,k),c in sorted(fns['output'].items()):
    if c['drop']:
        a=fns['input'].get((p,k),{}).get('free',0)
        print(f"{p}\t{k}\tdrop={c['drop']}\tout_free={c['free']}\tin_free={a}\tdrop_lines={occ[('output',p,k,'drop')]}\tin_free_lines={occ[('input',p,k,'free')]}")
print('## (3) totals by program')
cats=['forget.call','forget.valpath','ManuallyDrop.call','ManuallyDrop.valpath','ManuallyDrop.type','leak.call','leak.valpath','into_raw.call','into_raw.valpath','from_raw.call','from_raw.valpath']
for s in ('input','output'):
    for cat in cats:
        per={p:tot(s,p,cat) for p in PROGS}; per={p:v for p,v in per.items() if v}
        print(s,cat,sum(per.values()),per)
print('## (3b) into_raw valpath sites')
for (s,p,k,cat),ls in sorted(occ.items()):
    if cat in('into_raw.valpath','from_raw.valpath'): print(s,p,k,cat,ls)
print('## (4) BrotliFree / lodepng_free per program and per-function mismatches')
for cat in ('BrotliFree','lodepng_free'):
    for p in PROGS:
        a,b=tot('input',p,cat),tot('output',p,cat)
        if a or b: print(cat,p,'in',a,'out',b)
    for (p,k) in sorted(keys):
        a=fns['input'].get((p,k),{}).get(cat,0); b=fns['output'].get((p,k),{}).get(cat,0)
        if a!=b: print('  mismatch',cat,p,k,a,b)
print('## (5) folded check: fn key __crat_safe_X folded into X, callee __crat_safe_X folded into X; every release-named call, per function, input vs output (free compared with free+drop)')
def fold(k):
    parts=k.split('::'); parts[-1]=parts[-1].replace('__crat_safe_','',1); return '::'.join(parts)
F={s:collections.defaultdict(collections.Counter) for s in('input','output')}
for side,prog,key,kind,name,line,arg in rows:
    if kind!='call': continue
    L=fold(last(name))
    if L.startswith('Box::') or name.endswith(('Box::into_raw','Box::from_raw','Box::leak')): continue
    if L=='drop': L='free'   # drop compared against free
    F[side][(prog,fold(key))][L]+=1
bad=0
for pk in sorted(set(F['input'])|set(F['output'])):
    a=F['input'].get(pk,collections.Counter()); b=F['output'].get(pk,collections.Counter())
    for n in sorted(set(a)|set(b)):
        if a[n]!=b[n]: bad+=1; print('  MISMATCH',pk,n,a[n],b[n])
print('folded mismatches:',bad)
print('## (6) other release-named callees, totals per program (input/output; callee __crat_safe_X folded to X)')
tot2=collections.Counter()
for side,prog,key,kind,name,line,arg in rows:
    if kind=='call':
        L=fold(last(name))
        if L not in('free','drop') and not name.startswith('Box') and 'Box::' not in name: tot2[(prog,L,side)]+=1
for (prog,L) in sorted({(p,l) for p,l,s in tot2}):
    print(f"  {prog}\t{L}\tin={tot2[(prog,L,'input')]}\tout={tot2[(prog,L,'output')]}")
print('## (7) release-named value paths (fn items used as values), totals per program')
v=collections.Counter()
for side,prog,key,kind,name,line,arg in rows:
    if kind=='valpath' and 'Box::' not in name: v[(prog,name,side)]+=1
for (prog,n) in sorted({(p,n) for p,n,s in v}):
    print(f"  {prog}\t{n}\tin={v[(prog,n,'input')]}\tout={v[(prog,n,'output')]}")
