import csv,re,os,collections,sys
csv.field_size_limit(10**9)
def statics(root):
    names=set()
    for dp,_,fs in os.walk(root):
        for f in fs:
            if f.endswith('.rs'):
                for m in re.finditer(r'\bstatic\s+(?:mut\s+)?([A-Za-z_]\w*)\s*:', open(os.path.join(dp,f),errors='replace').read()):
                    names.add(m.group(1))
    return names
src={}
def text_at(root,f,line,col,n=120):
    p=os.path.join(root,f)
    if p not in src: src[p]=open(p,errors='replace').read().split('\n')
    ls=src[p]; i=int(line)-1
    return (ls[i][int(col)-1:]+' '+' '.join(x.strip() for x in ls[i+1:i+3]))[:n]
for side in sys.argv[1:]:
    rows=list(csv.DictReader(open(f'toolmade-{side}.tsv'),delimiter='\t'))
    c=collections.Counter(); ex=[]
    rootcache={}
    for r in rows:
        if not r['kind'].startswith('a:'): continue
        d=f"scratch/analysis-fanout/r132/out/{side}/{r['program']}"
        cmd=open(d+'/cmd.txt').read().split()
        root=os.path.dirname(cmd[cmd.index('--root')+1])
        if root not in rootcache: rootcache[root]=statics(root)
        t=text_at(root,r['file'],r['line'],r['col'])
        m=re.match(r'(?:Some\()?&\s*(?:mut\s+)?\(?\s*([A-Za-z_][\w:]*)',t)
        nm=m.group(1).split('::')[-1] if m else None
        isst = nm in rootcache[root] if nm else False
        c[isst]+=1
        if isst and len(ex)<5: ex.append((r['program'],r['file'],r['line'],r['src_ty'][:30],t[:70]))
    print(side,c); [print('  ',e) for e in ex]
