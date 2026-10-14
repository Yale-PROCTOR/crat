#!/bin/bash
# RQ3: the nine &inator benchmarks through transpile.sh (c2rust c2rust-fork e4a13ca, R684); inputs checked against 016's manifest first.
set -u
R=scratch/analysis-fanout/rq3
B=$R/gh/refinator-impl-4fdf3309d2a3763786b0090ae956940d97661855/benchmarks
M=docs/agents/artifacts/2026-09-29-analysis-fanout-016/inputs-sha256.tsv
O=$R/c2rust-out
python3 - "$B" "$M" <<'PY' || { echo "INPUT MISMATCH"; exit 1; }
import hashlib,sys,os
b,m=sys.argv[1:3]; bad=0
for i,l in enumerate(open(m)):
    if i==0: continue
    x=l.rstrip('\n').split('\t')
    if hashlib.sha256(open(os.path.join(b,x[1]),'rb').read()).hexdigest()!=x[3]: print('differs',x[1]); bad+=1
print('inputs: 58 checked,',bad,'differ'); sys.exit(1 if bad else 0)
PY
mkdir -p $O
for p in running-example ulidgen leftpad amp nandc rbtree carrays jccc tisp; do
  extra=(); [ $p = jccc ] && extra=(-Isrc)
  echo "== $(date -u +%FT%TZ) $p ${extra[*]:-}"
  /usr/bin/time -f "c2rust wall %e s maxrss %M KB exit %x" bash $R/c2rust/transpile.sh $B/$p source.c $O/$p "${extra[@]}" > $O/$p.log 2>&1; echo "exit $? ($(tail -1 $O/$p.log))"
done
python3 - $O <<'PY'
import hashlib,os,sys
o=sys.argv[1]
with open(os.path.join(o,'c2rust-out-sha256.tsv'),'w') as f:
    f.write('program\tpath\tbytes\tsha256\troute\n')
    for p in ['running-example','ulidgen','leftpad','amp','nandc','rbtree','carrays','jccc','tisp']:
        for d in (p, p+'.cc'):
            for dp,dn,fn in sorted(os.walk(os.path.join(o,d))):
                dn.sort()
                for n in sorted(fn):
                    q=os.path.join(dp,n); f.write(f'{p}\t{os.path.relpath(q,o)}\t{os.path.getsize(q)}\t{hashlib.sha256(open(q,"rb").read()).hexdigest()}\tc2rust c2rust-fork e4a13ca\n')
print(open(os.path.join(o,'c2rust-out-sha256.tsv')).read().count('\n')-1,'files in the manifest')
PY
