#!/usr/bin/env python3
"""Forward chunked scan (64 MiB, never loads the file) of a byte range for key markers; prints each hit's absolute offset."""
import sys
CH=64<<20
MK=[b",\"metadata\":{\"bodies\":", b",\"no_ref_carriers\":", b",\"value_origins\":{\"values\":", b",\"offset\":"]
def scan(path, start, end):
    hits=[]
    ov=max(len(m) for m in MK)
    with open(path,'rb') as f:
        pos=start; prev=b''
        while pos<end:
            n=min(CH,end-pos); f.seek(pos); buf=prev+f.read(n); base=pos-len(prev)
            for m in MK:
                i=buf.find(m)
                while i>=0:
                    a=base+i
                    if not hits or (a,m) not in hits[-200:]: hits.append((a,m))
                    i=buf.find(m,i+1)
            prev=buf[-ov:]; pos+=n
    return sorted(set(hits))
if __name__=='__main__':
    p,s,e=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
    for a,m in scan(p,s,e): print(a,m.decode())
