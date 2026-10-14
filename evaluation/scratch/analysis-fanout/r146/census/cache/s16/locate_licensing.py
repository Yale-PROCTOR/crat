#!/usr/bin/env python3
"""Find byte offsets of the origin.licensing section of an era5b-model-cache-v1 entry by scanning
BACKWARD from the end in 64 MiB chunks (never loads the entry). Prints start (of the '[' value),
end (of ',"reader_replay":'), and section length."""
import sys, os
CH=64<<20
START=b',"licensing":['
END=b',"reader_replay":'
def locate(path):
    size=os.path.getsize(path)
    with open(path,'rb') as f:
        pos=size; tail=b''; end=None; start=None
        while pos>0:
            n=min(CH,pos); pos-=n; f.seek(pos); buf=f.read(n)+tail
            if end is None:
                i=buf.rfind(END)
                if i>=0: end=pos+i
            if end is not None:
                j=buf.rfind(START, 0, end-pos if end-pos>=0 else len(buf))
                if j>=0: start=pos+j+len(START)-1; break
            tail=buf[:len(START)+len(END)]
    return size,start,end
if __name__=='__main__':
    for p in sys.argv[1:]:
        size,s,e=locate(p)
        print(os.path.basename(p), size, s, e, (e-s) if s is not None and e is not None else None, flush=True)
