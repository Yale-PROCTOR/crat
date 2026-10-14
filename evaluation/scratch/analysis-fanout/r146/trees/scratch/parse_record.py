#!/usr/bin/env python3
import json, sys
def parse(path):
    rows = []
    for l in open(path):
        if not l.startswith('| '):
            continue
        c = [x.strip() for x in l.rstrip('\n').strip().strip('|').split(' | ')]
        if len(c) != 6 or c[0] in ('key',) or set(c[0]) <= set('-: '):
            continue
        rows.append(dict(key=c[0], value=c[1], status=c[2], kind=c[3], unit=c[4], prov=c[5]))
    return rows
if __name__ == '__main__':
    rows = parse(sys.argv[1])
    if len(sys.argv) > 2:
        ref = json.load(open(sys.argv[2]))
        if rows != ref:
            print(len(rows), len(ref)); 
            for a, b in zip(rows, ref):
                if a != b: print(a); print(b); break
            raise SystemExit('parse mismatch')
        print('parse reproduces', len(rows))
    else:
        json.dump(rows, open(sys.argv[3] if len(sys.argv) > 3 else '/dev/stdout', 'w'), indent=1)
