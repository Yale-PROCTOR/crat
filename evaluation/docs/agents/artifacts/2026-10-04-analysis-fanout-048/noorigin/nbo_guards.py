"""nbo_guards.py <entries.tsv> <out.tsv>: the slots NoOrigin forbids at L01^13 = the model's Comparisons guard records with
rule NoBorrowOrigin (emitted only for a no-borrow-origin slot outside the nullability set; mod.rs:489-505 at a5ffb2e05),
streamed by regex in 64 MiB chunks."""
import re, sys
C = 'worktrees/era5c-l01p13-night-solve/cache/era5b-model-cache-v1'
pat = re.compile(rb'"fields":\{"kind":"guard","rule":"NoBorrowOrigin","slot":"([^"]+)"\}')
w = open(sys.argv[2], 'w')
for l in open(sys.argv[1]):
    p, size, fn = l.rstrip('\n').split('\t'); seen = set()
    with open(f'{C}/{fn}', 'rb') as fh:
        tail = b''
        while True:
            ch = fh.read(1 << 26)
            if not ch: break
            buf = tail + ch; last = 0
            for m in pat.finditer(buf): seen.add(m.group(1).decode()); last = m.end()
            tail = buf[max(last, len(buf) - 1024):]
    for s in sorted(seen): w.write(f'{p}\t{s}\n')
    w.flush(); print(p, len(seen), file=sys.stderr, flush=True)
