"""common.py: loaders shared by the r141 waiver-key scripts. load(B, t) reads <B>/*.<t>.tsv with analysis-fanout 060/061's
multi-line-cell rejoin (a physical line short of the header continues the previous record's last cell from field 14 on)."""
import glob, os
def load(B, t, strict=False):
    rows = []; bad = 0
    for f in sorted(glob.glob(f'{B}/*.{t}.tsv')):
        p = os.path.basename(f)[:-len(t) - 5]
        lines = [l for l in open(f, errors='replace').read().split('\n') if l]
        if not lines: continue
        hdr = lines[0].split('\t'); i = 1
        while i < len(lines):
            parts = lines[i].split('\t'); i += 1
            while len(parts) < len(hdr) and i < len(lines):
                cont = lines[i].split('\t'); i += 1
                parts = parts[:-1] + [parts[-1] + ' ' + cont[14].strip()] + cont[15:]
            if len(parts) != len(hdr):
                bad += 1
                if strict: raise SystemExit(f'BAD {t} {p} {len(parts)} vs {len(hdr)}')
                continue
            r = dict(zip(hdr, parts)); r['prog'] = p; rows.append(r)
    return rows, bad
PROGS = "avl binn brotli bst buffer bzip2 genann heman ht json.h libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser".split()
STAMP = 13  # stamp fields before `program` in the census receipt tables
def load_rejoin(B, t):
    """r146 (117's value fix, the r141 verifier's reader): rows of <B>/*.<t>.tsv as dicts; a record whose last cell spans
    physical lines continues on a line that repeats the stamp + program fields and whose next cell starts with whitespace;
    such lines are joined. A short row not followed by a continuation is padded with ''. Fails closed on an overlong row."""
    out = []
    for f in sorted(glob.glob(f'{B}/*.{t}.tsv')):
        p = os.path.basename(f)[:-len(t) - 5]
        lines = [l for l in open(f, errors='replace').read().split('\n') if l != '']
        if not lines: continue
        hdr = lines[0].split('\t'); i = 1
        while i < len(lines):
            parts = lines[i].split('\t'); i += 1
            while len(parts) < len(hdr) and i < len(lines):
                nxt = lines[i].split('\t')
                if len(nxt) > STAMP + 1 and nxt[STAMP] == p and nxt[STAMP + 1][:1].isspace():
                    parts = parts[:-1] + [parts[-1] + ' ' + nxt[STAMP + 1].strip()] + nxt[STAMP + 2:]; i += 1
                else: break
            if len(parts) > len(hdr): raise SystemExit(f'overlong row in {f}: {len(parts)} > {len(hdr)}')
            parts += [''] * (len(hdr) - len(parts))
            r = dict(zip(hdr, parts))
            if r.get('program') not in (p, ''): raise SystemExit(f'program mismatch in {f}: {r.get("program")} vs {p}')
            out.append(r)
    return out
