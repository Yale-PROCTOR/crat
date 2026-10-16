"""Table effect-inator (the eight's interface types) and the eight's C lines.

The population: the 311 interface positions (parameters, returns, struct fields of pointer C type, of functions and
structs the program defines) on which &inator's outputs and the C2Rust translation agree, shipped as bare identities
in data/inator-positions.tsv (program, kind, &inator's owner, index, the translation's owner and name). When &inator's
outputs are present the join is recomputed and must equal the shipped list.
  ours      the type our emitted tree gives the position (the safe twin `__jobcrat_safe_f` where the exposure split
            one off; type aliases resolved): ref / mut (`&`, `&mut`, the cursors) / box / raw.
  &inator   its type fragment for the position (rtypes.txt), the outermost `ghost` stripped; the first constructor
            inside it (and inside the Cell / RefCell / [] qualifiers) decides: `&'n mut` -> mut, `&'n` -> ref,
            Box -> box, Rc -> rc, unknown -> unknown, a referent stored by value -> byvalue.
  loc       cloc code lines over the program's .c / .h files (&inator's benchmark directory)."""
import glob, os, re, shutil, subprocess, tempfile
from collections import Counter

import common as C
import inator_positions as IP

FORMS = ['ref', 'mut', 'box', 'rc', 'byvalue', 'unknown']
OURS = ['ref', 'mut', 'box', 'raw']
DATA = os.path.join(C.RQ1, 'data', 'inator-positions.tsv')


def positions():
    rows = C.read_tsv(DATA)
    for r in rows:
        r['index'] = int(r['index'])
    return rows


def classify(t):
    t = t.strip()
    if t.startswith('ghost<') and t.endswith('>'):
        t = t[6:-1].strip()
    for _ in range(4):
        m = re.match(r'^(?:Cell|RefCell)<(.*)>$', t)
        if m:
            t = m.group(1).strip()
            continue
        m = re.match(r'^\[(.*)\]$', t)
        if m:
            t = m.group(1).strip()
            continue
        break
    if re.match(r"^&'\d+ mut ", t):
        return 'mut'
    if re.match(r"^&'\d+ ", t):
        return 'ref'
    if t.startswith('Box<'):
        return 'box'
    if t.startswith('Rc<'):
        return 'rc'
    if t == 'unknown' or t.startswith('unknown'):
        return 'unknown'
    if t.startswith('ghost<') or re.match(r'^(struct\(|i\d+|f\d+|bool|void)', t):
        return 'byvalue'
    raise SystemExit(f'rq1: unclassified &inator fragment: {t!r}')


def ours_bucket(t):
    t = re.sub(r'\s+', ' ', t.strip())
    u = re.sub(r'^Option<\s*', '', t)
    if u.startswith('Box<'):
        return 'box'
    if re.match(r"^&\s*('\w+\s+)?mut\b", u):
        return 'mut'
    if u.startswith('&'):
        return 'ref'
    if re.match(r'^\*(mut|const)\b', u):
        return 'raw'
    if re.match(r'^(\w+::)*SliceCursorMut\b', u) or re.match(r'^(\w+::)*\w*CursorMut\b', u):
        return 'mut'
    if re.match(r'^(\w+::)*\w*Cursor\b', u):
        return 'ref'
    return 'other:' + t[:60]


def ours_types(q, rows):
    tree = os.path.join(C.TREES, q)
    if not os.path.isdir(tree):
        return None
    text = ''
    for f in sorted(glob.glob(f'{tree}/**/*.rs', recursive=True)):
        if not f.endswith('build.rs'):
            text += open(f, encoding='utf-8').read() + '\n'
    tmp = tempfile.mkdtemp()
    try:
        os.makedirs(f'{tmp}/src')
        open(f'{tmp}/src/all.rs', 'w').write(text)
        crows = IP.c2rust_rows(tmp)
    finally:
        shutil.rmtree(tmp)
    aliases = {m.group(1): m.group(2).strip() for m in re.finditer(r'^\s*pub type (\w+) = (.*?);$', text, flags=re.M)}

    def resolve(t):
        t = t.strip()
        for _ in range(20):
            core = re.sub(r'^Option<\s*(.*)>$', r'\1', t)
            if t in aliases:
                t = aliases[t]
            elif core in aliases and core != t:
                t = 'Option<' + aliases[core] + '>'
            else:
                break
        return t
    em = {}
    for r in crows:
        owner = r['owner']
        twin = owner.startswith(C.TW)
        if twin:
            owner = owner[len(C.TW):]
        k = (r['kind'], owner, r['index'])
        if twin or k not in em:
            em[k] = r
    out = []
    for r in rows:
        e = em.get((r['kind'], r['c_owner'], r['index']))
        out.append(ours_bucket(resolve(e['rtype'])) if e else 'absent')
    return out


def inator_dir(q):
    d = os.path.join(C.INATOR, q)
    return d if os.path.exists(os.path.join(d, 'rtypes.txt')) and os.path.exists(os.path.join(d, 'stypes.txt')) else None


def inator_index(q):
    rows, _, _ = IP.inator_rows(inator_dir(q))
    return {(r['kind'], re.sub(r'^(struct|union)\.', '', r['owner']), r['index']): r for r in rows
            if not (r['kind'] == 'field' and re.sub(r'^(struct|union)\.', '', r['owner']).startswith('__'))}


def join_check(q, rows, I):
    """The join of &inator's positions with the input translation's, recomputed; must equal the shipped rows."""
    cr = IP.c2rust_rows(os.path.join(C.INPUT8, q))
    ANON = {'tisp': {'C2RustUnnamed_11': 'anon', 'C2RustUnnamed_15': 'anon.0', 'C2RustUnnamed_14': 'anon.1',
                     'C2RustUnnamed_13': 'anon.2', 'C2RustUnnamed_12': 'anon.3'}}.get(q, {})
    LIBC_ANON = {'tisp': {'C2RustUnnamed', 'sigval'} | {'C2RustUnnamed_%d' % n for n in range(0, 11)}}.get(q, set())
    cr = [r for r in cr if not (r['kind'] == 'field' and r['owner'] in LIBC_ANON and r['owner'] not in ANON)]
    for r in cr:
        if r['kind'] == 'field' and r['owner'] in ANON:
            r['owner'] = ANON[r['owner']]
    structs_c = {r['owner'] for r in cr if r['kind'] == 'field'}

    def ckey(r):
        o = 'main' if r['owner'] == 'main_0' else r['owner']
        if r['kind'] == 'field' and o.endswith('_0') and o[:-2] not in structs_c:
            o = o[:-2]
        return (r['kind'], o, r['index'])
    cr = [r for r in cr if not (r['kind'] == 'field' and re.match(r'^(_IO_|__)', r['owner']))]
    cp = {ckey(r): r for r in cr if r['owner'] != 'main'}
    cptr = {k for k, r in cp.items() if r['ck'] == 'pointer'}
    both = set(I) & cptr
    shipped = {(r['kind'], r['owner'], r['index']) for r in rows}
    return both == shipped, len(both), len(shipped)


def loc(q):
    d = os.path.join(C.INATOR, 'src', q)
    if not os.path.isdir(d):
        return None
    cloc = os.environ.get('CLOC', 'cloc')
    r = subprocess.run(cloc.split() + ['--quiet', '--csv', '--include-ext=c,h', d], capture_output=True, text=True,
                       check=True).stdout
    s = [l.split(',') for l in r.splitlines() if ',SUM,' in l or ',C,' in l or ',C/C++ Header,' in l]
    return next(int(x[4]) for x in s if x[1] == 'SUM') if any(x[1] == 'SUM' for x in s) else sum(int(x[4]) for x in s)


def measure():
    v, table = {}, []
    allrows = positions()
    tot = {'pos': 0, **{f'ours.{b}': 0 for b in OURS}, **{f'inator.{b}': 0 for b in FORMS}}
    ours_all = inator_all = True
    checks = []
    locs = {}
    for q in C.EIGHT:
        k = f'rq3.inator.{q}'
        rows = [r for r in allrows if r['program'] == q]
        row = {'program': q, 'positions': len(rows)}
        v[f'{k}.types.pos'] = str(len(rows))
        tot['pos'] += len(rows)
        ob = ours_types(q, rows)
        if ob is None:
            ours_all = False
            for b in OURS:
                v[f'{k}.types.ours.{b}'] = 'skipped (no emitted tree)'
        else:
            bad = [x for x in ob if x not in OURS]
            if bad:
                raise SystemExit(f'rq1: {q}: positions with no ref / mut / box / raw form in our tree: {Counter(bad)}')
            c = Counter(ob)
            for b in OURS:
                v[f'{k}.types.ours.{b}'] = str(c[b])
                tot[f'ours.{b}'] += c[b]
                row[f'ours.{b}'] = c[b]
        if inator_dir(q) is None:
            inator_all = False
            for b in FORMS:
                v[f'{k}.types.inator.{b}'] = ('skipped (--small: &inator runs five of the eight)' if C.SMALL
                                              else 'skipped (no third-party: &inator)')
        else:
            I = inator_index(q)
            ok, nb, ns = join_check(q, rows, I)
            checks.append(f'{q}\t{"equal" if ok else "DIFFERS"}\tjoin {nb}\tshipped {ns}')
            if not ok:
                raise SystemExit(f'rq1: {q}: the join of &inator\'s positions with the translation ({nb}) differs from '
                                 f'the shipped population ({ns})')
            c = Counter(classify(I[(r['kind'], r['owner'], r['index'])]['rtype']) for r in rows)
            for b in FORMS:
                v[f'{k}.types.inator.{b}'] = str(c[b])
                tot[f'inator.{b}'] += c[b]
                row[f'inator.{b}'] = c[b]
        n = loc(q)
        locs[q] = n
        v[f'{k}.loc'] = str(n) if n is not None else 'skipped (no third-party: &inator\'s C sources)'
        row['c_lines'] = n if n is not None else ''
        table.append(row)
    v['rq3.inator.total.types.pos'] = str(tot['pos'])
    for b in OURS:
        v[f'rq3.inator.total.types.ours.{b}'] = str(tot[f'ours.{b}']) if ours_all else 'skipped (an emitted tree absent)'
    for b in FORMS:
        v[f'rq3.inator.total.types.inator.{b}'] = (str(tot[f'inator.{b}']) if inator_all
                                                  else 'skipped (&inator\'s outputs not on all eight)')
    v['rq3.inator.total.loc'] = (str(sum(locs.values())) if all(x is not None for x in locs.values())
                                 else 'skipped (no third-party: &inator\'s C sources)')
    os.makedirs(C.OUT, exist_ok=True)
    open(os.path.join(C.OUT, 'inator-join-check.txt'), 'w').write('\n'.join(checks) + '\n' if checks else
                                                                 'not run: &inator\'s outputs absent\n')
    return v, table
