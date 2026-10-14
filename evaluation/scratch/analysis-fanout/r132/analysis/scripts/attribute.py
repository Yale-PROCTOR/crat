#!/usr/bin/env python3
"""r132 analysis (relay 132): attribute the raw-to-safe conversion sites of each tool's emitted tree to the TOOL.

A site of an AFTER tree is TOOL-MADE when it has no counterpart in that tool's own BEFORE tree:
  crown, ours58, ours56  : before = the input (benchmarks/rs-crown)      -> r132/out/input/<p>/sites.tsv
  laertes                : before = the artifact's Laertes BEFORE tree   -> analysis/out-before/laertes_before/<p>/sites.tsv
Only non-excluded kind a / b rows are attributed (the relay's count); x / h rows are listed in notes only.

Matching key (multiplicity, no line numbers):
  (fn*, kind, prod_family, dest, callee*)
  fn*      def_path_str of the body, the last segment's `__crat_safe_` prefix removed (crat moves a C-named function's
           body into its safe twin `__crat_safe_f` and keeps `f` as the exposure wrapper)
  kind     a:ref | a:mut-ref | b:<call>
  prod_family  the produced value's outer form: [opt-](ref|mut-ref|slice|slice-mut|box|box-slice|other)
  dest     call-arg | decl | assign | return | field-store | other
  callee*  call-arg only: dest_detail, `__crat_safe_` removed, generic args `::<..>` removed, last two segments
matched = min(after, before) per key; tool-made = after - matched; disappeared = before - matched.
A tool-made site is then flagged `from_idiom` when the before tree holds an unmatched EXCLUDED row with the same
(fn*, kind, callee*-or-dest) (the c2rust address idiom whose consumer the tool made safe, e.g. a formal turned to &mut).
"""
import csv, os, re, sys
from collections import Counter, defaultdict

csv.field_size_limit(10**9)
R = 'scratch/analysis-fanout/r132'
A = f'{R}/analysis'
OUT = f'{R}/out'
BEFORE_L = f'{A}/out-before/laertes_before'
sys.path.insert(0, 'docs/agents/tools/rq2')
sys.dont_write_bytecode = True
import pos_census as P  # noqa: E402
PROGRAMS = P.PROGRAMS
SIDES = {'crown': f'{OUT}/input', 'laertes': BEFORE_L, 'ours58': f'{OUT}/input', 'ours56': f'{OUT}/input'}


def norm_fn(f):
    head, _, last = f.rpartition('::')
    if last.startswith('__crat_safe_'):
        last = last[len('__crat_safe_'):]
    return f'{head}::{last}' if head else last


def norm_callee(c):
    """generic args removed, `__crat_safe_` removed, the LAST TWO path segments (`Type::method` / `module::fn`): crat's
    pre-passes merge c2rust's duplicated struct definitions across modules (brotli's BrotliDecoderStateStruct is
    `src::dec::state::..` in the input and `src::dec::decode::..` in ours), which changes a method's full path"""
    c = re.sub(r'::<[^>]*(<[^>]*>[^>]*)*>', '', c)
    return '::'.join(norm_fn(c).split('::')[-2:])


def prod_family(t):
    t = re.sub(r"&'\w+\s+", '&', t.strip())       # a formal's type may carry a named lifetime (`&'a1 mut T`)
    opt = ''
    m = re.match(r'(std|core)::option::Option<(.*)>$', t)
    if m:
        opt, t = 'opt-', m.group(2).strip()
    if t.startswith('&mut ['):
        f = 'slice-mut'
    elif t.startswith('&['):
        f = 'slice'
    elif t.startswith('&mut '):
        f = 'mut-ref'
    elif t.startswith('&'):
        f = 'ref'
    elif re.match(r'(std::boxed::|alloc::boxed::)?Box<\[', t):
        f = 'box-slice'
    elif re.match(r'(std::boxed::|alloc::boxed::)?Box<', t):
        f = 'box'
    else:
        f = 'other'
    return opt + f


def call_class(k):
    """b's call as the relay names it."""
    if k in ('b:ptr-as_ref', 'b:ptr-as_ref_unchecked'):
        return 'as_ref'
    if k in ('b:ptr-as_mut', 'b:ptr-as_mut_unchecked'):
        return 'as_mut'
    if k.startswith('b:box-'):
        return 'Box::from_raw'
    if k.startswith('b:slice-'):
        return 'from_raw_parts' + ('_mut' if k.endswith('_mut') else '')
    if k.startswith('b:nonnull-'):
        return 'NonNull'
    if k.startswith('b:'):
        return k[2:]
    return k


def dest_class(g):
    d = g['dest']
    if d == 'call-arg':
        fs = g['formal_safe']
        return 'call-arg.' + (fs if fs in ('safe', 'raw', 'generic') else 'other')
    return d


def load(f):
    if not os.path.exists(f):
        return None
    return list(csv.DictReader(open(f), delimiter='\t'))


def status(d):
    s = os.path.join(d, 'status.txt')
    ss = os.path.join(d, 'sites-status.txt')
    st = open(s).read().split('\t')[0].strip() if os.path.exists(s) else 'no-run'
    if st != 'ok':
        return st
    return 'ok' if os.path.exists(ss) and open(ss).read().startswith('ok') else 'sites-not-ok'


def key(g):
    callee = norm_callee(g['dest_detail']) if g['dest'] == 'call-arg' else '-'
    return (norm_fn(g['fn']), g['kind'], prod_family(g['prod_ty']), g['dest'], callee)


def idiom_key(g):
    callee = norm_callee(g['dest_detail']) if g['dest'] == 'call-arg' else g['dest']
    return (norm_fn(g['fn']), g['kind'].split(':')[0] + ':' + g['kind'].split(':')[1].replace('mut-', ''), callee)


def is_ab(g):
    return g['kind'][:2] in ('a:', 'b:')


def attribute(after, before):
    """-> (tool-made rows, matched count, disappeared rows, from_idiom flags per tool-made row)"""
    a_ab = [g for g in after if is_ab(g) and g['excluded'] == 'no']
    b_ab = [g for g in before if is_ab(g) and g['excluded'] == 'no']
    bk = defaultdict(list)
    for g in b_ab:
        bk[key(g)].append(g)
    ak = defaultdict(list)
    for g in a_ab:
        ak[key(g)].append(g)
    made, gone, matched = [], [], 0
    for k in set(ak) | set(bk):
        la, lb = ak.get(k, []), bk.get(k, [])
        m = min(len(la), len(lb))
        matched += m
        # which particular rows are "extra" is arbitrary inside a key; sort by line so the earliest pair up
        la = sorted(la, key=lambda g: (g['file'], int(g['line']), int(g['col'])))
        lb = sorted(lb, key=lambda g: (g['file'], int(g['line']), int(g['col'])))
        made += la[m:]
        gone += lb[m:]
    # from_idiom: the before's excluded rows (c2rust's address idiom) with the same fn / kind / consumer
    pool = Counter(idiom_key(g) for g in before if is_ab(g) and g['excluded'] == 'yes')
    # rows of the before that were excluded and are no longer present as excluded in the after
    pool_after = Counter(idiom_key(g) for g in after if is_ab(g) and g['excluded'] == 'yes')
    free = Counter({k: max(0, pool[k] - pool_after.get(k, 0)) for k in pool})
    flags = []
    for g in made:
        k = idiom_key(g)
        if free.get(k, 0) > 0:
            free[k] -= 1
            flags.append('yes')
        else:
            flags.append('no')
    return made, matched, gone, flags


def tree_root(side, p, dest):
    """the directory the site's `file` is relative to (the root file's directory of the run)."""
    cmd = open(os.path.join(dest, 'cmd.txt')).read().split('\n')[0].split()
    r = cmd[cmd.index('--root') + 1]
    return os.path.dirname(r)


_src = {}


def src_line(root, f, line, n=1):
    path = os.path.join(root, f)
    if path not in _src:
        try:
            _src[path] = open(path, errors='replace').read().split('\n')
        except OSError:
            _src[path] = []
    ls = _src[path]
    i = int(line) - 1
    return ' '.join(x.strip() for x in ls[i:i + n]) if 0 <= i < len(ls) else ''


_statics = {}


def statics(root):
    """names of the tree's statics (`static [mut] NAME:`, extern-block statics included)"""
    if root not in _statics:
        names = set()
        for dp, _, fs in os.walk(root):
            for f in fs:
                if f.endswith('.rs'):
                    txt = open(os.path.join(dp, f), errors='replace').read()
                    names |= set(re.findall(r'\bstatic\s+(?:mut\s+)?([A-Za-z_]\w*)\s*:', txt))
        _statics[root] = names
    return _statics[root]


def expr_at(root, f, line, col, limit=1500):
    """the source text from the site's span start to the end of its expression: balanced brackets, stopping at a
    `,` / `;` / unmatched closer at depth 0 (whitespace collapsed)"""
    path = os.path.join(root, f)
    if path not in _src:
        try:
            _src[path] = open(path, errors='replace').read().split('\n')
        except OSError:
            _src[path] = []
    ls = _src[path]
    i = int(line) - 1
    if not (0 <= i < len(ls)):
        return ''
    txt = ls[i][int(col) - 1:] + '\n' + '\n'.join(ls[i + 1:i + 40])
    out, depth = [], 0
    for ch in txt[:limit]:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            if depth == 0:
                break
            depth -= 1
        elif ch in ',;' and depth == 0:
            break
        out.append(ch)
    return re.sub(r'\s+', ' ', ''.join(out)).strip()


def shape(g, e):
    """kind a: how the reference is written; b: the call"""
    k = g['kind']
    if not k.startswith('a:'):
        return call_class(k)
    t = re.sub(r'^Some\(\s*', '', e)
    if re.match(r'ref\s', t):
        return 'a:ref-binding'                       # `let ref mut freshN = <place through raw>`
    m = re.match(r'&\s*(mut\s+)?(.)', t)
    if m:
        return 'a:explicit-pointee' if m.group(2) == '*' else 'a:explicit-subplace'   # `&mut *p..` / `&mut (*p).f`
    if g['dest'] == 'call-arg':
        return 'a:autoref-receiver:' + norm_callee(g['dest_detail']).rsplit('::', 1)[-1]
    return 'a:implicit'


def static_base(root, e):
    m = re.match(r'(?:Some\()?\s*&\s*(?:mut\s+)?\(?\s*([A-Za-z_][\w:]*)', e)
    return bool(m) and m.group(1).rsplit('::', 1)[-1] in statics(root)


COLS = ['side', 'program', 'file', 'line', 'col', 'fn', 'kind', 'call', 'call_class', 'prod_ty', 'prod_family', 'dest',
        'dest_class', 'dest_detail', 'formal_ty', 'formal_safe', 'via', 'null_dom', 'null_test', 'src_ty',
        'post_raw_derefs', 'in_wrapper', 'macro', 'boundary', 'helper_module', 'from_idiom', 'shape', 'static_base',
        'roundtrip', 'counted', 'expr', 'text']


def main():
    os.makedirs(A, exist_ok=True)
    per = []
    gone_all = []
    for side, bdir in SIDES.items():
        rows_out = []
        for p in PROGRAMS:
            adest = os.path.join(OUT, side, p)
            bdest = os.path.join(bdir, p)
            sa, sb = status(adest), status(bdest)
            if sa != 'ok' or sb != 'ok':
                per.append({'side': side, 'program': p, 'status': f'after={sa};before={sb}'})
                continue
            after, before = load(f'{adest}/sites.tsv'), load(f'{bdest}/sites.tsv')
            made, matched, gone, flags = attribute(after, before)
            root = tree_root(side, p, adest)
            broot = tree_root(side, p, bdest)
            c = Counter()
            c['after_ab'] = sum(1 for g in after if is_ab(g) and g['excluded'] == 'no')
            c['before_ab'] = sum(1 for g in before if is_ab(g) and g['excluded'] == 'no')
            c['matched'] = matched
            c['tool_made'] = len(made)
            c['disappeared'] = len(gone)
            for g, fl in zip(made, flags):
                k = g['kind']
                cc = call_class(k) if k.startswith('b:') else k
                dc = dest_class(g)
                bnd = 'yes' if g['dest'] == 'call-arg' and g['dest_detail'].rsplit('::', 1)[-1].startswith(
                    '__crat_safe_') else 'no'
                helper = 'yes' if g['fn'].startswith('slice_cursor::') or '::slice_cursor::' in g['fn'] else 'no'
                e = expr_at(root, g['file'], g['line'], g['col'])
                sb = 'yes' if g['kind'].startswith('a:') and static_base(root, e) else 'no'
                rt = 'yes' if g['dest'] == 'call-arg' and re.match(r'(std|core)::ptr::(from_mut|from_ref)\b',
                                                                   g['dest_detail']) else 'no'
                counted = 'yes' if sb == 'no' and rt == 'no' else 'no'
                sh = shape(g, e)
                c['static_base'] += sb == 'yes'
                c['roundtrip'] += rt == 'yes'
                c['tool_made_counted'] += counted == 'yes'
                c[f'sh.{sh.split(":")[0]}:{sh.split(":")[1]}' if sh.startswith('a:') else f'sh.b'] += 1
                c[f'k.{cc}'] += 1
                c[f'd.{dc}'] += 1
                c['from_idiom'] += fl == 'yes'
                c['boundary'] += bnd == 'yes'
                c['helper'] += helper == 'yes'
                if cc in ('Box::from_raw', 'as_ref', 'as_mut'):
                    nd = g['null_dom']
                    nd = 'yes' if nd in ('yes', 'yes-base') else 'yes-place' if nd in ('yes-place', 'yes-base-place') else 'no'
                    c[f'nd.{cc}.{nd}'] += 1
                rows_out.append(dict(g, side=side, program=p, call_class=cc, prod_family=prod_family(g['prod_ty']),
                                     dest_class=dc, boundary=bnd, helper_module=helper, from_idiom=fl,
                                     shape=sh, static_base=sb, roundtrip=rt, counted=counted, expr=e[:600],
                                     text=src_line(root, g['file'], g['line'], 2)[:400]))
            for g in gone:
                gone_all.append(dict(g, side=side, program=p, call_class='', prod_family=prod_family(g['prod_ty']),
                                     dest_class=dest_class(g), boundary='', helper_module='', from_idiom='',
                                     text=src_line(broot, g['file'], g['line'], 1)[:300]))
            per.append(dict({'side': side, 'program': p, 'status': 'ok'}, **c))
        with open(f'{A}/toolmade-{side}.tsv', 'w') as f:
            w = csv.DictWriter(f, COLS, delimiter='\t', extrasaction='ignore', lineterminator='\n')
            w.writeheader()
            for r in rows_out:
                w.writerow(r)
    with open(f'{A}/disappeared.tsv', 'w') as f:
        w = csv.DictWriter(f, COLS, delimiter='\t', extrasaction='ignore', lineterminator='\n')
        w.writeheader()
        for r in gone_all:
            w.writerow(r)
    cols = ['side', 'program', 'status', 'before_ab', 'after_ab', 'matched', 'tool_made', 'disappeared',
            'k.a:ref', 'k.a:mut-ref', 'k.as_ref', 'k.as_mut', 'k.Box::from_raw', 'k.from_raw_parts',
            'k.from_raw_parts_mut', 'k.NonNull',
            'd.call-arg.safe', 'd.call-arg.raw', 'd.call-arg.generic', 'd.call-arg.other', 'd.decl', 'd.assign',
            'd.return', 'd.field-store', 'd.other',
            'nd.Box::from_raw.yes', 'nd.Box::from_raw.yes-place', 'nd.Box::from_raw.no',
            'nd.as_ref.yes', 'nd.as_ref.yes-place', 'nd.as_ref.no', 'nd.as_mut.yes', 'nd.as_mut.yes-place', 'nd.as_mut.no',
            'boundary', 'helper', 'from_idiom', 'static_base', 'roundtrip', 'tool_made_counted',
            'sh.a:ref-binding', 'sh.a:explicit-pointee', 'sh.a:explicit-subplace', 'sh.a:autoref-receiver',
            'sh.a:implicit', 'sh.b']
    # every key that occurs must be in cols (no silent drop)
    seen = set(k for r in per for k in r)
    extra = sorted(seen - set(cols))
    assert not extra, extra
    tots = defaultdict(Counter)
    for r in per:
        if r['status'] == 'ok':
            for k in cols[3:]:
                tots[r['side']][k] += r.get(k, 0)
            tots[r['side']]['ok'] += 1
    with open(f'{A}/per-tool-program.tsv', 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for side in SIDES:
            for r in per:
                if r['side'] == side:
                    f.write('\t'.join(str(r.get(k, 0 if r['status'] == 'ok' else '-')) for k in cols) + '\n')
            t = tots[side]
            f.write('\t'.join([side, 'TOTAL', f'{t["ok"]} ok'] + [str(t[k]) for k in cols[3:]]) + '\n')
    for side in SIDES:
        t = tots[side]
        print(side, ' '.join(f'{k}={t[k]}' for k in cols[3:] if t[k]))


if __name__ == '__main__':
    main()
