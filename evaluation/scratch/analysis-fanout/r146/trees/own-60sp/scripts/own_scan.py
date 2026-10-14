#!/usr/bin/env python3
"""r131/own — owning-family census of batch 56's twenty emitted programs (analysis-fanout, relay 131, S37).

Read-only: the emitted trees, the c2rust inputs, the typed counter's positions.tsv (ours at batch 56; the input's
from r043), and batch 56's subject-outcome tables (the Box-key cross-check). Writes only under r131/own/.

Sources per program:
  TYPED  positions.tsv (pos_counter, compiler types, nightly-2025-06-23): a declaration (kind, owner, name, idx) is
         owning-typed when ANY of its layers has a form in BOX_FORMS (any depth, any ctx).
  TEXT   the emitted .rs text with comments and string/char literals blanked (line numbers kept): Box type mentions,
         Box expression sites (Box::<method>, .into_boxed_slice(), drop()/mem::drop() of a Box-typed binding),
         and the other owning std types (OTHER), compared with the input's text.
"""
import csv, os, re, sys, glob
from collections import Counter, defaultdict

csv.field_size_limit(10**9)
EMIT = 'scratch/main/batch60sp/emitted-trees'
INPUT = 'crat/benchmarks/rs-crown'
POS_OURS = 'scratch/analysis-fanout/r146/trees/t4/out-ours-60sp/ours'
POS_IN = 'scratch/analysis-fanout/r043/out/input'
CENSUS = 'scratch/main/batch60sp'
OUT = 'scratch/analysis-fanout/r146/trees/own-60sp'
PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
BOX_FORMS = {'box', 'box-slice', 'opt-box', 'opt-box-slice'}

# other owning std types (the extension covers the Box family only)
OTHER = {
    'Vec': r'\bVec\b', 'vec!': r'\bvec!', 'String': r'\bString\b', 'Rc': r'\bRc\b', 'Arc': r'\bArc\b',
    'RefCell': r'\bRefCell\b', 'Cell': r'\bCell\b', 'UnsafeCell': r'\bUnsafeCell\b', 'CString': r'\bCString\b',
    'OsString': r'\bOsString\b', 'PathBuf': r'\bPathBuf\b', 'HashMap': r'\bHashMap\b', 'BTreeMap': r'\bBTreeMap\b',
    'HashSet': r'\bHashSet\b', 'BTreeSet': r'\bBTreeSet\b', 'VecDeque': r'\bVecDeque\b',
    'BinaryHeap': r'\bBinaryHeap\b', 'LinkedList': r'\bLinkedList\b', 'Cow': r'\bCow\b',
    'format!': r'\bformat!', '.to_string()': r'\.to_string\s*\(', '.to_owned()': r'\.to_owned\s*\(',
    '.to_vec()': r'\.to_vec\s*\(', '.collect': r'\.collect\b', 'ManuallyDrop': r'\bManuallyDrop\b',
}


def blank(src):
    """Blank comments, string literals and char literals (keep newlines and length)."""
    out = list(src)
    i, n = 0, len(src)

    def fill(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '
    while i < n:
        c = src[i]
        if src.startswith('//', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            fill(i, j); i = j; continue
        if src.startswith('/*', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith('/*', j): depth += 1; j += 2
                elif src.startswith('*/', j): depth -= 1; j += 2
                else: j += 1
            fill(i, j); i = j; continue
        m = re.match(r'b?r(#*)"', src[i:i + 40])
        if m and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == '_')):
            close = '"' + m.group(1)
            j = src.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            fill(i, j); i = j; continue
        if c == '"' or (c == 'b' and src.startswith('b"', i) and (i == 0 or not (src[i-1].isalnum() or src[i-1] == '_'))):
            j = i + (2 if c == 'b' else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            fill(i, j + 1); i = j + 1; continue
        if c == "'" or (c == 'b' and src.startswith("b'", i) and (i == 0 or not (src[i-1].isalnum() or src[i-1] == '_'))):
            k = i + (2 if c == 'b' else 1)
            m = re.match(r"(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'", src[k:k + 14])
            if m:
                fill(i, k + m.end()); i = k + m.end(); continue
        i += 1
    return ''.join(out)


def rs_files(d):
    fs = []
    for root, _, files in os.walk(d):
        if '/target' in root:
            continue
        for f in files:
            if f.endswith('.rs') and f != 'build.rs':
                fs.append(os.path.join(root, f))
    return sorted(fs)


def lines_of(path):
    with open(path, encoding='utf-8', errors='replace') as fh:
        return blank(fh.read()).split('\n')


def positions(path):
    decls = defaultdict(list)
    with open(path) as fh:
        for r in csv.DictReader(fh, delimiter='\t'):
            if r['kind'] == 'kind':
                continue
            decls[(r['kind'], r['owner'], r['name'], r['idx'])].append(r)
    return decls


def own_decls(decls):
    return {k: v for k, v in decls.items() if any(r['form'] in BOX_FORMS for r in v)}


RX_TYPE = re.compile(r'\bBox\s*<')
RX_CALL = re.compile(r'\bBox\s*(?:::\s*<[^;{}]*?>)?\s*::\s*([A-Za-z_]\w*)')
RX_IBS = re.compile(r'\.\s*into_boxed_slice\s*\(')
RX_DROP = re.compile(r'(?:\bmem\s*::\s*|(?<![\w:]))drop\s*\(\s*([A-Za-z_]\w*)\s*\)')
RX_MACRO = re.compile(r'\bmacro_rules!')


def main():
    os.makedirs(OUT, exist_ok=True)
    rows, examples, othert = [], [], []
    detail = open(os.path.join(OUT, 'box-sites.tsv'), 'w')
    detail.write('program\tfile\tline\tclass\ttext\n')
    decl_out = open(os.path.join(OUT, 'owning-decls.tsv'), 'w')
    decl_out.write('program\tkind\towner\tname\tidx\tbinding\tsynthetic\tforms\tctxs\ttype\n')
    # census cross-check: realized-as-predicted with a Box-family emitted_form
    census = {}
    for p in PROGS:
        c = Counter()
        with open(f'{CENSUS}/{p}.raw-boundary-subject-outcomes.tsv') as fh:
            for r in csv.DictReader(fh, delimiter='\t'):
                if r['delivery'] == 'realized-as-predicted' and r['emitted_form'] in BOX_FORMS:
                    c[r['emitted_form']] += 1
        census[p] = c
    for p in PROGS:
        decls = positions(f'{POS_OURS}/{p}/positions.tsv')
        own = own_decls(decls)
        idecl = own_decls(positions(f'{POS_IN}/{p}/positions.tsv'))
        bykind = Counter(k[0] for k in own)
        nonlocal_ctx = Counter()
        for k, v in sorted(own.items()):
            forms = sorted({r['form'] for r in v if r['form'] in BOX_FORMS})
            ctxs = sorted({r['ctx'] for r in v if r['form'] in BOX_FORMS})
            depths = sorted({r['depth'] for r in v if r['form'] in BOX_FORMS})
            for cx in ctxs:
                nonlocal_ctx[cx] += 1
            if depths != ['0']:
                nonlocal_ctx['depth>0'] += 1
            r0 = v[0]
            decl_out.write('\t'.join([p, *k, r0['binding'], r0['synthetic'], ','.join(forms), ','.join(ctxs),
                                      r0['type']]) + '\n')
        boxnames = {k[2] for k in own}
        # text
        emitted_files = rs_files(f'{EMIT}/{p}')
        tcount = Counter()
        calls = Counter()
        first = None
        drops_nonbox = []
        macro_box = 0
        for f in emitted_files:
            L = lines_of(f)
            in_macro = 0
            for i, ln in enumerate(L, 1):
                rel = os.path.relpath(f, EMIT)
                for m in RX_TYPE.finditer(ln):
                    tcount['type-mention'] += 1
                    detail.write(f'{p}\t{rel}\t{i}\ttype\t{ln.strip()[:200]}\n')
                    if first is None:
                        first = (rel, i, ln.strip())
                for m in RX_CALL.finditer(ln):
                    calls['Box::' + m.group(1)] += 1
                    tcount['expr'] += 1
                    detail.write(f'{p}\t{rel}\t{i}\tBox::{m.group(1)}\t{ln.strip()[:200]}\n')
                for m in RX_IBS.finditer(ln):
                    calls['into_boxed_slice'] += 1
                    tcount['expr'] += 1
                    detail.write(f'{p}\t{rel}\t{i}\tinto_boxed_slice\t{ln.strip()[:200]}\n')
                for m in RX_DROP.finditer(ln):
                    if m.group(1) in boxnames:
                        calls['drop(box)'] += 1
                        tcount['expr'] += 1
                        detail.write(f'{p}\t{rel}\t{i}\tdrop(box)\t{ln.strip()[:200]}\n')
                    else:
                        drops_nonbox.append(f'{rel}:{i}')
                if RX_MACRO.search(ln):
                    in_macro += 1
        # Box mentions inside macro_rules bodies (macro-generated code)
        for f in emitted_files:
            src = blank(open(f, encoding='utf-8', errors='replace').read())
            for m in RX_MACRO.finditer(src):
                j = src.find('{', m.end())
                depth, k = 0, j
                while k < len(src):
                    if src[k] == '{': depth += 1
                    elif src[k] == '}':
                        depth -= 1
                        if depth == 0: break
                    k += 1
                body = src[j:k]
                macro_box += len(re.findall(r'\bBox\b', body))
        # other owning std types: emitted vs input
        in_files = rs_files(f'{INPUT}/{p}')
        def other_counts(files):
            c, where = Counter(), defaultdict(list)
            for f in files:
                for i, ln in enumerate(lines_of(f), 1):
                    for name, rx in OTHER.items():
                        for _ in re.finditer(rx, ln):
                            c[name] += 1
                            where[name].append((os.path.relpath(f, '/'), i, ln.strip()[:160]))
            return c, where
        oc, ow = other_counts(emitted_files)
        ic, _ = other_counts(in_files)
        new_other = {k: (oc[k], ic.get(k, 0)) for k in oc if oc[k] > ic.get(k, 0)}
        for k in sorted(set(oc) | set(ic)):
            othert.append((p, k, oc.get(k, 0), ic.get(k, 0)))
        for k in new_other:
            for w in ow[k]:
                examples.append(f'[other] {p}\t{k}\t/{w[0]}:{w[1]}\t{w[2]}')
        # example: first owning declaration line in text, else first type mention
        ex = '-'
        if first:
            ex = f'{EMIT}/{first[0]}:{first[1]}: {first[2][:160]}'
        owning = bool(own) or tcount['type-mention'] > 0 or tcount['expr'] > 0
        if bool(own) != (tcount['type-mention'] > 0 or tcount['expr'] > 0):
            decided = 'DISAGREE typed/text'
        elif own:
            decided = 'typed (positions.tsv) + text agree'
        else:
            decided = 'typed (0 rows) + text (0 Box tokens) agree'
        cen = census[p]
        dr = open(f'{CENSUS}/{p}.raw-boundary-box-drops.tsv').read().split('\n')
        st = dict(l.split('=', 1) for l in dr[:3] if '=' in l)
        rc = Counter(l.split('\t')[7] for l in dr[4:] if l.count('\t') >= 8) if st.get('status') == 'ok' else Counter()
        drop_receipt = f"status={st.get('status')};rows={st.get('rows', '-')}" + ''.join(f';{k}={v}' for k, v in sorted(rc.items()))
        closure_box = 0
        for f in emitted_files:
            for ln in lines_of(f):
                closure_box += len(re.findall(r'\|\s*(\w+)\s*\|\s*(?:::std::boxed::)?Box\s*::\s*into_raw\s*\(\s*\1\s*\)', ln))
        rows.append({
            'program': p, 'owning': 'yes' if owning else 'no',
            'owning_decls_typed': len(own),
            'decls_param': bykind['param'], 'decls_return': bykind['return'], 'decls_local': bykind['local'],
            'decls_field': bykind['field'], 'decls_static': bykind['static'],
            'decls_ctx_or_depth_nonzero': ';'.join(f'{k}={v}' for k, v in sorted(nonlocal_ctx.items()) if k != '-')
                                         or '-',
            'input_owning_decls_typed': len(idecl),
            'box_expr_sites_text': tcount['expr'],
            'expr_breakdown': ';'.join(f'{k}={v}' for k, v in sorted(calls.items())) or '-',
            'box_type_mentions_text': tcount['type-mention'],
            'box_in_macro_rules': macro_box,
            'drop_nonbox': ','.join(drops_nonbox) or '-',
            'closure_params_box_text_only': closure_box,
            'implicit_box_drop_receipts': drop_receipt,
            'census_delivered_box_family': sum(cen.values()),
            'census_split': ';'.join(f'{k}={v}' for k, v in sorted(cen.items())) or '-',
            'other_owning_new_vs_input': ';'.join(f'{k}={a}(input {b})' for k, (a, b) in sorted(new_other.items()))
                                         or '-',
            'decided_by': decided, 'example': ex,
        })
    detail.close(); decl_out.close()
    cols = list(rows[0])
    with open(os.path.join(OUT, 'per-program.tsv'), 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for r in rows:
            fh.write('\t'.join(str(r[c]) for c in cols) + '\n')
    with open(os.path.join(OUT, 'other-owning-std.tsv'), 'w') as fh:
        fh.write('program\ttoken\temitted\tinput\n')
        for t in othert:
            fh.write('\t'.join(map(str, t)) + '\n')
    with open(os.path.join(OUT, 'examples-other.txt'), 'w') as fh:
        fh.write('\n'.join(examples) + '\n')
    n = sum(r['owning'] == 'yes' for r in rows)
    print(f'formal.outputs.owning = {n}; formal.outputs.non-owning = {20 - n}')
    for r in rows:
        print(r['program'], r['owning'], r['owning_decls_typed'], r['box_expr_sites_text'], r['expr_breakdown'],
              r['box_type_mentions_text'], r['census_delivered_box_family'], r['census_split'],
              r['other_owning_new_vs_input'], r['decided_by'], r['drop_nonbox'], r['box_in_macro_rules'],
              r['input_owning_decls_typed'], r['decls_ctx_or_depth_nonzero'], sep=' | ')


if __name__ == '__main__':
    main()
