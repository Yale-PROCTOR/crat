#!/usr/bin/env python3
"""analysis-fanout r108 g4-rq2: rq2.constructs.<construct>.<tool> (Appendix E, Table tab:rq2-constructs).

usage: constructs.py <census dir> [--out <dir>]

The table's caption: "Per-construct coverage: analyzed, declined, or unsupported. Where a system's stance is documented
in its own paper it is cited at the cell; where the disclosure cannot be produced symmetrically, the affected comparison
carries the asymmetry and no superiority claim."  Each cell is one word.

Definitions used here (stated so the cells can be audited):
  analyzed    - the system's analysis reasons about pointers that flow through the construct, and the construct's
                pointers can come out in a safe form;
  declined    - the system recognizes the construct and keeps its pointers raw by design (out of its scope), without
                failing on the input;
  unsupported - the system has no handling: its paper says it does not support the construct, generates no
                constraints for it, may crash on it, or the inputs had to be modified to remove it.

Third-party cells are frame-independent: read from the tools' own papers (paper-workspace/related/A_direct-comparison,
text extracted with pdftext/pdftxt.py in this directory; quotes in STANCES) and, for streams where a paper is silent,
from the outputs CROWN's artifact distributes (benchmarks/rs-crown-transformed; crown-artifact/
comparison) -- never a Laertes run of ours (R858-3).  Our cells carry the code cite at the frame and an evidence count
measured on <census dir>, so the script re-runs at a new frame.  Writes <out>/constructs.tsv (key, value, provenance)."""
import argparse, csv, glob, os, re, sys
from collections import Counter

csv.field_size_limit(10**9)
CROWN_OUT = os.environ.get('CROWN_OUT', 'crat/benchmarks/rs-crown-transformed')
CROWN_ARTIFACT = os.environ.get('CROWN_ARTIFACT', 'crown-artifact')
CROWN_P = 'CROWN paper (A03_CROWN_Ownership_Guided_C_to_Rust_Translation_2023.pdf)'
LAERTES_P = 'Laertes paper (A01_Laertes_Translating_C_to_Safer_Rust_OOPSLA2021.pdf)'
INATOR_P = '&inator paper (A04_and_inator_Correct_Precise_C_to_Rust_Interface_Translation_PLDI2026.pdf)'

STANCES = {
    ('fnptr', 'crown'): ('unsupported', f'{CROWN_P} sec. 7.2 "Function pointers. Crown does not generate any constraints for them."'),
    ('union', 'crown'): ('unsupported', f'{CROWN_P} sec. 7.2 "for unions we assume that they contain no pointer fields and consequently, we generate no constraints ... unions and variadic arguments may cause our tool to crash"; sec. 8 fn. 4: json-c, optipng, tinycc excluded "where Crown crashes because of the uses of unions and variadic arguments"'),
    ('variadic', 'crown'): ('unsupported', f'{CROWN_P} sec. 7.2 "we generate no constraints for variadic arguments ... may cause our tool to crash"; sec. 8 fn. 4 (three benchmarks excluded)'),
    ('array', 'crown'): ('declined', f'{CROWN_P} sec. 2.2 "The creation of meta-data such as array bounds is beyond the scope of ownership analysis. In this work, we keep array pointers as raw pointers"; sec. 7.3 "it does not generate the meta data required to synthesise Rust code"'),
    # ('stream', 'crown') is measured on the artifact (the paper is silent): see crown_stream()
    ('fnptr', 'laertes'): ('declined', f'{LAERTES_P} sec. 4.2 "a limitation of our method in that we do not rewrite function pointer types, so we cannot change the signature of the functions passed as function pointers" (pointers in such signatures stay raw: json-c, lil, TI)'),
    ('union', 'laertes'): ('declined', f'{LAERTES_P} sec. 2.2 lists union field reads as a separate unsafety category; sec. 2.3.3 replacing unions with tagged enums is a conjecture, not done; sec. 4.1 the method converts only Lifetime raw pointers (sec. 2.3.1)'),
    ('variadic', 'laertes'): ('declined', f'{LAERTES_P} sec. 2.3.1 a raw pointer "passed as an argument to, or returned from, an external function call" is the ExternPtr category, outside the method\'s Lifetime scope (sec. 4.1); the variadic callees in the corpus are libc (printf/scanf families)'),
    ('array', 'laertes'): ('declined', f'{LAERTES_P} sec. 2.3.1 "The raw pointer is used in pointer arithmetic. Because arrays in C decay to pointers, this reason captures most array accesses" = the PtrArith category, outside the Lifetime scope the method converts (sec. 4.1)'),
    ('fnptr', 'andinator'): ('unsupported', f'{INATOR_P} sec. 3.2 "&inator currently provides partial or no support for certain C program features: function pointers, polymorphic pointers, union types, variadic functions"; sec. 11.1 "it does not support function pointers, union types, variadic functions"; sec. 11.2 carrays/jccc/tisp modified "to not use ... unions, function pointers"'),
    ('union', 'andinator'): ('unsupported', f'{INATOR_P} sec. 3.2 and sec. 11.1 (union types not supported); sec. 11.2 inputs modified to remove unions'),
    ('variadic', 'andinator'): ('unsupported', f'{INATOR_P} sec. 3.2 and sec. 11.1 (variadic functions not supported)'),
    ('array', 'andinator'): ('analyzed', f'{INATOR_P} sec. 7.4 "Array Consistency": array qualifiers are inferred for a pointer used as a pointer to an array (constraints C-Array, App. B.4); stack ("ghost") arrays are conservatively disallowed (sec. 7.4)'),
}


def laertes_outputs():
    roots = []
    lc = os.path.join(CROWN_ARTIFACT, 'comparison/laertes-crown/after')
    roots += [os.path.join(lc, d) for d in sorted(os.listdir(lc))]
    for line in open(os.path.join(CROWN_ARTIFACT, 'comparison/laertes-path')):
        line = line.strip()
        if line:
            roots.append(os.path.join(CROWN_ARTIFACT, 'comparison/laertes-laertes/after', os.path.dirname(line)))
    return roots


FILE_RAW = re.compile(r'\*(?:mut|const) (?:libc::)?(?:FILE|_IO_FILE)\b')
FILE_SAFE = re.compile(r'(?:Option<&(?:mut )?|Box<|&(?:mut )?)(?:libc::)?(?:FILE|_IO_FILE)\b')


def file_forms(roots):
    raw = safe = 0
    for r in roots:
        for f in glob.glob(os.path.join(r, '**/*.rs'), recursive=True):
            t = open(f, encoding='utf-8', errors='replace').read()
            raw += len(FILE_RAW.findall(t))
            safe += len(FILE_SAFE.findall(t))
    return raw, safe


def tsv(census, kind):
    for f in sorted(glob.glob(os.path.join(census, f'*.raw-boundary-{kind}.tsv'))):
        yield from csv.DictReader(open(f), delimiter='\t')


def ours(census):
    # function pointers: functions in a function-pointer web whose body is converted, and their delivered subjects
    web = {}
    for r in tsv(census, 'exposure'):
        if r['fnptr_web'] == '1':
            web[(r['program'], r['function'])] = r
    conv = {k for k, r in web.items() if r['inner_metric'] == 'converted'}
    plans = Counter(r['surface_plan'] for k, r in web.items() if k in conv)
    deliv = Counter()
    forms = Counter()
    held_stream = 0
    for r in tsv(census, 'subject-outcomes'):
        if (r['program'], r['owner_fn']) in conv:
            deliv[r['delivery']] += 1
        if r['delivery'] == 'realized-as-predicted':
            forms[r['emitted_form']] += 1
    for r in tsv(census, 'subjects'):
        if any('io-domain' in (v or '') for v in r.values()):
            held_stream += 1
    fnptr_bridges = Counter()
    variadic = Counter()
    vprogs = set()
    for r in tsv(census, 'bridge-receipts'):
        if r['stage'] != 'terminal' or r['state'] != 'applied':
            continue
        if 'fnptr' in (r.get('bridge_kind') or ''):
            fnptr_bridges[r['bridge_kind']] += 1
        callee = (r.get('callee') or '').split('::')[-1]
        if re.fullmatch(r'(f|s|sn|v|vf|vs|vsn)?printf|(f|s|v|vf|vs)?scanf', callee):
            variadic[callee] += 1
            vprogs.add(r['program'])
    # program-defined C-variadic functions and union declarations in the emitted trees
    vdefs = unions = uptr = 0
    for f in glob.glob(os.path.join(census, 'emitted-trees', '*', '**', '*.rs'), recursive=True):
        t = open(f, encoding='utf-8', errors='replace').read()
        vdefs += len(re.findall(r'\bmut [A-Za-z_0-9]+: \.\.\.', t))
        for m in re.finditer(r'pub union \w+\s*\{(.*?)\n\s*\}', t, re.S):
            unions += 1
            uptr += len(re.findall(r'\*(?:mut|const) |&|Box<', m.group(1)))
    arrays = {k: forms[k] for k in ('slice', 'cursor', 'opt-slice', 'opt-box-slice', 'box-slice', 'owner-view') if forms[k]}
    code = 'code 4a47f16f7 (L01^14)'
    return {
        'fnptr': ('analyzed', f'{code}: a call through a function pointer is opaque to ownership (its arguments are lent, T-ICALL-OPQ, '
                  f'infer.rs) and the pair rule reads its targets from points-to; a function in a function-pointer web keeps a C-named raw '
                  f'wrapper that the pointer names and its body is converted in __crat_safe_<f> (bo_rewriter/decision/exposure.rs, '
                  f'ast_transform.rs; analysis-fanout 061). At {census}: {len(conv)} web functions with converted bodies '
                  f'({", ".join(f"{k} {v}" for k, v in plans.most_common())}), {deliv["realized-as-predicted"]} delivered subjects in them '
                  f'({deliv["degraded"]} degraded); applied fn-pointer bridges {dict(fnptr_bridges)}'),
        'union': ('declined', f'{code}: a union field gets no slot (borrow_ownership/resolve.rs:93 `!adt.is_struct() || adt.is_union()` -> None) '
                  f'and a union-reachable place is a pure use (ownership/ssa/consume.rs place_not_reachable_to_union), so its pointers stay raw; '
                  f'no failure. At {census}: {unions} union declarations in the emitted trees with {uptr} pointer or reference fields '
                  f'(the corpus\'s unions hold no pointers, so no count in RQ1/RQ2 depends on this cell)'),
        'variadic': ('analyzed', f'{code}: calls to the libc variadic families carry per-position contracts (bo_rewriter/decision/'
                     f'raw_boundary_contracts.rs printf_tail_first / scanf_tail_first, no-retention and access per tail position), so a safe '
                     f'subject reaches a variadic argument through a bridge; the analysis records variadic positions as observations '
                     f'(infer/boundary.rs:400). At {census}: {sum(variadic.values())} applied terminal bridges at printf/scanf-family calls '
                     f'({", ".join(f"{k} {v}" for k, v in variadic.most_common())}) in {len(vprogs)} programs; program-defined C-variadic '
                     f'functions: {vdefs} (such a definition would keep its raw signature: ast_transform.rs `inbound-wrapper-unplaceable: '
                     f'variadic function`)'),
        'array': ('analyzed', f'{code}: array and pointer-arithmetic subjects are decided as slices or bidirectional cursors and delivered; '
                  f'at {census} realized-as-predicted array forms: {arrays} (subject-outcomes emitted_form)'),
        'stream': ('declined', f'{code}: FILE-typed declarations are held by identity (held:io-domain; ruling addenda 176-177, premises X1), '
                   f'owned by a separate I/O pass; at {census}: {held_stream} subject rows carry io-domain in *.raw-boundary-subjects.tsv '
                   f'(the RQ5 key rq5.cause.held counts the in-scope ones)'),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('census')
    ap.add_argument('--out', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out'))
    a = ap.parse_args()
    if not os.path.isdir(os.path.join(a.census, 'emitted-trees')):
        sys.exit(f'no emitted-trees in {a.census}; nothing written')
    rows = {}
    for (c, t), (v, p) in STANCES.items():
        rows[f'rq2.constructs.{c}.{t}'] = (v, p)
    craw, csafe = file_forms([CROWN_OUT])
    rows['rq2.constructs.stream.crown'] = (
        'analyzed', f'{CROWN_P} is silent on streams (no rule for FILE); measured on CROWN\'s distributed outputs ({CROWN_OUT}): '
        f'FILE pointers are constrained like any pointer -- {csafe} FILE positions in a safe form (Option<&mut FILE>: libcsv '
        f'src/libcsv.rs csv_fwrite fp, tulipindicators smoke.rs get_array fp) beside {craw} raw')
    lraw, lsafe = file_forms(laertes_outputs())
    rows['rq2.constructs.stream.laertes'] = (
        'declined', f'{LAERTES_P} sec. 2.3.1: a pointer passed to an external function (fopen, fprintf, ...) is ExternPtr, outside the '
        f'Lifetime scope (sec. 4.1); the Laertes outputs CROWN\'s artifact distributes ({CROWN_ARTIFACT}/comparison): {lsafe} FILE '
        f'positions safe, {lraw} raw')
    for c, (v, p) in ours(a.census).items():
        rows[f'rq2.constructs.{c}.ours'] = (v, p)
    os.makedirs(a.out, exist_ok=True)
    with open(os.path.join(a.out, 'constructs.tsv'), 'w') as f:
        f.write('key\tvalue\tprovenance\n')
        for k in sorted(rows):
            v, p = rows[k]
            f.write(f'{k}\t{v}\t{p}\n')
    print(open(os.path.join(a.out, 'constructs.tsv')).read())
    print('NOT SEEDED: rq2.constructs.stream.andinator (the &inator paper is silent on FILE streams; no &inator output on this '
          'host -- the rq3-inator lane (host-b) probes it)', file=sys.stderr)


if __name__ == '__main__':
    main()
