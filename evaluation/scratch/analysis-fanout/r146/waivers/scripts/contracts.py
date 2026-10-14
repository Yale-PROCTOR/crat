#!/usr/bin/env python3
"""contracts.py <rev>...: design.libc-contract-* from crates/.../decision/raw_boundary_contracts.rs at a commit (git show, read
only): TABLE's (symbol, position) rows and distinct symbols; + the stdio-stream family's symbols not in TABLE; release positions
= rows whose access is Consume / SourceSink (free, fclose, realloc)."""
import re, subprocess, sys
P = 'crates/pointer_replacer/src/bo_rewriter/decision/raw_boundary_contracts.rs'
for rev in sys.argv[1:]:
    s = subprocess.run(['git', '-C', 'crat', 'show', f'{rev}:{P}'], capture_output=True, text=True, check=True).stdout
    t = s[s.index('const TABLE: &[ContractRow] = &['):]; t = t[:t.index('\n];')]
    t = re.sub(r'//[^\n]*', '', t)
    rows = re.findall(r'\b(\w*row)\(\s*"([^"]+)"\s*,\s*(\d+)\s*,\s*([^,)]+)', t)
    rows += [('ContractRow', sym, i, own) for sym, i, own in re.findall(r'ContractRow\s*\{\s*symbol:\s*"([^"]+)",\s*position:\s*Position::Exact\((\d+)\),.*?ownership:\s*OwnershipContract::(\w+)', t, re.S)]
    pos = {(sym, int(i)) for _, sym, i, _ in rows}; syms = {sym for _, sym, _, _ in rows}
    acc = {}
    for kind, sym, i, a in rows: acc.setdefault(sym, set()).add((kind, a.strip()))
    st = s[s.index('fn is_stdio_stream_position'):]; st = st[:st.index('\n}')]
    stream = set(re.findall(r'\("(\w+)",\s*\d+\)', st))
    rel = sorted(sym for sym, a in acc.items() if any(('Consume' in x or 'Source' in x or 'Sink' in x or 'release' in k.lower()) for k, x in a))
    print(f'{rev}\tTABLE rows {len(rows)} positions {len(pos)} symbols {len(syms)}\tstream-family symbols {sorted(stream)} not in TABLE {sorted(stream - syms)}\tcallees {len(syms | stream)}\trelease {rel}\tno-retain {len(syms | stream) - len(rel)}')
    print('   row kinds', sorted({k for k, _, _, _ in rows}), 'Retains/Unknown uses in TABLE:', len(re.findall(r'Retention::(Retains|Unknown)', t)))
