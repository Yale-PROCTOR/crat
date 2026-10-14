#!/usr/bin/env python3
"""classify.py: relay 083 items 1-2 over rows.tsv (deref-tool output for b54p emitted trees = side 'out', derived inputs = side 'in').
Class of a `&mut *X` (precedence top-down; X = operand of the deref, typed by deref-tool from declarations in scope):
  b  raw view      : b1 arg of core::ptr::from_mut (from_ref for `&*`) | b5 initializer of a let typed *mut/*const | b2 operand of a cast to a raw type (`&mut *p as *mut T`)
                     | b3 arg of a call whose formal is a raw pointer (implicit coercion &mut->*mut; incl. slice::from_raw_parts_mut)
                     | b4 the inner `&mut *p` of a doubled `&mut *&mut *p` / `&*&mut *p` whose outer one is b1/b2
  c  returned      : operand of `return` (or a fn/closure tail expression)
  d  owner lend    : d1 X typed Box<T>/Box<[T]> (non-optional owner) | d2 X typed &mut Box<..> from Option<Box<..>> (`&mut *o.as_mut().unwrap()`)
  a  raw bridge    : X typed *mut T / *const T (a reference formed from a raw pointer), any other context
  e  other         : the rest, sub-keyed by context|operand kind
"""
import collections, sys
rows = [l.rstrip('\n').split('\t') for l in open('rows.tsv')]
D = [r for r in rows if r[0] in ('DEREF', 'TYPE')]
def cls(r):
    if r[0] == 'TYPE': return 'e', 'e-type-position (a type `&mut *mut T` / `&mut *const T`, not an expression)'
    side, prog, fn, line, form, ctx, det, pk, anc, ok = r[1:11]
    callee = det.split('#')[0]
    if ctx == 'call-arg' and callee in ('from_mut', 'from_ref'): return 'b', 'b1-from_mut/from_ref'
    if ctx == 'cast' and det.startswith('*'): return 'b', 'b2-cast-to-raw'
    if ctx in ('call-arg', 'method-arg') and (pk.startswith('raw') or callee in ('from_raw_parts_mut', 'from_raw_parts')):
        return 'b', 'b3-coerced-to-raw-formal'
    a = anc.split(' < ')
    if ctx == 'other' and det == 'unary' and len(a) >= 3 and a[1] == 'other:ref-operand' and (a[2].startswith('call-arg:from_mut#') or a[2].startswith('call-arg:from_ref#') or a[2].startswith('cast:*')):
        return 'b', 'b4-inner-of-doubled'
    if ctx == 'let-init' and (': * mut' in det or ': * const' in det): return 'b', 'b5-coerced-to-raw-typed-let'
    if ctx in ('return', 'fn-tail', 'closure-tail'): return 'c', 'c-' + ctx + '|' + ok
    if ok in ('box', 'box-slice'): return 'd', 'd1-box-operand|' + ctx
    if ok.endswith('-to-box'): return 'd', 'd2-opt-box-operand|' + ctx
    if ok.startswith('raw'): return 'a', 'a-' + ctx + '|formal=' + (pk if ctx in ('call-arg', 'method-arg') else '-')
    return 'e', 'e-' + ctx + '|' + ok + ('|formal=' + pk if ctx in ('call-arg', 'method-arg') else '')
form = sys.argv[1] if len(sys.argv) > 1 else 'mut'
C = collections.Counter(); S = collections.Counter(); P = collections.defaultdict(collections.Counter); ex = collections.defaultdict(list)
progs = sorted({r[2] for r in rows})
for r in D:
    if r[5] != form: continue
    c, s = cls(r); C[(r[1], c)] += 1; S[(r[1], s)] += 1; P[(r[1], r[2])][c] += 1
    if r[1] == 'out' and len(ex[s]) < 2: ex[s].append(f'{r[2]} L{r[4]} fn {r[3]} :: ' + (r[14] if r[0] == 'TYPE' else f'&{"mut " if form=="mut" else ""}*{r[14]}'))
K = 'abcde'
print(f'== form {form}: class totals (out = emitted, in = derived input, diff = out - in)')
for k in K: print(k, C[('out', k)], C[('in', k)], C[('out', k)] - C[('in', k)])
print('TOTAL', sum(C[('out', k)] for k in K), sum(C[('in', k)] for k in K), sum(C[('out', k)] - C[('in', k)] for k in K))
print('\n== per program: out a b c d e | in a b c d e | diff a b c d e')
for p in progs:
    o = [P[('out', p)][k] for k in K]; i = [P[('in', p)][k] for k in K]
    print(p, *o, '|', *i, '|', *[x - y for x, y in zip(o, i)])
print('\n== subclasses (out, in, diff)')
for s in sorted({s for (_, s) in S}):
    print(f'{S[("out", s)]:5d} {S[("in", s)]:5d} {S[("out", s)] - S[("in", s)]:6d}  {s}')
# carried-text attribution: an emitted occurrence is 'carried' when the derived input has an occurrence in the same program,
# same enclosing fn key and the same operand text (multiset matching); otherwise 'new'. Input occurrences left unmatched = 'gone'.
inpool = collections.Counter((r[2], r[3], r[14]) for r in D if r[1] == 'in' and r[5] == form)
car = collections.Counter(); carp = collections.defaultdict(collections.Counter)
for r in D:
    if r[1] != 'out' or r[5] != form: continue
    k = (r[2], r[3], r[14]); c, s = cls(r)
    if inpool[k] > 0: inpool[k] -= 1; car[(c, 'carried')] += 1; carp[r[2]][(c, 'carried')] += 1
    else: car[(c, 'new')] += 1; carp[r[2]][(c, 'new')] += 1
print('\n== carried-text attribution (out occurrences): class carried new; input occurrences gone =', sum(inpool.values()))
for k in K: print(k, car[(k, 'carried')], car[(k, 'new')])
print('TOTAL', sum(car[(k, 'carried')] for k in K), sum(car[(k, 'new')] for k in K))
print('per program new a b c d e:')
for p in progs: print(' ', p, *[carp[p][(k, 'new')] for k in K], '| carried', *[carp[p][(k, 'carried')] for k in K])
print('\n== untyped operands (out, in):', sum(1 for r in D if r[5] == form and r[10] == 'untyped' and r[1] == 'out'),
      sum(1 for r in D if r[5] == form and r[10] == 'untyped' and r[1] == 'in'))
print('\n== examples (out)')
for s in sorted(ex):
    for e in ex[s]: print(s, '::', e)
