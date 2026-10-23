#!/usr/bin/env python3
"""Compares every number the runs produced with the paper's.

Reads expected.tsv (beside this script: every key the paper cites, `key<TAB>value` as the paper prints it),
expected-differ.tsv (beside it: the keys whose value here is known to differ from the paper's, `key<TAB>the value
this artifact produces<TAB>where the difference is documented`) and results/rq1/keys.txt, results/rq2/keys.txt,
results/rq3/keys.txt (`key = value`, one per line; a key a run did not produce carries `skipped (<why>)`). Writes
results/compare.txt: one row per cited key,
  key <TAB> expected <TAB> produced <TAB> verdict
with the verdict
  equal       a count, rate, size or verdict, equal to the paper's as printed
  reported    a time or a factor, both numbers (and the host line): printed beside the paper's, with produced /
              expected; times depend on the machine and are never compared (a status word in place of a time,
              e.g. `crash`, must be equal)
  skipped     the run wrote `skipped (<why>)`, or that research question's run has not been made
  differ (documented: <where>)
              a key of expected-differ.tsv whose produced value is the one listed there
  differ      anything else (`differ (missing)`: the research question ran but did not write the key)
then the keys a run produced that the paper does not cite, and a last line
  "N keys equal, M reported, K skipped, D differ as documented, J differ".
usage: compare.py [RESULTS]   (default: ./results); exit status 0 (a difference is a result, not a failure)"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else 'results')
NUM = re.compile(r'^-?[\d,]+(\.\d+)?%?$')


def lane(k):
    """The research question whose run writes key k."""
    if k.startswith('rq4.') or k.startswith('rq1.tests.'):
        return 'rq3'
    if k.startswith('rq3.') and not re.match(r'^rq3\.inator\.[^.]+\.(types\.|loc$)', k):
        return 'rq2'
    return 'rq1'


def reported(k):
    return k.endswith('-s') or k.endswith('.factor') or k == 'setup.host'


def num(s):
    return float(s.replace(',', '').rstrip('%')) if NUM.match(s) else None


def main():
    expected = {}
    for line in open(os.path.join(HERE, 'expected.tsv'), encoding='utf-8'):
        if line.strip():
            k, v = line.rstrip('\n').split('\t', 1)
            expected[k] = v
    documented = {}
    for line in open(os.path.join(HERE, 'expected-differ.tsv'), encoding='utf-8'):
        if line.strip() and not line.startswith('#'):
            k, v, where = line.rstrip('\n').split('\t', 2)
            documented[k] = (v, where)
    produced, ran = {}, set()
    for q in ('rq1', 'rq2', 'rq3'):
        f = os.path.join(RESULTS, q, 'keys.txt')
        if not os.path.exists(f):
            continue
        ran.add(q)
        for line in open(f, encoding='utf-8'):
            if ' = ' in line:
                k, v = line.rstrip('\n').split(' = ', 1)
                produced[k.strip()] = v.strip()
    rows, n = [], {'equal': 0, 'reported': 0, 'skipped': 0, 'documented': 0, 'differ': 0}
    for k in sorted(expected):
        e = expected[k]
        if k not in produced:
            q = lane(k)
            p, verdict = '-', (f'skipped ({q} not run)' if q not in ran else 'differ (missing)')
        else:
            p = produced[k]
            if p.startswith('skipped'):
                verdict = 'skipped'
            elif k == 'setup.host':
                verdict = 'reported'
            elif reported(k) and num(p) is not None and num(e) is not None:
                a, b = num(p), num(e)
                verdict = f'reported ({a / b:.2f}x)' if b else 'reported'
            elif p == e:
                verdict = 'equal'
            elif k in documented and p == documented[k][0]:
                verdict = f'differ (documented: {documented[k][1]})'
            else:
                verdict = 'differ'
        n['documented' if verdict.startswith('differ (documented') else verdict.split(' ')[0]] += 1
        rows.append(f'{k}\t{e}\t{p}\t{verdict}')
    extra = sorted(k for k in produced if k not in expected)
    out = os.path.join(RESULTS, 'compare.txt')
    with open(out, 'w', encoding='utf-8') as f:
        f.write('# every key the paper cites: key, the paper\'s value, the value produced here, the verdict\n')
        f.write('key\texpected\tproduced\tverdict\n')
        f.write('\n'.join(rows) + '\n')
        if extra:
            f.write('\n# produced here, not cited by the paper\n')
            f.write('\n'.join(f'{k}\t\t{produced[k]}\t' for k in extra) + '\n')
        last = (f"{n['equal']} keys equal, {n['reported']} reported, {n['skipped']} skipped, "
                f"{n['documented']} differ as documented, {n['differ']} differ")
        f.write('\n' + last + '\n')
    print(last, '->', out)


if __name__ == '__main__':
    main()
