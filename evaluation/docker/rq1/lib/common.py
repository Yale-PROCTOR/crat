"""Shared paths, program lists and readers for rq1/ (Tables effect-all, effect-crown, effect-inator).

Environment (set by the artifact's run.sh; defaults for a run from the unpacked source root):
  SRC          the translator's source root: benchmarks/{crown,inator}/ and deps_crate/target/debug/deps
  RESULTS      the results root (default $SRC/results)
  TREES        the emitted trees, one directory per program (default $RESULTS/trees)
  THIRD_PARTY  the comparison tools' outputs (default $RESULTS/third-party):
                 trees/crown/<p>/ with analysis_results/   CROWN's output tree per program
                 crown/evaluation.csv                      CROWN's own evaluation table (its evaluate.sh)
                 comparison/                               the CROWN artifact's comparison/ directory (Laertes trees)
                 inator/<q>/{stypes,rtypes}.txt            &inator's outputs on the eight
                 inator/src/<q>/                           the eight's C sources (C lines)
  SMALL        1: our trees for lil and brotli are not produced (--small)
  RQ1_BIN      the two counters' binaries (default: rq1/target/release)"""
import csv, json, os, re

csv.field_size_limit(10 ** 9)
HERE = os.path.dirname(os.path.abspath(__file__))
RQ1 = os.path.dirname(HERE)
SRC = os.path.abspath(os.environ.get('SRC', os.getcwd()))
RESULTS = os.path.abspath(os.environ.get('RESULTS', os.path.join(SRC, 'results')))
TREES = os.path.abspath(os.environ.get('TREES', os.path.join(RESULTS, 'trees')))
THIRD_PARTY = os.path.abspath(os.environ.get('THIRD_PARTY', os.path.join(RESULTS, 'third-party')))
SMALL = os.environ.get('SMALL', '0') == '1'
OUT = os.path.join(RESULTS, 'rq1')
WORK = os.path.join(OUT, 'counter')
BIN = os.path.abspath(os.environ.get('RQ1_BIN', os.path.join(RQ1, 'target', 'release')))
TYPED = os.path.join(BIN, 'typed_counter')
DECL = os.path.join(BIN, 'decl_counter')
TOOLCHAIN = 'nightly-2025-06-23'

PROGS = ['avl', 'binn', 'brotli', 'bst', 'buffer', 'bzip2', 'genann', 'heman', 'ht', 'json.h', 'libcsv', 'libtree',
         'libzahl', 'lil', 'lodepng', 'quadtree', 'rgba', 'robotfindskitten', 'tulipindicators', 'urlparser']
LARGE = ('lil', 'brotli')          # left out of our side under --small
EIGHT = ['ulidgen', 'leftpad', 'amp', 'nandc', 'rbtree', 'carrays', 'jccc', 'tisp']
TW = '__jobcrat_safe_'             # the exposure wrapper's twin: the safe body of `f` is `__jobcrat_safe_f`

INPUT = os.path.join(SRC, 'benchmarks', 'crown')
INPUT8 = os.path.join(SRC, 'benchmarks', 'inator')
CROWN = os.path.join(THIRD_PARTY, 'trees', 'crown')
COMPARISON = os.path.join(THIRD_PARTY, 'comparison')
EVALUATION = os.path.join(THIRD_PARTY, 'crown', 'evaluation.csv')
INATOR = os.path.join(THIRD_PARTY, 'inator')


def K(p):
    return p.replace('.', '')


def pct(a, b):
    return f'{100.0 * a / b:.1f}%'


def ours_programs():
    return [p for p in PROGS if not (SMALL and p in LARGE)]


def root_of(d):
    for f in ('lib.rs', 'c2rust-lib.rs', 'src/lib.rs', 'rust/src/lib.rs', 'test.rs'):
        if os.path.exists(os.path.join(d, f)):
            return os.path.join(d, f)
    return None


def unsrc(s):
    return s[5:] if s.startswith('src::') else s


def read_tsv(path):
    with open(path, encoding='utf-8') as fh:
        return list(csv.DictReader(fh, delimiter='\t'))


def status(d):
    f = os.path.join(d, 'status.txt')
    return open(f).read().split('\t')[0].strip() if os.path.exists(f) else 'no-run'


def tab(d, name):
    """A counter table, or None when the counter did not complete on that tree."""
    if status(d) != 'ok':
        return None
    return read_tsv(os.path.join(d, name))


def counted(side, p):
    return os.path.join(WORK, side, p)


# ------------------------------------------------------------------ CROWN's universe (fn_data, depth 0, Mut and Ptr)
_U = {}


def have_crown(p):
    return os.path.isfile(os.path.join(CROWN, p, 'analysis_results', 'mutability.json'))


def universe(p):
    if p not in _U:
        b = os.path.join(CROWN, p, 'analysis_results')
        u = set()
        if have_crown(p):
            mu = json.load(open(f'{b}/mutability.json'))['fn_data']
            fa = json.load(open(f'{b}/fatness.json'))['fn_data']
            for fn, vs in mu.items():
                for v, lab in vs.items():
                    if lab[:1] == ['Mut'] and fa.get(fn, {}).get(v, [])[:1] == ['Ptr']:
                        u.add(f'{fn}::{v}')
        _U[p] = u
    return _U[p]


# ------------------------------------------------------------------ the Laertes trees CROWN's artifact distributes
def laertes_root(p):
    """(the Laertes output directory for p, whether its layout is flat), or (None, False)."""
    lc = os.path.join(COMPARISON, 'laertes-crown', 'after', p)
    if os.path.isdir(lc):
        return lc, False
    lp = os.path.join(COMPARISON, 'laertes-path')
    if os.path.exists(lp):
        for line in open(lp):
            line = line.strip()
            if line.split('/')[0] == p:
                return os.path.join(COMPARISON, 'laertes-laertes', 'after', os.path.dirname(line)), True
    return None, False


# ------------------------------------------------------------------ CROWN's own evaluation table (decl / usage cells)
def evaluation():
    """{program: (declarations before, after, usages before, after)} from CROWN's evaluation.csv, or {}."""
    if not os.path.exists(EVALUATION):
        return {}
    ev = {}
    for r in csv.reader(open(EVALUATION)):
        if r and r[0] and not r[0].startswith('Benchmark'):
            ev[r[0]] = (int(r[1]), int(r[2]), int(r[4]), int(r[5]))
    return ev
