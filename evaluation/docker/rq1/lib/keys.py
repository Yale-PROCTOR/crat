#!/usr/bin/env python3
"""Writes rq1's keys and tables from the counters' outputs (count.py must have run):
  results/rq1/keys.txt                           `key = value`, one per key; `skipped (<why>)` where not produced
  results/tables/effect-{all,crown,inator}.csv   the three tables, per program and the total
  results/tables/effect-{all,crown,inator}.tex   the produced keys as the paper's numbers.tex rows
usage: keys.py            (environment: common.py)"""
import csv, ctypes, ctypes.util, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C  # noqa: E402
import inator_types  # noqa: E402
import measure  # noqa: E402
import sloc  # noqa: E402

TABLES = os.path.join(C.RESULTS, 'tables')
NUMBER_RE = re.compile(r'^(-?)(\d+)(\.\d+)?(%?)$')


def print_form(value):
    """A plain number prints with thousands separators in its integer part; any other value as recorded."""
    m = NUMBER_RE.match(value.strip())
    if not m:
        return value
    sign, whole, frac, pc = m.groups()
    return f'{sign}{int(whole):,}{frac or ""}{pc}'


def tex_escape(s):
    return (s.replace('\\', r'\textbackslash{}').replace('%', r'\%').replace('&', r'\&').replace('#', r'\#')
            .replace('_', r'\_').replace('^', r'\^{}').replace('~', r'\textasciitilde{}').replace('{', r'\{')
            .replace('}', r'\}'))


def setup_keys():
    v = {'setup.programs': str(len([p for p in C.PROGS if os.path.isdir(os.path.join(C.INPUT, p))]))}
    try:
        o = subprocess.run(['rustc', f'+{C.TOOLCHAIN}', '-V'], capture_output=True, text=True)
        v['setup.rustc'] = o.stdout.split()[1] if o.returncode == 0 else 'skipped (no rustc)'
    except OSError:
        v['setup.rustc'] = 'skipped (no rustc)'
    ver = None
    try:
        import z3  # noqa: F401
        ver = z3.get_version_string()
    except Exception:
        cands = [os.path.join(d, n) for d in
                 (os.environ.get('Z3_LIBRARY_PATH_OVERRIDE', ''), *os.environ.get('LD_LIBRARY_PATH', '').split(':')) if d
                 for n in ('libz3.so', 'libz3.so.4.15')]
        cands += [f for f in (ctypes.util.find_library('z3'),) if f]
        for f in cands:
            try:
                lib = ctypes.CDLL(f)
                a, b, c, d = (ctypes.c_uint() for _ in range(4))
                lib.Z3_get_version(ctypes.byref(a), ctypes.byref(b), ctypes.byref(c), ctypes.byref(d))
                ver = f'{a.value}.{b.value}.{c.value}'
                break
            except (OSError, AttributeError):
                continue
    v['setup.solver'] = f'Z3 {".".join(ver.split(".")[:3])}' if ver else 'skipped (no z3 library found)'
    model, threads, cores = '', os.cpu_count(), set()
    phys = core = None
    for l in open('/proc/cpuinfo'):
        if l.startswith('model name') and not model:
            model = l.split(':', 1)[1].strip()
        elif l.startswith('physical id'):
            phys = l.split(':', 1)[1].strip()
        elif l.startswith('core id'):
            core = l.split(':', 1)[1].strip()
            cores.add((phys, core))
    mem = next(int(l.split()[1]) for l in open('/proc/meminfo') if l.startswith('MemTotal'))
    v['setup.host'] = f'{model} ({len(cores) or threads} cores, {threads} threads) and {round(mem / 1048576)} GiB of RAM'
    return v


def write_csv(name, header, rows):
    with open(os.path.join(TABLES, f'{name}.csv'), 'w', newline='') as f:
        w = csv.writer(f, lineterminator='\n')
        w.writerow(header)
        w.writerows(rows)


def write_tex(name, keys, v):
    with open(os.path.join(TABLES, f'{name}.tex'), 'w') as f:
        f.write(f'% {name}: the produced keys in the paper\'s numbers.tex form (skipped keys are absent)\n')
        for k in keys:
            if k in v and not v[k].startswith('skipped'):
                f.write(f'\\@namedef{{nr@{k}}}{{\\nrMeasured{{{tex_escape(print_form(v[k]))}}}}}\n')


def main():
    os.makedirs(C.OUT, exist_ok=True)
    os.makedirs(TABLES, exist_ok=True)
    v, per = measure.measure()
    vs, slocs = sloc.sloc()
    vi, itab = inator_types.measure()
    v.update(vs)
    v.update(vi)
    v.update(setup_keys())
    with open(os.path.join(C.OUT, 'keys.txt'), 'w') as f:
        for k in sorted(v):
            f.write(f'{k} = {v[k]}\n')

    # Table effect-all: SLOC, every declaration, every use
    ka = lambda p: C.K(p)
    rows = []
    for p in C.PROGS + ['total']:
        k = ka(p)
        rows.append([p, v.get(f'setup.{k}.sloc', v['setup.sloc'] if p == 'total' else ''),
                     v[f'rq1.{k}.alldecl.before'], v[f'rq1.{k}.alldecl.rate'], v[f'rq2.{k}.alldecl.crown'],
                     v[f'rq2.{k}.alldecl.laertes'], v[f'rq1.{k}.uses.before'], v[f'rq1.{k}.uses.rate'],
                     v[f'rq2.{k}.uses.crown'], v[f'rq2.{k}.uses.laertes']])
    write_csv('effect-all', ['program', 'sloc', 'declarations', 'ours', 'crown', 'laertes', 'uses', 'ours', 'crown',
                             'laertes'], rows)
    all_keys = [f'{f}.{ka(p)}.{s}' for p in C.PROGS + ['total'] for f, s in
                (('rq1', 'alldecl.before'), ('rq1', 'alldecl.rate'), ('rq2', 'alldecl.crown'), ('rq2', 'alldecl.laertes'),
                 ('rq1', 'uses.before'), ('rq1', 'uses.rate'), ('rq2', 'uses.crown'), ('rq2', 'uses.laertes'))]
    all_keys += [f'setup.{ka(p)}.sloc' for p in C.PROGS] + ['setup.sloc']
    write_tex('effect-all', all_keys, v)

    # Table effect-crown: CROWN's population (mutable non-array pointer declarations and their uses)
    rows = []
    for p in C.PROGS + ['total']:
        k = ka(p)
        dc = v.get(f'rq2.{k}.decl.crown', v.get('rq2.total.decl.crown-rate', '')) if p != 'total' else v['rq2.total.decl.crown-rate']
        dl = v.get(f'rq2.{k}.decl.laertes', '') if p != 'total' else v['rq2.total.decl.laertes-rate']
        rows.append([p, v[f'rq1.{k}.decl.before'], v[f'rq1.{k}.decl-twin.rate'], dc, dl, v[f'rq1.{k}.decl-uses.before'],
                     v[f'rq1.{k}.decl-uses-twin.rate'], v[f'rq2.{k}.decl-uses.crown'], v[f'rq2.{k}.decl-uses.laertes']])
    write_csv('effect-crown', ['program', 'declarations', 'ours', 'crown', 'laertes', 'uses', 'ours', 'crown',
                               'laertes'], rows)
    crown_keys = [f'rq1.{ka(p)}.{s}' for p in C.PROGS + ['total'] for s in
                  ('decl.before', 'decl-twin.rate', 'decl-uses.before', 'decl-uses-twin.rate')]
    crown_keys += [f'rq2.{ka(p)}.{s}' for p in C.PROGS for s in ('decl.crown', 'decl.laertes')]
    crown_keys += ['rq2.total.decl.crown-rate', 'rq2.total.decl.laertes-rate']
    crown_keys += [f'rq2.{ka(p)}.{s}' for p in C.PROGS + ['total'] for s in ('decl-uses.crown', 'decl-uses.laertes')]
    write_tex('effect-crown', crown_keys, v)

    # Table effect-inator: the eight's interface positions by form
    rows = []
    for q in C.EIGHT + ['total']:
        k = f'rq3.inator.{q}'
        rows.append([q, v[f'{k}.loc'], v[f'{k}.types.pos']] + [v[f'{k}.types.inator.{b}'] for b in inator_types.FORMS]
                    + [v[f'{k}.types.ours.{b}'] for b in inator_types.OURS])
    write_csv('effect-inator', ['program', 'c_lines', 'positions'] + [f'inator_{b}' for b in inator_types.FORMS]
              + [f'ours_{b}' for b in inator_types.OURS], rows)
    inator_keys = [f'rq3.inator.{q}.{s}' for q in C.EIGHT + ['total'] for s in
                   ['loc', 'types.pos'] + [f'types.inator.{b}' for b in inator_types.FORMS]
                   + [f'types.ours.{b}' for b in inator_types.OURS]]
    write_tex('effect-inator', inator_keys, v)
    write_tex('setup', ['setup.programs', 'setup.rustc', 'setup.solver', 'setup.host'], v)

    n = len(v)
    s = sum(1 for x in v.values() if x.startswith('skipped'))
    print(f'rq1: {n} keys, {n - s} produced, {s} skipped -> {os.path.join(C.OUT, "keys.txt")}')


if __name__ == '__main__':
    main()
