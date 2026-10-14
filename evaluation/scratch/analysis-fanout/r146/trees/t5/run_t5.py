#!/usr/bin/env python3
"""relay 116 / S25b (Table 5, CROWN's population, the uses columns): runs the PRE-BUILT typed counter
(rq2_pos_counter, analysis-fanout 031; nothing built) per (side, program) into t5/out/<side>/<p>/, exactly as
pos_census.run does (same EXE, env, universe file, --strip-src for flat Laertes layouts, the E0557 feature-gate shim
for Laertes trees), with two additions: the side list below, and relay 117's mechanical `llvm_asm!` adaptation
(r117/adapt_llvm_asm.py, run unchanged into t5/adapted/) for any Laertes tree that holds `llvm_asm!` (libzahl).

usage: run_t5.py SIDE [PROG ...]
  SIDE: input | crown | derived | derived_pre814 | ours14u | ours54p | laertes_after | laertes_before"""
import os, subprocess, sys, time

TOOLS = 'tmp/scratchpad/wt067/agents/tools/rq2'
sys.path.insert(0, TOOLS)
import pos_census as P  # noqa: E402
import seed_rq2 as SR  # noqa: E402

T5 = 'scratch/analysis-fanout/r146/trees/t5'
OUT = os.path.join(T5, 'out')
ADAPT = 'scratch/analysis-fanout/r117/adapt_llvm_asm.py'
CENSUS = {'ours14u': 'scratch/main/frame14u',
          'ours54p': 'scratch/main/b54p',
          'ours56': 'scratch/main/batch56',
          'ours58': 'scratch/main/batch58',
          'ours58pp': 'scratch/main/batch58pp',
          'ours58pps39': 'scratch/main/batch58pps39',
          'ours60sp': 'scratch/main/batch60sp'}


def side_dir(side, p):
    if side == 'input':
        return f'{P.INPUT}/{p}', False
    if side == 'crown':
        return f'{P.CROWN}/{p}', False
    if side == 'derived':          # the substrate the census consumes (expand -> extern -> preprocess)
        return f'{P.CRAT}/benchmarks/rs-crown-derived/{p}', False
    if side == 'derived_pre814':   # 54' (b54p, 10-04) consumed brotli / lodepng before R814's 10-05 regeneration
        d = f'{P.CRAT}/benchmarks/rs-crown-derived.pre-r814/{p}'
        return (d if os.path.isdir(d) else f'{P.CRAT}/benchmarks/rs-crown-derived/{p}'), False
    if side in CENSUS:
        return os.path.join(CENSUS[side], 'emitted-trees', p), False
    d, flat = SR.laertes_root(p)
    if d is None:
        return None, False
    if side == 'laertes_before':
        d = d.replace('/after/', '/before/')
    return d, flat


def has_llvm_asm(d):
    for dp, _, fs in os.walk(d):
        for f in fs:
            if f.endswith('.rs') and 'llvm_asm!' in open(os.path.join(dp, f), errors='replace').read():
                return True
    return False


def main():
    side, progs = sys.argv[1], sys.argv[2:] or P.PROGRAMS
    exe = P.EXE
    assert os.path.isfile(exe), exe
    sr = P.sysroot()
    env = dict(os.environ, SYSROOT=sr, LD_LIBRARY_PATH=f'{sr}/lib', DIR=P.CRAT, RUSTUP_TOOLCHAIN=P.TOOLCHAIN)
    log = open(os.path.join(OUT, f'run-{side}.log'), 'a')
    for p in progs:
        d, flat = side_dir(side, p)
        dest = os.path.join(OUT, side, p)
        os.makedirs(dest, exist_ok=True)
        for f in os.listdir(dest):
            os.remove(os.path.join(dest, f))
        if not d or not os.path.isdir(d):
            open(os.path.join(dest, 'status.txt'), 'w').write(f'no-tree\t{d}\n')
            print(f'{side}\t{p}\tno-tree\t{d}', file=log, flush=True)
            continue
        note = []
        if side.startswith('laertes') and has_llvm_asm(d):
            # R882-1 (relay 117): the mechanical llvm_asm! -> asm! adaptation, relay 117's script unchanged
            ad = os.path.join(T5, 'adapted', side, p)
            os.makedirs(os.path.dirname(ad), exist_ok=True)
            subprocess.run(['python3', ADAPT, d, ad], check=True, capture_output=True, text=True)
            note.append(f'llvm_asm adapted by {ADAPT} into {ad}')
            d = ad
        r = P.root_of(d)
        uf = os.path.join(OUT, 'universe', f'{p}{"-flat" if flat else ""}.txt')
        os.makedirs(os.path.dirname(uf), exist_ok=True)
        open(uf, 'w').write('\n'.join(sorted(P.universe(p, flat))) + '\n')
        cmd = ['nice', '-n', '10', '/usr/bin/time', '-f', 'wall=%e maxrss_kb=%M', exe, '--root', r, '--out', dest,
               '--universe', uf] + (['--strip-src'] if flat else [])
        t0 = time.time()
        pr = subprocess.run(cmd, env=env, capture_output=True, text=True)
        if pr.returncode and side.startswith('laertes'):
            removed = P.removed_features(pr.stderr)
            if removed:
                r, shim = P.shim_tree(os.path.join(T5, 'shimroot', side), p, d, r, removed)  # t5/shimroot/<side>/shim/laertes/<p>
                cmd = cmd[:7] + ['--root', r] + cmd[9:]
                pr = subprocess.run(cmd, env=env, capture_output=True, text=True)
                note.append(f'removed feature gates: {",".join(sorted(removed))}; shim tree: {shim}')
        st = 'ok' if pr.returncode == 0 else f'exit-{pr.returncode}'
        if pr.returncode:
            open(os.path.join(dest, 'stderr.txt'), 'w').write(pr.stderr[-20000:])
        open(os.path.join(dest, 'flat.txt'), 'w').write('flat\n' if flat else 'tree\n')
        open(os.path.join(dest, 'cmd.txt'), 'w').write(' '.join(cmd) + '\n' + '\n'.join(note) + '\n')
        if st != 'ok' and not os.path.exists(os.path.join(dest, 'status.txt')):
            open(os.path.join(dest, 'status.txt'), 'w').write(f'{st}\t{r}\n')
        tail = pr.stderr.strip().splitlines()
        print(f'{side}\t{p}\t{st}\t{r}\t{time.time() - t0:.1f}s\t{tail[-1] if tail else "-"}\t{"; ".join(note)}',
              file=log, flush=True)
        print(side, p, st, f'{time.time() - t0:.1f}s', '; '.join(note), flush=True)


if __name__ == '__main__':
    main()
