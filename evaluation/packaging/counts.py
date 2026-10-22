#!/usr/bin/env python3
"""The counts the derivation prints for the development-material bar (every one 0 before a zip is made), over the
derived tree W after the rename. Writes each list under $ZS/hits/ and prints one line per count; the last line is
`#BAR <sum>`.
  test files       files under a tests/, testdata/ or fixtures/ directory, or named *_tests.rs, tests.rs, test_*.py
  drivers          the measurement drivers, the per-program worker, frames/ and the crates' tools/ (MEASUREMENT_PATHS)
  env off record   environment names the translator's sources name (a "JOBCRAT_..." literal, or a literal read by
                   env::var / env::var_os) that config/analysis-env.sh does not export, that artifact/run.sh does not
                   set, and that are not the toolchain's (ENV_TOOLCHAIN)
  artifact hooks   lines of artifact/ matching a development switch or hook (ARTIFACT_HOOKS, one regex per line)
Environment: W, ZS; MEASUREMENT_PATHS, ENV_TOOLCHAIN, ENV_RUN_SH, ARTIFACT_HOOKS override the defaults below."""
import os, re, subprocess
W = os.environ['W'].rstrip('/'); H = os.environ['ZS'] + '/hits'; os.makedirs(H, exist_ok=True)
MEASUREMENT_PATHS = os.environ.get('MEASUREMENT_PATHS', r'(^|/)(bo_c1|a4_[a-z0-9_]*|a5_measurement|s23_measurement|'
    r'p_b_measurement|kind_equate_core_census|copy_lend_funnel|era5_worker)(\.rs|/)|(^|/)frames/|^crates/[^/]+/tools/')
ENV_TOOLCHAIN = set(os.environ.get('ENV_TOOLCHAIN', 'DIR SYSROOT LD_LIBRARY_PATH TMPDIR HOME PATH RUSTUP_HOME '
    'RUSTUP_TOOLCHAIN MULTIRUST_HOME MULTIRUST_TOOLCHAIN CARGO CARGO_HOME').split())
ENV_RUN_SH = set(os.environ.get('ENV_RUN_SH', 'JOBCRAT_FALLBACK_SLICE_EXTENT JOBCRAT_ERA5C_RAW_CAUSE_LEDGER').split())
ARTIFACT_HOOKS = [h for h in os.environ.get('ARTIFACT_HOOKS', r'''\bTP_ONLY\b
\bEXPECTED_TREES\b
order-variant
case \$LG in
"--trace"
"--reclassify"
"--beta"''').splitlines() if h]

files = subprocess.run(['git', '-C', W, 'ls-files'], stdout=subprocess.PIPE, text=True).stdout.split()
src = [f for f in files if re.match(r'^(crates|src|deps_crate)/', f)]
out = []

tests = [f for f in src if re.search(r'(^|/)(tests|testdata|fixtures)/|(^|/)(\w+_tests|tests)\.rs$|(^|/)test_\w+\.py$', f)]
open(H + '/test-files.txt', 'w').write(''.join(f + '\n' for f in tests))
out.append(('test files and fixtures', len(tests)))

drv = [f for f in files if re.search(MEASUREMENT_PATHS, f)]
open(H + '/drivers.txt', 'w').write(''.join(f + '\n' for f in drv))
out.append(('measurement drivers, the worker, frames/, tools/ (files)', len(drv)))

read = set()
for f in src:
    if not f.endswith('.rs'): continue
    t = open(f'{W}/{f}', encoding='utf-8').read()
    read |= set(re.findall(r'"(JOBCRAT_[A-Z0-9_]+)"', t))
    read |= set(re.findall(r'env::var(?:_os)?\(\s*"([A-Za-z_][A-Za-z0-9_]*)"', t))
cfg = f'{W}/config/analysis-env.sh'
record = set(re.findall(r'^export ([A-Za-z_][A-Za-z0-9_]*)=', open(cfg).read(), re.M)) if os.path.exists(cfg) else set()
off = sorted(read - record - ENV_RUN_SH - ENV_TOOLCHAIN)
open(H + '/env-off-record.txt', 'w').write(''.join(n + '\n' for n in off))
out.append((f'environment names off the record ({len(read)} named; {len(read & record)} of the record)', len(off)))

hooks = []
for f in files:
    if not f.startswith('artifact/'): continue
    try: lines = open(f'{W}/{f}', encoding='utf-8').read().split('\n')
    except (UnicodeDecodeError, IsADirectoryError): continue
    for i, l in enumerate(lines, 1):
        for h in ARTIFACT_HOOKS:
            if re.search(h, l): hooks.append(f'{f}:{i}\t{h}\t{l.strip()[:160]}')
open(H + '/artifact-hooks.tsv', 'w').write(''.join(h + '\n' for h in hooks))
out.append((f'artifact/ lines with a development switch or hook ({len({h.split(chr(9))[1] for h in hooks})} of '
            f'{len(ARTIFACT_HOOKS)} patterns)', len(hooks)))

for k, v in out: print(f'   {k}: {v}')
print(f'#BAR {sum(v for _, v in out)}')
