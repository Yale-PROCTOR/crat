#!/usr/bin/env python3
"""relay 161 (R817-1): libtree's SHIPPED suite (tests/NN `make check`, nine) under Miri. The program under test is
the Miri project of one pass (input/output x A/C/D), reached through a $BIN wrapper that runs `cargo miri run` in the
caller's directory (isolation off: the tests read the ELF files they build) and appends each invocation's stderr to
a per-test log; each test runs exactly as the native census runs it: `ln -sf "$BIN" libtree && make -s -C tests/NN check`.
usage: libtree_suite.py <census> <work> <pass: A|C|D> <variant: substrate|emitted>"""
import os, re, shutil, subprocess, sys
T = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, T)
import runtime_census as rc, miri_census as mc, miri_repair
census, work, pss, var = sys.argv[1:5]
p = "libtree"; cfg = rc.PROGRAMS[p]; mc.PROGRAM[0] = p
tree = os.path.join(census, "emitted-trees", p) if var == "emitted" else os.path.join(rc.SUBSTRATE, p)
pw = os.path.join(work, f"libtree-{pss}-{var}"); os.makedirs(pw, exist_ok=True)
proj = os.path.join(pw, "proj"); tgt = os.path.join(pw, "target")
repairs = (miri_repair.load(os.environ["JOBCRAT_MIRI_REPAIRS"]) if os.environ.get("JOBCRAT_MIRI_REPAIRS") else miri_repair.load()) if pss == "D" else None
pass_c = pss in ("C", "D") and var == "emitted"
module = cfg["mains"]["libtree"][0]
if not os.path.exists(os.path.join(proj, "src", "main.rs")):
    mc.project(rc.crate_root(tree), module, var, cfg, proj, p, False, pass_c, None, repairs)
flags = "-Zmiri-disable-isolation -Zmiri-ignore-leaks -Zmiri-tree-borrows" + (" -Zmiri-address-reuse-rate=0" if pass_c else "")
# cargo/rustup put the toolchain's lib dir into LD_LIBRARY_PATH, which Miri forwards to the program (isolation off):
# the tests set LD_LIBRARY_PATH themselves, so the wrapper hands the CALLER's value to the program (an unset one
# arrives as the empty string: libtree then prints an empty LD_LIBRARY_PATH list where natively it says "not set")
# `cargo miri` has no `build`: the first `cargo miri run` through the wrapper compiles the project
rows = []
for input_id, drv, args, stdin, files in cfg["runs"]:
    if args[:1] != ["@sh"]: continue          # bin-ls is a harness-made input: not the shipped suite (R817-1)
    rundir = os.path.join(pw, "runs", input_id)
    if os.path.exists(rundir): shutil.rmtree(rundir)
    rc.setup_dir(cfg, rundir)
    log = os.path.join(rundir, "miri-invocations.log")
    wrapper = os.path.join(rundir, "miri-libtree.sh")
    open(wrapper, "w").write(f'''#!/bin/bash
echo "=== invocation: $PWD $* LD_LIBRARY_PATH=${{LD_LIBRARY_PATH-}}" >> {log}
MIRIFLAGS="{flags} -Zmiri-env-set=LD_LIBRARY_PATH=${{LD_LIBRARY_PATH-}}" CARGO_TARGET_DIR={tgt} exec cargo +{mc.MIRI_TOOLCHAIN} miri run --offline -q --manifest-path {proj}/Cargo.toml -- "$@" 2>> {log}
''')
    os.chmod(wrapper, 0o755)
    try:
        q = subprocess.run(["bash", "-c", args[1]], cwd=rundir, env=dict(os.environ, BIN=wrapper, CC="gcc"),
                           capture_output=True, text=True, timeout=7200)
        code, out = q.returncode, q.stdout + q.stderr
    except subprocess.TimeoutExpired:
        code, out = "timeout", ""
    text = open(log).read() if os.path.exists(log) else ""
    inv = text.count("=== invocation:")
    m = re.search(r"^error: (Undefined Behavior|unsupported operation|abnormal termination)[^:]*: (.*)$", text, re.M)
    first = f"{m.group(1)}: {m.group(2)}" if m else "-"
    site = re.search(r"-->\s+src/main\.rs:(\d+):(\d+)", text[m.start():]) if m else None
    open(os.path.join(rundir, "make.out"), "w").write(out)
    rows.append((input_id, code, inv, first, site.group(1) if site else "-"))
with open(os.path.join(work, f"libtree-{pss}-{var}.tsv"), "w") as f:
    f.write("input\tmake_exit\tmiri_invocations\tfirst_report\tline\n")
    for row in rows: f.write("\t".join(str(x) for x in row) + "\n")
for row in rows: print(f"libtree {pss} {var}", *row, sep="\t")
