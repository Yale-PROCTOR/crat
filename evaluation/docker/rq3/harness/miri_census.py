#!/usr/bin/env python3
"""The Miri census (R621-2 / R623-1, wave-6o report 084): the runtime census's
drivers and inputs, run under Miri on the newer nightly (the census's compile
toolchain is unchanged; only this runner moves).

usage: miri_census.py <census-dir> <work-dir> [--programs p,q] [--inputs a,b]
       [--discipline TB|SB] [--variant emitted|substrate] [--timeout S] [--native <native work dir>]
prints one receipt per program:
  miri program=<p> discipline=<TB|SB> inputs=<n> pass=<k> fabricated_extent=<f>
  input_ub=<i> allocator=<a> unsupported=<u> other=<o> wall=<s>
  unsupported_names=<n:count,..> coverage=<full|prefix-to:<fn>,..> frame=<f>
and writes <work-dir>/<p>/miri-runs.tsv with the first report per input.

Per (program, driver) a Cargo project is generated: the tree (the same two
textual edits as the native runner, plus the one feature-gate rename the newer
nightly needs: `derive_clone_copy` -> `derive_clone_copy_internals`), the
harness's C-library models mounted as a module (`miri/jobcrat_libc_models.rs`,
R622-2 STOP 2), `panic = "abort"` for every crate, the pinned deps_crate lock.
Nothing else is added; the allocator line is never added.

`input_ub` is assigned only by the substrate rule (R674-7 (1)): the substrate's own
Miri run (`--variant substrate`, run first into the same work dir) reports the same
class on the same input; any other UB report the classifier cannot place in a
fabricated-extent construction is `other` until traced. `fabricated_extent_sites`
counts distinct (fn, line) sites: the §77 class is the same at any N (R693-1).
"""
import csv, glob, os, re, shutil, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import runtime_census as rc  # noqa: E402
import miri_oracle  # noqa: E402
import miri_trace  # noqa: E402
import miri_repair  # noqa: E402

MODELS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "jobcrat_libc_models.rs")
MIRI_TOOLCHAIN = os.environ.get("MIRI_TOOLCHAIN", "nightly-2026-09-17")  # rustc 923c95cdf (2026-09-16), its miri
LOCK = os.path.join(rc.SRC, "deps_crate", "Cargo.lock")


# Relay 128 §3: harness-side edits that make three programs runnable under Miri, declared and
# recorded per project (`harness-edits.txt`), never in the emitted program:
#   tulipindicators: the program's `#[no_mangle]` data statics `open` / `close` clash with the
#     runtime's symbols; their SYMBOL is renamed (`#[export_name]`), the Rust items are unchanged;
#   bzip2: Miri's shim refuses the program's `signal(..)` registrations; the calls go to a declared
#     stub returning the default handler (no signal is raised on the inputs run);
#   libtree: `glob` has no Miri shim; a declared model returns GLOB_NOMATCH with an empty result
#     (libtree then reads no ld.so.conf include files: a stated deviation of the input).
HARNESS_EDITS = {
    "tulipindicators": [(r"#\[no_mangle\](\s*pub static mut (open|close)\b)",
                         r'#[export_name = "jobcrat_miri_tulip_\2"]\1')],
    "bzip2": [(r"(?<![\w:])(?<!fn )signal\((?=\d+ as std::os::raw::c_int)", "crate::jobcrat_miri_signal(")],
    "robotfindskitten": [(r"(?<![\w:])(?<!fn )signal\((?=\d+ as libc::c_int)", "crate::jobcrat_miri_signal(")],
    # the provided test's own UB, class (a), recorded first (pass A, 095): `printf("%d", sizeof(binn))`
    # passes a size_t for %d (C11 7.21.6.1p9); the Miri copy passes an int so coverage continues
}
# Edits to a file the driver brings in by `#[path]` (the edit is applied to a copy in the Miri project
# and the path redirected): binn's provided test has its own UB, class (a), recorded first (pass A,
# 095): `printf("%d", sizeof(binn))` passes a size_t for %d (C11 7.21.6.1p9); the copy passes an int
HARNESS_FILE_EDITS = {
    "binn": {"test_binn.rs": [(r'(sizeof\(binn\) = %d\\n\\n\\0" as \*const u8 as \*const libc::c_char,\s*::std::mem::size_of::<binn>\(\)) as libc::c_ulong',
                               r"\1 as libc::c_int")]},
}
SIGNAL_STUB = ("\n// harness (relay 128 §3): Miri refuses signal registration; declared stub (no signal is raised)\n"
               "#[allow(dead_code)]\nunsafe fn jobcrat_miri_signal<A>(_: std::os::raw::c_int, _: A)\n"
               "    -> Option<unsafe extern \"C\" fn(std::os::raw::c_int)> { None }\n")
HARNESS_APPEND = {
    "bzip2": SIGNAL_STUB,
    "robotfindskitten": SIGNAL_STUB,
    "libtree": "\n// harness (relay 128 §3): a declared glob model (GLOB_NOMATCH, empty result)\n"
               "#[no_mangle]\npub unsafe extern \"C\" fn glob(_p: *const std::os::raw::c_char, _f: std::os::raw::c_int,\n"
               "    _e: *mut std::os::raw::c_void, g: *mut usize) -> std::os::raw::c_int {\n"
               "    if !g.is_null() { *g = 0; *g.add(1) = 0; *g.add(2) = 0; }\n    3\n}\n"
               "#[no_mangle]\npub unsafe extern \"C\" fn globfree(_g: *mut std::os::raw::c_void) {}\n",
}
# Relay 133 item 4: a program the native runtime census does not configure, run under Miri only
# (json.h: the provided tests as a generated Rust driver, drivers/json.h/make_rs.py)
MIRI_PROGRAMS = {"json.h": dict(kind="cdriver", c_dir=None, drivers={"main": None},
                                runs=[("main", "main", [], None, [])])}
# A shell-driven native input whose shell only prepares the run dir: the Rust driver does it
# (heman's `mkdir -p build && "$BIN"`)
MIRI_RUN_ARGS = {("heman", "test_sdf"): []}
# Relay 129 pass B (diagnostic, NOT of record): R443's declaration, added harness-side
GLOBAL_ALLOCATOR = "\n// harness, pass B (relay 129; NOT of record): R443's declaration\n#[global_allocator]\nstatic JOBCRAT_MIRI_SYSTEM_ALLOCATOR: std::alloc::System = std::alloc::System;\n"


def project(tree_root, module, var, cfg, proj, program="", pass_b=False, pass_c=False, trace_census=None, repairs=None):
    text = open(tree_root, encoding="utf-8", errors="replace").read()
    if module.endswith(".rs"):
        # a transcribed Rust driver (report 084, STOP 3), appended to the tree's crate
        body = text + "\n" + open(module).read().replace("@DRIVERS@", rc.DRIVERS)
    else:
        body = rc.shim(text, module)
    body = body.replace("#![feature(derive_clone_copy)]", "#![feature(derive_clone_copy_internals)]", 1)
    # the newer nightly's deny-by-default lints (the census caps lints; so does this runner)
    body = "#![allow(unknown_lints, dangerous_implicit_autorefs, invalid_reference_casting)]\n" + body
    body += f'\n// harness: the C-library models (not the program)\n#[path = "{MODELS}"]\nmod jobcrat_libc_models;\n'
    edits = []
    for pat, rep in HARNESS_EDITS.get(program, []):
        body, n = re.subn(pat, rep, body)
        edits.append(f"subst {n}x: {pat} -> {rep}")
    for name, subs in HARNESS_FILE_EDITS.get(program, {}).items():
        m = re.search(r'#\[path = "([^"]*/' + re.escape(name) + r')"\]', body)
        if not m:
            edits.append(f"file {name}: no #[path] found")
            continue
        src = open(m.group(1)).read()
        for pat, rep in subs:
            src, n = re.subn(pat, rep, src)
            edits.append(f"file {name} subst {n}x: {pat} -> {rep}")
        os.makedirs(os.path.join(proj, "src"), exist_ok=True)
        local = os.path.join(proj, "src", f"harness_{name}")
        open(local, "w").write(src)
        body = body.replace(m.group(0), f'#[path = "{local}"]')
    if program in HARNESS_APPEND:
        body += HARNESS_APPEND[program]
        edits.append("append: " + HARNESS_APPEND[program].strip().splitlines()[0])
    if pass_b:
        body += GLOBAL_ALLOCATOR
        edits.append("append: #[global_allocator] System (pass B, not of record)")
    if repairs is not None:
        # relay 138 (R779-1): the input-repair pass, the same declared edit in the input and the
        # output copy (rule 2: the output only where its text is byte-equal to the input's)
        sub_root = rc.crate_root(os.path.join(rc.SUBSTRATE, program))
        sub_text = open(sub_root, encoding="utf-8", errors="replace").read() if var == "emitted" else None
        body, rec = miri_repair.apply(body, program, var, repairs, sub_text)
        edits += rec
    if pass_c:
        # relay 133 pass C (NOT of record): the oracle extents (miri_oracle.py)
        body, rec, _, _ = miri_oracle.apply(body)
        edits += rec
    if trace_census:
        # relay 137 item 1: the function-entry trace of the functions with a delivered declaration
        body, own, rec = miri_trace.apply(body, trace_census, program)
        edits.append(rec)
        os.makedirs(proj, exist_ok=True)
        open(os.path.join(proj, "trace-owners.txt"), "w").write("\n".join(own) + "\n")
    os.makedirs(os.path.join(proj, "src"), exist_ok=True)
    open(os.path.join(proj, "harness-edits.txt"), "w").write("\n".join(edits) + "\n")
    open(os.path.join(proj, "src", "main.rs"), "w").write(body)
    deps = 'libc = "0.2"\n'
    if "extern crate c2rust_bitfields" in text:
        deps += 'c2rust-bitfields = "0.3"\n'
    open(os.path.join(proj, "Cargo.toml"), "w").write(
        f'[package]\nname = "miri-run"\nversion = "0.1.0"\nedition = "2021"\n[dependencies]\n{deps}'
        f'[profile.dev]\npanic = "abort"\n[[bin]]\nname = "miri-run"\npath = "src/main.rs"\n')
    shutil.copy(LOCK, os.path.join(proj, "Cargo.lock"))
    return os.path.join(proj, "src", "main.rs")


REPORT = re.compile(r"^error: (Undefined Behavior|unsupported operation|abnormal termination)[^:]*: (.*)$", re.M)
SITE = re.compile(r"-->\s+src/main\.rs:(\d+):(\d+)")
PANIC = re.compile(r"panicked at src/main\.rs:(\d+):\d+:\n(.*)")


PROGRAM = [""]   # the program being classified (set by main / reclassify)


def classify(stderr, code, main_rs):
    """-> (kind, detail, fn, line)"""
    if code == 0 or (code == 0 and "error:" not in stderr):
        # Miri exits non-zero on UB / an unsupported operation; a warning that merely contains
        # `error:` is not a report (tulip's 1,484 lint warnings)
        return "pass", "-", "-", "-"
    m = REPORT.search(stderr)
    p = PANIC.search(stderr)
    line = None
    if p:
        line = int(p.group(1))
        detail = "panic: " + p.group(2).strip()[:160]
    elif m:
        after = stderr[m.end():]
        s = SITE.search(after)
        line = int(s.group(1)) if s else None
        detail = f"{m.group(1)}: {m.group(2).strip()[:160]}"
    elif code == "timeout":
        return "timeout", "-", "-", "-"
    else:
        return "other", f"exit {code}: {stderr.strip().splitlines()[-1][:160] if stderr.strip() else '-'}", "-", "-"
    fn = "-"
    text = ""
    if line:
        toks, funcs, offs = rc._index(main_rs)
        owner = rc.owner_of(funcs, rc._first_at(toks, offs[line - 1]))
        fn = owner[0] if owner else "-"
        text = open(main_rs, encoding="utf-8", errors="replace").read().split("\n")[line - 1]
    if "longjmp-reached" in stderr:
        # the harness's setjmp / longjmp model (relay 109): coverage ends at the first longjmp
        return "unsupported", "longjmp", fn, line
    if m and m.group(1) == "unsupported operation":
        name = re.search(r"foreign function `([^`]+)`", m.group(2))
        return "unsupported", (name.group(1) if name else m.group(2)[:80]), fn, line
    if re.search(r"allocat(ed|or).*(different|C heap|Rust heap)|deallocat.*using", detail):
        return "allocator", detail, fn, line
    # the span Miri renders for the report (from the report to "occurred here")
    span = ""
    if m:
        span = stderr[m.end():]
        span = span[:span.find("occurred here") + 1] if "occurred here" in span else span[:1500]
    if "FALLBACK_SLICE_EXTENT" not in text + span and m:
        # the report's own site may be inside a helper (the cursor's `from_raw_parts(ptr, len)`):
        # the construction's fabricated extent is then on one of the first program frames
        lines = open(main_rs, encoding="utf-8", errors="replace").read().split("\n")
        for a, b in re.findall(r"at src/main\.rs:(\d+):\d+(?:: (\d+):\d+)?", stderr[m.end():])[:4]:
            frame = "\n".join(lines[int(a) - 1:int(b or a)])  # the frame's whole span
            if "FALLBACK_SLICE_EXTENT" in frame or "jobcrat_miri_extent(&__jobcrat_b" in frame:
                text = frame
                break
    created = re.search(r"was created here.*?\n((?:.*\n){1,4})", stderr[m.end():] if m else "")
    if m and created and "jobcrat_miri_extent(&__jobcrat_b" in created.group(1):
        # pass C: the accessed reference is an oracle-extent slice, longer than the C array it stands
        # for when sibling arrays share one allocation (genann's weights / outputs): its length is the
        # waived quantity, so the report is class (d), listed with its site
        k = re.search(r"jobcrat_miri_extent\(&__jobcrat_b(\d+)", created.group(1))
        return "fabricated-extent", f"oracle-extent-overlap site={k.group(1) if k else '?'}: " + detail, fn, line
    if m and "jobcrat_miri_extent(&__jobcrat_b" in text + span and \
            re.search(r"constructing invalid value|dangling reference|beyond the bounds", detail):
        # pass C: a report at an oracle-extent construction is the fallback kept for an unresolved
        # base (class (d), the site printed `jobcrat-miri-unresolved`) or a wrong extent (a STOP)
        k = re.search(r"jobcrat_miri_extent\(&__jobcrat_b(\d+)", text + span)
        if k and f"jobcrat-miri-unresolved site={k.group(1)}\n" in stderr:
            return "fabricated-extent", f"unresolved-base site={k.group(1)}: " + detail, fn, line
        return "other", f"oracle-extent-wrong site={k.group(1) if k else '?'}: " + detail, fn, line
    if "FALLBACK_SLICE_EXTENT" in text or "FALLBACK_SLICE_EXTENT" in span:
        # R693-1 (relay 120): the §77 / R481 class is the retag / access BEYOND the allocation, the
        # same at any N; a report at a fabricated construction whose allocation already covers the
        # requested bytes is not that class and stays `other` (a STOP)
        sz, want = re.search(r"has size (\d+)", span + detail), re.search(r"(?:pointer to|of size|to) (\d+) bytes?", span + detail)
        if sz and want and int(sz.group(1)) >= int(want.group(1)):
            return "other", "fabricated-extent-inside-allocation: " + detail, fn, line
        if not re.search(r"beyond the bounds of its allocation|out-of-bounds|has size \d+", detail + span):
            # a report at a fabricated construction that is not about the extent (e.g. an aliasing retag)
            return "other", "at-fabricated-construction: " + detail, fn, line
        return "fabricated-extent", detail, fn, line
    return "other", detail, fn, line


def beta_callees(path):
    """main 144's (beta) rows: per program, the callee functions whose thin Ref formal is bridged
    from a raw pointer with no dominating dereference (the P7 sites, R758-1)."""
    out, on = {}, False
    for line in open(path):
        if line.startswith("(beta) rows"):
            on = True
            continue
        if on:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 2 or "::" not in parts[1]:
                if line.strip() == "":
                    continue
                if not line[0].isalpha():
                    break
                continue
            out.setdefault(parts[0], set()).add(parts[1].split("::")[-2])
    return out


def refine(result, main_rs, beta):
    """The classes of record (relays 119 / 127 / 129) beyond the classifier's kinds:
    known-r443   a Rust deallocation of C-heap memory (or the reverse) with no #[global_allocator]
                 System (R443 ruled, not yet emitted: one line fixes it; main 250 in 54);
    known-r416-5 a panic on a one-element slice (`len is 1`): R416-5's from_ref bridge (main 250 §4);
    premise-p7   a reference-validity report whose first site is a call into a P7 (beta) callee."""
    kind, detail, fn, line = result
    if kind == "allocator":
        return "known-r443", detail, fn, line
    if detail.startswith("panic:") and re.search(r"len is 1\b|length 1\b", detail):
        return "known-r416-5", detail, fn, line
    if kind == "other" and beta and line not in ("-", None):
        text = open(main_rs, encoding="utf-8", errors="replace").read().split("\n")[int(line) - 1]
        if re.search(r"dangling|retag|invalid value|reference|not granting", detail) and \
                any(re.search(rf"\b{re.escape(c)}\s*\(", text) for c in beta):
            return "premise-p7", detail, fn, line
    return kind, detail, fn, line


def reclassify(work, var, disc, beta):
    """Re-read each saved first report (runs-<var>/<input>/miri-stderr) under the current
    classifier, without re-running Miri; pass / timeout rows and absent stderr stay as recorded."""
    for f in sorted(glob.glob(os.path.join(work, "*", f"miri-runs-{var}-{disc}.tsv"))):
        pw = os.path.dirname(f)
        program = os.path.basename(pw)
        PROGRAM[0] = program
        main_rs = next(iter(glob.glob(os.path.join(pw, f"proj-{var}-*", "src", "main.rs"))), None)
        rows = list(csv.DictReader(open(f), delimiter="\t"))
        for r in rows:
            se_path = os.path.join(pw, f"runs-{var}", r["input"], "miri-stderr")
            if r["first_report"] in ("pass", "timeout") or not main_rs or not os.path.exists(se_path):
                continue
            kind, detail, fn, line = refine(classify(open(se_path).read(), 1, main_rs), main_rs,
                                            beta.get(program, set()))
            r.update(first_report=kind, detail=detail, fn=fn, line=str(line))
        with open(f, "w") as t:
            t.write("input\tfirst_report\tdetail\tfn\tline\twall_s\n")
            for r in rows:
                t.write("\t".join(str(r[k]) for k in ("input", "first_report", "detail", "fn", "line", "wall_s")) + "\n")
        print(f"reclassified {program}: {dict((k, sum(1 for r in rows if r['first_report'] == k)) for k in sorted({r['first_report'] for r in rows}))}")


def main(argv):
    if "--reclassify" in argv:
        disc = argv[argv.index("--discipline") + 1] if "--discipline" in argv else "TB"
        var = argv[argv.index("--variant") + 1] if "--variant" in argv else "emitted"
        beta = beta_callees(argv[argv.index("--beta") + 1]) if "--beta" in argv else {}
        return reclassify(argv[2], var, disc, beta)
    census, work = argv[1], argv[2]
    only = set(argv[argv.index("--programs") + 1].split(",")) if "--programs" in argv else None
    inputs = set(argv[argv.index("--inputs") + 1].split(",")) if "--inputs" in argv else None
    disc = argv[argv.index("--discipline") + 1] if "--discipline" in argv else "TB"
    var = argv[argv.index("--variant") + 1] if "--variant" in argv else "emitted"
    timeout = int(argv[argv.index("--timeout") + 1]) if "--timeout" in argv else 3600
    pass_b = "--global-allocator" in argv
    pass_c = "--oracle" in argv
    trace = census if "--trace" in argv else None
    repairs = miri_repair.load(argv[argv.index("--repair") + 1]) if "--repair" in argv else None
    beta = beta_callees(argv[argv.index("--beta") + 1]) if "--beta" in argv else {}
    native = argv[argv.index("--native") + 1] if "--native" in argv else \
        os.path.join(work, "..", os.path.basename(work).replace("miri", "b49"))
    flags = "-Zmiri-disable-isolation -Zmiri-ignore-leaks" + (" -Zmiri-tree-borrows" if disc == "TB" else "")
    if pass_c:
        # pass C's registry is keyed on addresses: no reuse, so a stale entry never covers a new allocation
        flags += " -Zmiri-address-reuse-rate=0"
    first = next(iter(glob.glob(os.path.join(census, "*.raw-boundary-subject-outcomes.tsv"))), None)
    frame = next(csv.DictReader(open(first), delimiter="\t"))["analysis_frame"] if first else "-"
    for program, cfg in {**rc.PROGRAMS, **MIRI_PROGRAMS}.items():
        rs_driver = os.path.join(rc.DRIVERS, program, "driver.rs")
        if only and program not in only:
            continue
        if cfg["kind"] != "main0":
            # a Rust driver per C driver: <driver>.driver.rs (relay 107), else the program's driver.rs
            rs = {d: rc.rust_driver(program, d) or (rs_driver if os.path.exists(rs_driver) else None)
                  for d in cfg["drivers"]}
            if not any(rs.values()):
                continue
            cfg = dict(cfg, mains={d: (p, None) for d, p in rs.items() if p},
                       runs=[r for r in cfg["runs"] if rs.get(r[1])])
        PROGRAM[0] = program
        tree = os.path.join(census, "emitted-trees", program) if var == "emitted" else os.path.join(rc.SUBSTRATE, program)
        pw = os.path.join(work, program)
        rows, t_all = [], 0.0
        for input_id, drv, args, stdin, files in cfg["runs"]:
            if inputs and input_id not in inputs:
                continue
            module = cfg["mains"][drv][0]
            proj = os.path.join(pw, f"proj-{var}-{drv}")
            main_rs = os.path.join(proj, "src", "main.rs")
            if not os.path.exists(main_rs):
                rc.prepare_driver(program, tree)
                project(rc.crate_root(tree), module, var, cfg, proj, program, pass_b, pass_c, trace, repairs)
            rundir = os.path.join(pw, f"runs-{var}", input_id)
            if os.path.exists(rundir):
                shutil.rmtree(rundir)
            rc.setup_dir(cfg, rundir)
            fin = subprocess.DEVNULL
            if stdin and stdin.startswith("@stage:"):
                src, dst = stdin[len("@stage:"):].rsplit(":", 1)
                # the C variant's output of the earlier input, from the native run (--native <dir>)
                prior = os.path.join(native, program, "runs", src.split("/", 1)[0], "c", src.split("/", 1)[1])
                shutil.copy(prior, os.path.join(rundir, dst))
            elif stdin:
                fin = open(stdin if os.path.isabs(stdin) else os.path.join(rundir, stdin), "rb")
            env = dict(os.environ, MIRIFLAGS=flags, CARGO_TARGET_DIR=os.path.join(pw, f"target-{var}"))
            cmd = ["cargo", "+" + MIRI_TOOLCHAIN, "miri", "run", "--offline", "-q", "--manifest-path", os.path.join(proj, "Cargo.toml"), "--"]
            args = MIRI_RUN_ARGS.get((program, input_id), args)
            if args[:1] == ["@sh"]:
                continue  # shell-driven inputs (libtree's Makefiles) are native-only
            code, so, se, wall = rc.run_cmd(cmd + args, cwd=rundir, stdin=fin, timeout=timeout, env=env)
            t_all += wall
            se = se.decode(errors="replace")
            open(os.path.join(rundir, "miri-stderr"), "w").write(se)
            open(os.path.join(rundir, "miri-stdout"), "wb").write(so)
            kind, detail, fn, line = refine(classify(se, code, main_rs), main_rs, beta.get(program, set()))
            rows.append((input_id, kind, detail, fn, line, wall, set(re.findall(r"jobcrat-miri-unresolved site=(\d+)", se))))
        with open(os.path.join(pw, f"miri-runs-{var}-{disc}.tsv"), "w") as t:
            t.write("input\tfirst_report\tdetail\tfn\tline\twall_s\tunresolved_sites\n")
            for r in rows:
                t.write("\t".join(str(x) for x in r[:5]) + f"\t{r[5]:.1f}\t{','.join(sorted(r[6], key=int)) or '-'}\n")
        # R674-7 (1) applied to Miri (relay 119 (a)): a first report whose class the substrate's own Miri run
        # reproduces on the same input is the input's UB (the substrate run: --variant substrate, same work dir)
        sub = os.path.join(pw, f"miri-runs-substrate-{disc}.tsv")
        if var == "emitted" and os.path.exists(sub):
            srows = {r["input"]: r for r in csv.DictReader(open(sub), delimiter="\t")}
            norm = lambda d: re.sub(r"alloc\d+|<\d+>|0x[0-9a-f]+|\d+", "#", d)
            for i, r in enumerate(rows):
                s_ = srows.get(r[0])
                if r[1] == "other" and s_ and s_["first_report"] == "other" and norm(s_["detail"]) == norm(r[2]):
                    rows[i] = (r[0], "input-ub", r[2] + f" (substrate: {s_['fn']}:{s_['line']})", *r[3:])
        count = lambda k: sum(1 for r in rows if r[1] == k)
        fab_sites = len({(r[3], r[4]) for r in rows if r[1] == "fabricated-extent"})
        names = {}
        for r in rows:
            if r[1] == "unsupported":
                names[r[2]] = names.get(r[2], 0) + 1
        cov = ",".join(sorted({f"prefix-to:{r[3]}" for r in rows if r[1] == "unsupported"})) or ("full" if rows else "-")
        print(f"miri program={program} variant={var} discipline={disc} inputs={len(rows)} pass={count('pass')} "
              f"fabricated_extent={count('fabricated-extent')} fabricated_extent_sites={fab_sites} "
              f"input_ub={count('input-ub')} allocator={count('allocator')} known_r443={count('known-r443')} "
              f"known_r416_5={count('known-r416-5')} premise_p7={count('premise-p7')} premise_b2={count('premise-b2')} run={'C' if pass_c else 'B' if pass_b else 'A'} unresolved_sites={len({u for r in rows for u in r[6]})} "
              f"unsupported={count('unsupported')} other={count('other') + count('timeout')} wall={t_all:.0f} "
              f"unsupported_names={','.join(f'{k}:{v}' for k, v in names.items()) or '-'} coverage={cov} frame={frame}", flush=True)


if __name__ == "__main__":
    main(sys.argv)
