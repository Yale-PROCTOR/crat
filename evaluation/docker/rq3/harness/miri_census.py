#!/usr/bin/env python3
"""The Miri runs: the native runner's
drivers and inputs, run under Miri on the newer nightly (the census's compile
toolchain is unchanged; only this runner moves).

usage: miri_census.py <census-dir> <work-dir> [--programs p,q] [--inputs a,b]
       [--discipline TB|SB] [--variant emitted|substrate] [--timeout S]
prints one receipt per program:
  miri program=<p> discipline=<TB|SB> inputs=<n> pass=<k> fabricated_extent=<f>
  input_ub=<i> allocator=<a> unsupported=<u> other=<o> wall=<s>
  unsupported_names=<n:count,..> coverage=<full|prefix-to:<fn>,..>
and writes <work-dir>/<p>/miri-runs.tsv with the first report per input.

Per (program, driver) a Cargo project is generated: the tree (the same two
textual edits as the native runner, plus the one feature-gate rename the newer
nightly needs: `derive_clone_copy` -> `derive_clone_copy_internals`), the
harness's C-library models mounted as a module (`jobcrat_libc_models.rs`),
`panic = "abort"` for every crate, the pinned deps_crate lock.
Nothing else is added; the allocator line is never added.

`input_ub` is assigned only by the substrate rule: the substrate's own
Miri run (`--variant substrate`, run first into the same work dir) reports the same
class on the same input; any other UB report the classifier cannot place in a
fabricated-extent construction is `other` until traced. `fabricated_extent_sites`
counts distinct (fn, line) sites: the fabricated-extent class is the same at any extent N.
"""
import csv, os, re, shutil, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import runtime_census as rc  # noqa: E402
import miri_oracle  # noqa: E402
import miri_repair  # noqa: E402

MODELS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "jobcrat_libc_models.rs")
MIRI_TOOLCHAIN = os.environ.get("MIRI_TOOLCHAIN", "nightly-2026-09-17")  # rustc 923c95cdf (2026-09-16), its miri
LOCK = os.path.join(rc.SRC, "deps_crate", "Cargo.lock")


# A harness-side edit that makes libtree runnable under Miri, declared and recorded per project
# (`harness-edits.txt`), never in the emitted program: `glob` has no Miri shim; a declared model returns
# GLOB_NOMATCH with an empty result (libtree then reads no ld.so.conf include files: a stated deviation of the input).
HARNESS_APPEND = {
    "libtree": "\n// harness: a declared glob model (GLOB_NOMATCH, empty result)\n"
               "#[no_mangle]\npub unsafe extern \"C\" fn glob(_p: *const std::os::raw::c_char, _f: std::os::raw::c_int,\n"
               "    _e: *mut std::os::raw::c_void, g: *mut usize) -> std::os::raw::c_int {\n"
               "    if !g.is_null() { *g = 0; *g.add(1) = 0; *g.add(2) = 0; }\n    3\n}\n"
               "#[no_mangle]\npub unsafe extern \"C\" fn globfree(_g: *mut std::os::raw::c_void) {}\n",
}
# pass B (a diagnostic, off unless --global-allocator): the emitted programs' #[global_allocator] declaration, added harness-side
GLOBAL_ALLOCATOR = "\n// harness, pass B (diagnostic): the global-allocator declaration\n#[global_allocator]\nstatic JOBCRAT_MIRI_SYSTEM_ALLOCATOR: std::alloc::System = std::alloc::System;\n"


def project(tree_root, module, var, cfg, proj, program="", pass_b=False, pass_c=False, repairs=None):
    text = open(tree_root, encoding="utf-8", errors="replace").read()
    body = rc.shim(text, module)
    body = body.replace("#![feature(derive_clone_copy)]", "#![feature(derive_clone_copy_internals)]", 1)
    # the newer nightly's deny-by-default lints (the census caps lints; so does this runner)
    body = "#![allow(unknown_lints, dangerous_implicit_autorefs, invalid_reference_casting)]\n" + body
    body += f'\n// harness: the C-library models (not the program)\n#[path = "{MODELS}"]\nmod jobcrat_libc_models;\n'
    edits = []
    if program in HARNESS_APPEND:
        body += HARNESS_APPEND[program]
        edits.append("append: " + HARNESS_APPEND[program].strip().splitlines()[0])
    if pass_b:
        body += GLOBAL_ALLOCATOR
        edits.append("append: #[global_allocator] System (pass B, diagnostic)")
    if repairs is not None:
        # the input-repair pass, the same declared edit in the input and the
        # output copy (rule 2: the output only where its text is byte-equal to the input's)
        sub_root = rc.crate_root(os.path.join(rc.SUBSTRATE, program))
        sub_text = open(sub_root, encoding="utf-8", errors="replace").read() if var == "emitted" else None
        body, rec = miri_repair.apply(body, program, var, repairs, sub_text)
        edits += rec
    if pass_c:
        # pass C: the oracle extents (miri_oracle.py)
        body, rec, _, _ = miri_oracle.apply(body)
        edits += rec
    os.makedirs(os.path.join(proj, "src"), exist_ok=True)
    open(os.path.join(proj, "harness-edits.txt"), "w").write("\n".join(edits) + "\n")
    open(os.path.join(proj, "src", "main.rs"), "w").write(body)
    deps = 'libc = "0.2"\n'
    if "extern crate c2rust_bitfields" in text:
        deps += 'c2rust-bitfields = "0.3"\n'
    open(os.path.join(proj, "Cargo.toml"), "w").write(
        f'[package]\nname = "miri-run"\nversion = "0.1.0"\nedition = "2021"\n[workspace]\n[dependencies]\n{deps}'
        f'[profile.dev]\npanic = "abort"\n[[bin]]\nname = "miri-run"\npath = "src/main.rs"\n')
    shutil.copy(LOCK, os.path.join(proj, "Cargo.lock"))
    return os.path.join(proj, "src", "main.rs")


REPORT = re.compile(r"^error: (Undefined Behavior|unsupported operation|abnormal termination)[^:]*: (.*)$", re.M)
SITE = re.compile(r"-->\s+src/main\.rs:(\d+):(\d+)")
PANIC = re.compile(r"panicked at src/main\.rs:(\d+):\d+:\n(.*)")


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
        # the fabricated-extent class is the retag / access BEYOND the allocation, the
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


def refine(result):
    """Two classes beyond the classifier's kinds:
    known-allocator    a Rust deallocation of C-heap memory (or the reverse) with no #[global_allocator]
                       System (the emitted programs declare it; one line fixes such a tree);
    known-one-element  a panic on a one-element slice (`len is 1`): a from_ref bridge."""
    kind, detail, fn, line = result
    if kind == "allocator":
        return "known-allocator", detail, fn, line
    if detail.startswith("panic:") and re.search(r"len is 1\b|length 1\b", detail):
        return "known-one-element", detail, fn, line
    return kind, detail, fn, line


def main(argv):
    census, work = argv[1], argv[2]
    only = set(argv[argv.index("--programs") + 1].split(",")) if "--programs" in argv else None
    inputs = set(argv[argv.index("--inputs") + 1].split(",")) if "--inputs" in argv else None
    disc = argv[argv.index("--discipline") + 1] if "--discipline" in argv else "TB"
    var = argv[argv.index("--variant") + 1] if "--variant" in argv else "emitted"
    timeout = int(argv[argv.index("--timeout") + 1]) if "--timeout" in argv else 3600
    pass_b = "--global-allocator" in argv
    pass_c = "--oracle" in argv
    repairs = miri_repair.load(argv[argv.index("--repair") + 1]) if "--repair" in argv else None
    flags = "-Zmiri-disable-isolation -Zmiri-ignore-leaks" + (" -Zmiri-tree-borrows" if disc == "TB" else "")
    if pass_c:
        # pass C's registry is keyed on addresses: no reuse, so a stale entry never covers a new allocation
        flags += " -Zmiri-address-reuse-rate=0"
    for program, cfg in rc.PROGRAMS.items():
        if only and program not in only:
            continue
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
                project(rc.crate_root(tree), module, var, cfg, proj, program, pass_b, pass_c, repairs)
            rundir = os.path.join(pw, f"runs-{var}", input_id)
            if os.path.exists(rundir):
                shutil.rmtree(rundir)
            rc.setup_dir(cfg, rundir)
            fin = subprocess.DEVNULL
            if stdin:
                fin = open(stdin if os.path.isabs(stdin) else os.path.join(rundir, stdin), "rb")
            env = dict(os.environ, MIRIFLAGS=flags, CARGO_TARGET_DIR=os.path.join(pw, f"target-{var}"))
            cmd = ["cargo", "+" + MIRI_TOOLCHAIN, "miri", "run", "--offline", "-q", "--manifest-path", os.path.join(proj, "Cargo.toml"), "--"]
            if args[:1] == ["@sh"]:
                continue  # shell-driven inputs (libtree's Makefiles) are native-only
            code, so, se, wall = rc.run_cmd(cmd + args, cwd=rundir, stdin=fin, timeout=timeout, env=env)
            t_all += wall
            se = se.decode(errors="replace")
            open(os.path.join(rundir, "miri-stderr"), "w").write(se)
            open(os.path.join(rundir, "miri-stdout"), "wb").write(so)
            kind, detail, fn, line = refine(classify(se, code, main_rs))
            rows.append((input_id, kind, detail, fn, line, wall, set(re.findall(r"jobcrat-miri-unresolved site=(\d+)", se))))
        with open(os.path.join(pw, f"miri-runs-{var}-{disc}.tsv"), "w") as t:
            t.write("input\tfirst_report\tdetail\tfn\tline\twall_s\tunresolved_sites\n")
            for r in rows:
                t.write("\t".join(str(x) for x in r[:5]) + f"\t{r[5]:.1f}\t{','.join(sorted(r[6], key=int)) or '-'}\n")
        # the substrate rule: a first report whose class the substrate's own Miri run
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
              f"input_ub={count('input-ub')} allocator={count('allocator')} known_allocator={count('known-allocator')} "
              f"known_one_element={count('known-one-element')} run={'C' if pass_c else 'B' if pass_b else 'A'} unresolved_sites={len({u for r in rows for u in r[6]})} "
              f"unsupported={count('unsupported')} other={count('other') + count('timeout')} wall={t_all:.0f} "
              f"unsupported_names={','.join(f'{k}:{v}' for k, v in names.items()) or '-'} coverage={cov}", flush=True)


if __name__ == "__main__":
    main(sys.argv)
