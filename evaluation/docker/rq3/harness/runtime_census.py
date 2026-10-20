#!/usr/bin/env python3
"""The native runs: run the emitted
programs on the benchmark inputs, beside the C original and the untransformed
substrate, and classify every Rust panic.

usage: runtime_census.py <census-dir> <work-dir> [--programs p,q] [--extent N]
prints one receipt per program:
  runtime program=<p> inputs=<n> panics=<k> fabricated_extent_panics=<f>
  other_panics=<o> (fabricated_extent_panics: a bounds panic whose len IS the tree's fabricated extent N, explained) differential_mismatches=<m> N=<extent: --extent, else the tree's own const, '-' if none> c_baseline=<built|absent>
  substrate_mismatches=<s> substrate_differs_from_c=<d> unwrap_none=<e9> overflow=<v> ub_precondition=<u>
  abi_changed_drivers=<a> frame=<analysis_frame> code_frame=<sha>
and writes <work-dir>/<p>/runs.tsv (one row per input and variant).

Three variants per input: `c` (the C original, gcc), `substrate`
(rs-crown-derived, untransformed) and `emitted` (the census's tree). Both Rust
variants are built identically: rustc nightly-2025-06-23, every deps_crate
rlib as an --extern, -C panic=abort, overflow checks and
debug assertions on, opt-level 1.

Driver kinds.
  main0   the tree keeps the C `main` as `main_0`; the harness makes TWO
          textual edits to a copy (the visibility of that `main_0`, and an
          appended `fn main` building argv in the tree's own argv type).
  cdriver a C driver (the program's own test / sample / example, or a harness
          transcription of a commented-out main) linked to the library built
          as a staticlib: the C sources for `c`, the tree for the others.
The two textual edits are written to <work-dir>/<p>/<variant>.shim.diff.

Panic kinds (the message the default hook prints before SIGABRT):
  bounds       index / range out of bounds; `fabricated-extent` when the panic
               moves or vanishes with FALLBACK_SLICE_EXTENT alone (--extent)
  unwrap-none  Option::unwrap / expect on None (e9)
  overflow     arithmetic overflow, division by zero
  ub-precondition  `unsafe precondition(s) violated` (counted as other)
  other        anything else
"""
import csv, difflib, functools, glob, os, re, shutil, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rust_scan import functions, owner_of, tokens  # noqa: E402

SRC = os.path.abspath(os.environ.get("SRC", os.getcwd()))                      # the translator's source root
RESULTS = os.path.abspath(os.environ.get("RESULTS", os.path.join(SRC, "results")))
CROWN = os.path.join(os.environ.get("THIRD_PARTY", os.path.join(RESULTS, "third-party")), "crown", "c-code")  # C originals (optional)
SUBSTRATE = os.path.abspath(os.environ.get("SUBSTRATE", os.path.join(RESULTS, "substrate")))  # the prepared inputs
RS = os.path.join(SRC, "benchmarks", "rs")
BENCH = os.path.join(SRC, "benchmarks")
DEPS = os.path.join(SRC, "deps_crate", "target", "debug", "deps")
DRIVERS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "drivers")
TOOLCHAIN = "+nightly-2025-06-23"
RUST_FLAGS = ["-C", "panic=abort", "-C", "opt-level=1", "-C", "overflow-checks=on",
              "-C", "debug-assertions=on", "--cap-lints", "allow"]
CC = ["gcc", "-O1", "-w", "-fno-strict-aliasing"]


def run_pty(binary, keys, cwd, timeout):
    """A scripted terminal session: the keys are fed one by one with a pause;
    the screen bytes are kept, the exit status is what the differential reads."""
    import pty, select
    t0 = time.time()
    pid, fd = pty.fork()
    if pid == 0:
        os.chdir(cwd)
        os.environ["TERM"] = "vt100"
        os.execv(binary, [binary])
    screen = b""
    for k in keys:
        end = time.time() + 0.3
        while time.time() < end:
            r, _, _ = select.select([fd], [], [], 0.05)
            if r:
                try:
                    screen += os.read(fd, 65536)
                except OSError:
                    break
        try:
            os.write(fd, k.encode())
        except OSError:
            break
    deadline = t0 + timeout
    status = None
    while time.time() < deadline:
        r, _, _ = select.select([fd], [], [], 0.1)
        if r:
            try:
                screen += os.read(fd, 65536)
            except OSError:
                pass
        done, st = os.waitpid(pid, os.WNOHANG)
        if done:
            status = st
            break
    if status is None:
        os.kill(pid, 9)
        os.waitpid(pid, 0)
        return "timeout", b"", screen, time.time() - t0
    code = os.waitstatus_to_exitcode(status)
    # the screen is random (srand(time)); only the exit status is compared
    return code, b"", screen, time.time() - t0


def run_cmd(cmd, cwd=None, stdin=None, timeout=600, env=None):
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=cwd, stdin=stdin, capture_output=True, timeout=timeout, env=env)
        return p.returncode, p.stdout, p.stderr, time.time() - t0
    except subprocess.TimeoutExpired as e:
        return "timeout", e.stdout or b"", e.stderr or b"", time.time() - t0


def externs():
    out = []
    for rlib in sorted(glob.glob(os.path.join(DEPS, "lib*.rlib"))):
        name = os.path.basename(rlib)[3:].rsplit("-", 1)[0]
        out += ["--extern", f"{name}={rlib}"]
    return out


def rustc(root, out, crate_type, log, link_args=()):
    cmd = ["rustc", TOOLCHAIN, "--edition", "2021", "--crate-type", crate_type,
           "--crate-name", re.sub(r"\W", "_", os.path.basename(out).split(".")[0].removeprefix("lib")),
           *RUST_FLAGS, *[f"-Clink-arg={a}" for a in link_args], "-L", f"dependency={DEPS}", *externs(), root, "-o", out]
    code, so, se, _ = run_cmd(cmd, timeout=3600)
    open(log, "wb").write(se)
    return code == 0


def crate_root(d):
    return next((os.path.join(d, f) for f in ("lib.rs", "c2rust-lib.rs") if os.path.exists(os.path.join(d, f))), None)


def tree_extent(d):
    """The emitted tree's own `FALLBACK_SLICE_EXTENT` (a build may override it), or None where the tree declares none."""
    for f in sorted(glob.glob(os.path.join(d, "**", "*.rs"), recursive=True)):
        m = re.search(r"const FALLBACK_SLICE_EXTENT: usize = (\d+);", open(f, encoding="utf-8", errors="replace").read())
        if m:
            return int(m.group(1))
    return None


def main0_line(text, module):
    """Line index (0-based) of `fn main_0` inside the `pub mod` path `module`."""
    toks = list(tokens(text))
    stack, depth, pending = [], 0, None
    for k, (kind, v, off) in enumerate(toks):
        if kind == "ident" and v == "mod" and k + 2 < len(toks) and toks[k + 2][1] == "{":
            pending = toks[k + 1][1]
        elif kind == "punct" and v == "{":
            depth += 1
            if pending:
                stack.append((pending, depth))
                pending = None
        elif kind == "punct" and v == "}":
            if stack and stack[-1][1] == depth:
                stack.pop()
            depth -= 1
        elif kind == "ident" and v == "main_0" and toks[k - 1][1] == "fn":
            if "::".join(s for s, _ in stack) == module:
                return text.count("\n", 0, off), text[off:text.index("{", off)]
    raise ValueError(f"no main_0 in {module}")


def shim(text, module, extent=None):
    """The two textual edits (main_0 made reachable, a `fn main` appended) plus the extent rewrite for a sweep."""
    lines = text.split("\n")
    idx, sig = main0_line(text, module)
    lines[idx] = re.sub(r"^(\s*)unsafe fn main_0", r"\1pub(crate) unsafe fn main_0", lines[idx])
    params = sig[sig.index("(") + 1: sig.rindex(")")].strip()
    if not params:
        call = "main_0()"
    else:
        argv_ty = params.split(",", 1)[1].split(":", 1)[1].strip()
        if argv_ty.startswith("&["):
            argv = "&argv[..]"
        elif argv_ty.startswith("&"):
            argv = "&argv[0]"
        elif "*const" in argv_ty:
            argv = "argv.as_mut_ptr() as *mut *const _"
        else:
            argv = "argv.as_mut_ptr() as *mut *mut _"
        call = f"main_0(argc as _, {argv})"
    out = "\n".join(lines)
    if extent:
        out = re.sub(r"const FALLBACK_SLICE_EXTENT: usize = \d+;", f"const FALLBACK_SLICE_EXTENT: usize = {extent};", out)
    out += f"""
// the native runner's driver (harness, not the emitted program)
fn main() {{
    let args: Vec<std::ffi::CString> =
        std::env::args().map(|a| std::ffi::CString::new(a).unwrap()).collect();
    let mut argv: Vec<*mut std::ffi::c_char> =
        args.iter().map(|a| a.as_ptr() as *mut std::ffi::c_char).collect();
    argv.push(core::ptr::null_mut());
    let argc = args.len();
    let _ = (&mut argv, argc);
    unsafe {{ ::std::process::exit(crate::{module}::{call} as i32) }}
}}
"""
    return out


# Harness-side platform models: C-library entry points the
# translation references that this platform's libc lacks. They model the C
# library, never the program.
PLATFORM_SHIMS = {
    "macos_ctype": """
// harness platform model: macOS ctype (`_DefaultRuneLocale.__runetype`, `__maskrune`) for a
// translation made on macOS (bzip2). Only `__runetype` (byte offset 60) is read by the tree.
#[repr(C)]
pub struct JobcratRuneLocaleModel { head: [u8; 60], runetype: [u32; 256], rest: [u8; 8192] }
const fn jobcrat_macos_runetype() -> [u32; 256] {
    let mut t = [0u32; 256];
    let mut c = 0usize;
    while c < 128 {
        let b = c as u8;
        let mut m = 0u32;
        let upper = b >= b'A' && b <= b'Z';
        let lower = b >= b'a' && b <= b'z';
        let digit = b >= b'0' && b <= b'9';
        let space = b == b' ' || (b >= 9 && b <= 13);
        let print = b >= 0x20 && b < 0x7f;
        let graph = b > 0x20 && b < 0x7f;
        if upper || lower { m |= 0x100 }          // _CTYPE_A
        if b < 0x20 || b == 0x7f { m |= 0x200 }   // _CTYPE_C
        if digit { m |= 0x400 }                   // _CTYPE_D
        if graph { m |= 0x800 }                   // _CTYPE_G
        if lower { m |= 0x1000 }                  // _CTYPE_L
        if graph && !(upper || lower || digit) { m |= 0x2000 } // _CTYPE_P
        if space { m |= 0x4000 }                  // _CTYPE_S
        if upper { m |= 0x8000 }                  // _CTYPE_U
        if digit || (b >= b'a' && b <= b'f') || (b >= b'A' && b <= b'F') { m |= 0x10000 } // _CTYPE_X
        if b == b' ' || b == 9 { m |= 0x20000 } // _CTYPE_B
        if print { m |= 0x40000 }                 // _CTYPE_R
        t[c] = m;
        c += 1;
    }
    t
}
#[no_mangle]
pub static mut _DefaultRuneLocale: JobcratRuneLocaleModel =
    JobcratRuneLocaleModel { head: [0; 60], runetype: jobcrat_macos_runetype(), rest: [0; 8192] };
#[no_mangle]
pub unsafe extern "C" fn __maskrune(c: std::ffi::c_int, mask: std::ffi::c_ulong) -> std::ffi::c_int {
    if (0..256).contains(&c) { (jobcrat_macos_runetype()[c as usize] as std::ffi::c_ulong & mask) as std::ffi::c_int } else { 0 }
}
// harness platform model: macOS stdio pointers and errno, bound to glibc's at startup
extern "C" {
    #[link_name = "stdin"] static mut jobcrat_glibc_stdin: *mut std::ffi::c_void;
    #[link_name = "stdout"] static mut jobcrat_glibc_stdout: *mut std::ffi::c_void;
    #[link_name = "stderr"] static mut jobcrat_glibc_stderr: *mut std::ffi::c_void;
    #[link_name = "__errno_location"] fn jobcrat_glibc_errno() -> *mut std::ffi::c_int;
}
#[no_mangle] pub static mut __stdinp: *mut std::ffi::c_void = core::ptr::null_mut();
#[no_mangle] pub static mut __stdoutp: *mut std::ffi::c_void = core::ptr::null_mut();
#[no_mangle] pub static mut __stderrp: *mut std::ffi::c_void = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn __error() -> *mut std::ffi::c_int { jobcrat_glibc_errno() }
#[used]
#[link_section = ".init_array"]
static JOBCRAT_MACOS_STDIO_INIT: unsafe extern "C" fn() = {
    unsafe extern "C" fn init() { __stdinp = jobcrat_glibc_stdin; __stdoutp = jobcrat_glibc_stdout; __stderrp = jobcrat_glibc_stderr; }
    init
};
""",
    # macOS's assert-failure entry (tulipindicators was translated on macOS)
    "assert_rtn": """
// harness platform model: macOS `__assert_rtn` (the assert macro's failure path), as the C library would
#[no_mangle]
pub unsafe extern "C" fn __assert_rtn(func: *const std::ffi::c_char, file: *const std::ffi::c_char,
                                      line: std::ffi::c_int, expr: *const std::ffi::c_char) -> ! {
    let s = |p: *const std::ffi::c_char| if p.is_null() { String::new() } else { std::ffi::CStr::from_ptr(p).to_string_lossy().into_owned() };
    eprintln!("Assertion failed: ({}), function {}, file {}, line {}.", s(expr), s(func), s(file), line);
    std::process::abort()
}
""",
}


# --- per-program configuration -------------------------------------------------
# runs: (input_id, driver, argv list, stdin file or None, output files to compare)
def P(**kw):
    return kw


PROGRAMS = {
    "avl": P(kind="cdriver", c_lib=["avl.c"], c_dir="avl", drivers={"main": "avl/driver.c"},
             runs=[("main", "main", [], None, [])]),
    "bst": P(kind="cdriver", c_lib=["bst.c"], c_dir="bst", drivers={"main": "bst/driver.c"},
             runs=[("main", "main", [], None, [])]),
    # upstream: `$(CC) -g -Wall -DDEBUG -o test/test_binn test/test_binn.c test/test_binn2.c src/binn.c`
    "binn": P(kind="cdriver", c_lib=["src/binn.c"], c_dir="binn-3.0", c_inc=["src"],
              cflags=["-std=gnu99", "-Wno-error=implicit-function-declaration"],
              drivers={"test_binn": ["@test/test_binn.c", "@test/test_binn2.c", "binn/internals.c"]},
              runs=[("test_binn", "test_binn", [], None, [])]),
    "buffer": P(kind="main0", c_dir="buffer-0.4.0", mains={"test": ("src::test", ["test.c", "buffer.c"])},
                runs=[("test", "test", [], None, [])]),
    "rgba": P(kind="main0", c_dir="rgba", c_inc=["src"], mains={"test": ("src::test", ["test.c", "src/rgba.c"])},
              runs=[("test", "test", [], None, [])]),
    "urlparser": P(kind="main0", c_dir="urlparser", mains={"test": ("src::test", ["test.c"])},
                   runs=[("test", "test", [], None, [])]),
    "quadtree": P(kind="main0", c_dir="quadtree-0.1.0", c_inc=["src"],
                  mains={"test": ("src::test", ["test.c", "src/bounds.c", "src/node.c", "src/point.c", "src/quadtree.c"])},
                  runs=[("test", "test", [], None, [])]),
    "genann": P(kind="main0", c_dir="genann-1.0.0/c",
                mains={m: (f"src::{m}", [f"{m}.c", "genann.c"]) for m in ("test", "example1", "example2", "example3", "example4")},
                setup=["example"],
                runs=[(m, m, [], None, []) for m in ("test", "example1", "example2", "example3", "example4")]),
    "ht": P(kind="cdriver", c_lib=["ht.c"], c_dir="ht",
            drivers={"demo": "@samples/demo.c", "dump": "@samples/dump.c", "stats": "@samples/stats.c"},
            runs=[("demo", "demo", [], f"{DRIVERS}/ht/demo.stdin", []), ("dump", "dump", [], None, []),
                  ("stats-words", "stats", [], f"{CROWN}/ht/samples/words.txt", [])]),
    "libcsv": P(kind="cdriver", c_lib=["libcsv.c"], c_dir="libcsv", drivers={"test_csv": "@test_csv.c"},
                runs=[("test_csv", "test_csv", [], None, [])]),
    "lodepng": P(kind="cdriver", c_lib=["lodepng.c"], c_dir="lodepng",
                 drivers={"encode": "@examples/example_encode.c", "decode": "@examples/example_decode.c"},
                 runs=[("encode", "encode", ["test.png"], None, ["test.png"]),
                       ("decode", "decode", ["in.png"], "@stage:encode/test.png:in.png", [])]),
    "bzip2": P(kind="main0", c_dir="bzip2", platform_shims=["macos_ctype"],
               mains={"bzip2": ("bzip2", ["bzip2.c", "blocksort.c", "huffman.c", "crctable.c", "randtable.c",
                                           "compress.c", "decompress.c", "bzlib.c"])},
               runs=[(f"compress-{n}", "bzip2", [f"-{n}"], f"{BENCH}/script-tests/bzip2/sample{n}.ref", []) for n in (1, 2, 3)]
                    + [("decompress-1", "bzip2", ["-d"], f"{BENCH}/script-tests/bzip2/sample1.bz2", []),
                       ("decompress-2", "bzip2", ["-d"], f"{BENCH}/script-tests/bzip2/sample2.bz2", []),
                       ("decompress-3", "bzip2", ["-ds"], f"{BENCH}/script-tests/bzip2/sample3.bz2", [])]),
    "brotli": P(kind="main0", c_dir="brotli-1.0.9", c_inc=["c/include"], timeout=900,
                mains={"brotli": ("src::tools::brotli",
                                  [os.path.relpath(f, f"{CROWN}/brotli-1.0.9") for d in ("common", "dec", "enc", "tools")
                                   for f in sorted(glob.glob(f"{CROWN}/brotli-1.0.9/c/{d}/*.c"))])},
                setup_abs=[f"{CROWN}/brotli-1.0.9/c/enc/encode.c", f"{CROWN}/brotli-1.0.9/c/common/dictionary.h",
                           f"{CROWN}/brotli-1.0.9/c/dec/decode.c"],
                # the repo's roundtrip test (q 1/6/9/11) plus q10 compress / stream (known defect (a) shows on q10)
                runs=[r for f in ("encode.c", "dictionary.h", "decode.c") for q in (1, 6, 9, 11) for r in (
                    (f"{f}-q{q}-compress", "brotli", ["-fq", str(q), f, "-o", "out.br"], None, ["out.br"]),
                    (f"{f}-q{q}-decompress", "brotli", ["-fd", "in.br", "-o", "out"], f"@stage:{f}-q{q}-compress/out.br:in.br", ["out"]),
                    (f"{f}-q{q}-stream", "brotli", ["-cq", str(q)], f, []))]
                     + [r for f in ("encode.c", "dictionary.h", "decode.c") for r in (
                    (f"{f}-q10-compress", "brotli", ["-fq", "10", f, "-o", "out.br"], None, ["out.br"]),
                    (f"{f}-q10-stream", "brotli", ["-cq", "10"], f, []))]),
    "libtree": P(kind="main0", c_dir="libtree-3.1.1/c", mains={"libtree": ("src::libtree", ["libtree.c"])},
                 setup_abs=[f"{BENCH}/crown/libtree/tests"],
                 runs=[("bin-ls", "libtree", ["/bin/ls"], None, [])]
                      + [(f"test-{os.path.basename(d)}", "libtree", ["@sh", f"ln -sf \"$BIN\" libtree && make -s -C tests/{os.path.basename(d)} check"], None, [])
                         for d in sorted(glob.glob(f"{BENCH}/crown/libtree/tests/[0-9]*"))]),
    "tulipindicators": P(kind="main0", c_dir=None, timeout=900, platform_shims=["assert_rtn"],
                         mains={m: (m, None) for m in ("example1", "example2", "smoke", "fuzzer", "sample")},
                         setup_abs=[f"{RS}/tulipindicators/tests"],
                         runs=[("example1", "example1", [], None, []), ("example2", "example2", [], None, []),
                               ("smoke", "smoke", [], None, []), ("fuzzer", "fuzzer", [], None, []),
                               ("sample-ma-5", "sample", ["ma", "5"], None, []),
                               ("sample-version", "sample", ["--version"], None, []),
                               ("sample-list", "sample", ["--list"], None, [])]),
    # heman: the two tests whose calls keep the C ABI (test_heman / test_pts / test_planet
    # call functions the emitted tree delivers with fat signatures)
    "heman": P(kind="cdriver", c_dir="heman", c_inc=["include", "kazmath", "src", "test"], cflags=["-fopenmp"],
               c_lib=[os.path.relpath(f, f"{CROWN}/heman") for d in ("src", "kazmath")
                      for f in sorted(glob.glob(f"{CROWN}/heman/{d}/*.c"))],
               drivers={"test_sdf": "@test/test_sdf.c", "test_earth": "@test/test_earth.c"},
               setup=["test"], timeout=600,
               runs=[("test_sdf", "test_sdf", ["@sh", "mkdir -p build && \"$BIN\""], None, ["build/sdfresult.png"]),
                     ("test_earth", "test_earth", ["@sh", "mkdir -p build && \"$BIN\""], None,
                      ["build/colorized.png", "build/litearth.png", "build/masked.png", "build/sweep.png"])]),
    # ncurses: the runtime library is present, the headers are not (no C baseline); pty, exit status only
    "robotfindskitten": P(kind="main0", c_dir=None, link_args=["-l:libncurses.so.6", "-l:libtinfo.so.6"], timeout=60,
                          mains={"rfk": ("src::robotfindskitten", None)},
                          runs=[("pty-session", "rfk", ["@pty", " hhhjjjlllkkkyubn q"], None, [])]),
    "lil": P(kind="main0", c_dir="lil", mains={"lil": ("src::main", ["main.c", "lil.c"])},
             setup=["*.lil"],
             runs=[(os.path.basename(f)[:-4], "lil", [os.path.basename(f)], None, [])
                   for f in sorted(glob.glob(f"{CROWN}/lil/*.lil"))]),
}


def c_build(cfg, driver_src, out, log):
    base = os.path.join(CROWN, cfg["c_dir"])
    inc = [f"-I{os.path.join(base, i)}" for i in cfg.get("c_inc", [])] + [f"-I{base}"]
    srcs = [os.path.join(base, s) for s in driver_src]
    code, so, se, _ = run_cmd([*CC, *cfg.get("cflags", []), *inc, *srcs, "-o", out, "-lm", "-lpthread", "-ldl"], timeout=1200)
    open(log, "wb").write(se)
    return code == 0


# Rust drivers generated from the tree under test at build time (not committed). Empty: libzahl's,
# the only one, was dropped (its test is a client outside the program).
GENERATED_DRIVERS = set()


def prepare_driver(program, tree):
    if program in GENERATED_DRIVERS:
        subprocess.run([sys.executable, os.path.join(DRIVERS, program, "make_rs.py"), tree], check=True,
                       stdout=subprocess.DEVNULL)


def rust_driver(program, drv):
    """A Rust driver transcribed from the program's own C test:
    drivers/<program>/<driver>.driver.rs, appended to the emitted crate, calling the
    emitted API as the tree declares it. None where the program has none."""
    p = os.path.join(DRIVERS, program, f"{drv}.driver.rs")
    return p if os.path.exists(p) else None


def driver_paths(cfg, spec):
    """A driver is one source or a list; `@x` is relative to the C repo, else to drivers/."""
    specs = spec if isinstance(spec, list) else [spec]
    return [os.path.join(CROWN, cfg["c_dir"], x[1:]) if x.startswith("@") else os.path.join(DRIVERS, x) for x in specs]


def build(program, cfg, census, work, extent=None):
    """-> {variant: {driver: binary path or None}}"""
    bins = {"c": {}, "substrate": {}, "emitted": {}}
    trees = {"substrate": os.path.join(SUBSTRATE, program), "emitted": os.path.join(census, "emitted-trees", program)}
    os.makedirs(work, exist_ok=True)
    if cfg["kind"] == "main0":
        for drv, (module, csrcs) in cfg["mains"].items():
            out = os.path.join(work, f"c-{drv}")
            bins["c"][drv] = (out if c_build(cfg, csrcs, out, out + ".log") else None) if cfg["c_dir"] else "absent"
            for var, tree in trees.items():
                root = crate_root(tree)
                text = open(root, encoding="utf-8", errors="replace").read()
                shimmed = shim(text, module, extent if var == "emitted" else None)
                shimmed += "".join(PLATFORM_SHIMS[n] for n in cfg.get("platform_shims", []))
                src = os.path.join(work, f"{var}-{drv}.rs")
                open(src, "w").write(shimmed)
                with open(os.path.join(work, f"{var}-{drv}.shim.diff"), "w") as d:
                    d.writelines(difflib.unified_diff(text.splitlines(True), shimmed.splitlines(True), root, src, n=0))
                out = os.path.join(work, f"{var}-{drv}")
                bins[var][drv] = out if rustc(src, out, "bin", out + ".log", cfg.get("link_args", ())) else None
    else:
        libs = {}
        for var, tree in trees.items():
            root = crate_root(tree)
            src = root
            if extent and var == "emitted":
                text = open(root, encoding="utf-8", errors="replace").read()
                src = os.path.join(work, f"{var}-lib.rs")
                open(src, "w").write(re.sub(r"const FALLBACK_SLICE_EXTENT: usize = \d+;",
                                            f"const FALLBACK_SLICE_EXTENT: usize = {extent};", text))
            out = os.path.join(work, f"lib{var}.a")
            libs[var] = out if rustc(src, out, "staticlib", out + ".log") else None
        base = os.path.join(CROWN, cfg["c_dir"])
        inc = [f"-I{os.path.join(base, i)}" for i in cfg.get("c_inc", [])] + [f"-I{base}"]
        for drv, spec in cfg["drivers"].items():
            dsrc = driver_paths(cfg, spec)
            out = os.path.join(work, f"c-{drv}")
            code, so, se, _ = run_cmd([*CC, *cfg.get("cflags", []), *inc, *dsrc, *[os.path.join(base, s) for s in cfg["c_lib"]],
                                       "-o", out, "-lm", "-lpthread", "-ldl"], timeout=1200)
            open(out + ".log", "wb").write(se)
            bins["c"][drv] = out if code == 0 else None
            for var in ("substrate", "emitted"):
                out = os.path.join(work, f"{var}-{drv}")
                rsd = rust_driver(program, drv)
                if var == "emitted" and rsd:
                    prepare_driver(program, trees[var])
                    # the emitted crate + its Rust driver, one binary: no C caller, so no ABI question
                    text = open(crate_root(trees[var]), encoding="utf-8", errors="replace").read()
                    if extent:
                        text = re.sub(r"const FALLBACK_SLICE_EXTENT: usize = \d+;",
                                      f"const FALLBACK_SLICE_EXTENT: usize = {extent};", text)
                    src = os.path.join(work, f"{var}-{drv}.rs")
                    open(src, "w").write(text + "\n" + open(rsd).read().replace("@DRIVERS@", DRIVERS)
                                         + "".join(PLATFORM_SHIMS[n] for n in cfg.get("platform_shims", [])))
                    bins[var][drv] = out if rustc(src, out, "bin", out + ".log", cfg.get("link_args", ())) else None
                    continue
                changed = abi_changed(cfg, spec, crate_root(trees[var]))
                if changed:
                    bins[var][drv] = ("abi-changed", changed)
                    continue
                if not libs[var]:
                    bins[var][drv] = None
                    continue
                code, so, se, _ = run_cmd([*CC, *cfg.get("cflags", []), *inc, *dsrc, libs[var], "-o", out, "-lm", "-lpthread", "-ldl"], timeout=1200)
                open(out + ".log", "wb").write(se)
                bins[var][drv] = out if code == 0 else None
    return bins


FAT = re.compile(r"&\s*(?:'\w+\s+)?(?:mut\s+)?\[|Box<\[|SliceCursor|&str\b")


def fat_exports(root):
    """Exported `extern "C"` functions whose signature no longer matches the C
    prototype (a fat pointer where C passes one word)."""
    t = open(root, encoding="utf-8", errors="replace").read()
    out = set()
    for m in re.finditer(r'#\[no_mangle\]\s*pub (?:unsafe )?extern "C" fn (\w+)(<[^>]*>)?\s*\((.*?)\)\s*(->\s*[^{]+?)?\s*\{', t, re.S):
        if FAT.search(m.group(0)):
            out.add(m.group(1))
    return out


def abi_changed(cfg, spec, tree_root):
    """The library functions a C driver calls whose emitted ABI changed."""
    fat = fat_exports(tree_root)
    called = set()
    seen, todo = set(), list(driver_paths(cfg, spec))
    local = {os.path.dirname(p) for p in todo}
    while todo:  # the driver and the headers it includes from its own directory (not the library's)
        src = todo.pop()
        if src in seen or not os.path.exists(src):
            continue
        seen.add(src)
        t = open(src, encoding="utf-8", errors="replace").read()
        called |= {f for f in fat if re.search(r"\b" + f + r"\s*\(", t)}
        for inc in re.findall(r'#\s*include\s*"([^"]+)"', t):
            cand = os.path.normpath(os.path.join(os.path.dirname(src), inc))
            if os.path.exists(cand) and os.path.dirname(cand) in local:
                todo.append(cand)
    return sorted(called)


ADDR = re.compile(rb"0x[0-9a-f]{6,16}")


# Per-input timing masks: an input that prints its own elapsed time.
TIMING = {("genann", "test"): re.compile(rb"\b\d+ms\b")}


def norm(b, rundir=None, key=None):
    """The declared output masks: printed addresses (ASLR), the variant's own run directory,
    and the elapsed-time fields of the inputs in TIMING."""
    if rundir:
        b = b.replace(rundir.encode(), b"<RUNDIR>")
    if key in TIMING:
        b = TIMING[key].sub(b"<MS>ms", b)
    return ADDR.sub(b"0xADDR", b)


@functools.lru_cache(maxsize=8)
def _index(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    toks = list(tokens(text))
    offs = [0]
    for ln in text.split("\n"):
        offs.append(offs[-1] + len(ln) + 1)
    return toks, functions(toks), offs


def _first_at(toks, target):
    lo, hi = 0, len(toks) - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if toks[mid][2] < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


# Known runtime defects of earlier emitted trees. A hit is
# `known-defect:<id>` and kept apart from new findings, whatever its message says.
KNOWN = [
    # (a) the dist_cache one-element adapters (quality 10): `from_mut` into
    # BrotliZopfliCreateCommands, `from_ref` into ComputeDistanceCache (which
    # re-slices [1..] and reads again, so it reports length 0 or 1)
    ("a", "brotli", ("BrotliZopfliCreateCommands", "ComputeDistanceCache"), r"length [01]\b|len is [01]\b", "q10"),
    # (b) an empty-slice Zopfli root at quality 11
    ("b", "brotli", ("ComputeDistanceCache",), r"length 0\b|len is 0\b", "q11"),
    ("c", "lodepng", ("lodepng_chunk_length", "lodepng_read32bitInt"), r".", None),
    ("d", "bzip2", ("copyFileName",), r"len is 1024 but the index is 1024", None),
    # one-element adapters: a one-element `from_ref` / `from_mut` into a callee that reads on
    # (later trees hold them raw); a hit is known, not new.
    ("one-element:Hash14", "brotli", ("Hash14",), r"length 1\b|len is 1\b", None),
    ("one-element:DecodeSymbol", "brotli", ("DecodeSymbol",), r"length 1\b|len is 1\b", None),
    ("one-element:ReplicateValue", "brotli", ("ReplicateValue",), r"length 1\b|len is 1\b", None),
    # FindAllMatchesH10's one-element ringbuffer, from BrotliZopfliComputeShortestPath (q10)
    # and BrotliCreateHqZopfliBackwardReferences (q11); the read is HashBytesH10's
    ("one-element:HashBytesH10", "brotli", ("HashBytesH10",), r"length 1\b|len is 1\b", None),
    ("one-element:AddMatch", "brotli", ("AddMatch",), r"length 1\b|len is 1\b", None),
    ("one-element:mainGtU", "bzip2", ("mainGtU",), r"length 1\b|len is 1\b", None),
    # a wrong-evidence extent, the loop INDEX
    # `(i) as usize` taken as the slice length at lodepng_convert's call, read at in[i*4 + k] by
    # getPixelColorRGBA8::in_0#5; reached by lodepng's transcribed driver
    ("wrong-evidence-extent", "lodepng", ("getPixelColorRGBA8",), r"len is 0\b|length 0\b", None),
]


# Mismatches against C that are explained, not jobcrat's: the input's own UB,
# and seeded / translation-level rows where the substrate does the same.
EXPLAINED = {
    ("urlparser", "test"): "input UB: url.h get_part sscanf heap overflow (ASan)",
    ("genann", "example1"): "time-seeded (srand(time(0)))",
    ("genann", "example2"): "translation-level: both Rust variants never converge",
}


# Panics on inputs whose own operation is the UB, kept apart from the count:
# tulip's fuzzer reads input[-1] in ti_dpo at period 1.
EXPLAINED_PANICS = {
    ("tulipindicators", "fuzzer"): "input UB: ti_dpo reads input[period-1-back] = input[-1] at period 1",
}


# Non-panic crashes of the emitted program that are known defects: binn's provided
# test passes INVALID_BINN (NULL) to binn_list_add / binn_map_set / binn_object_set, whose
# emitted formal is a non-Option `&mut binn` handed on as `Some(x)` to a NULL-testing callee;
# the emitted run dies of SIGSEGV (an earlier tree's defect, fixed in later trees).
KNOWN_CRASHES = {
    ("binn", "test_binn"): ("exported-null-into-ref", -11),
}


# The substrate rule: a non-bounds panic class the derived substrate
# reproduces leaves the panic count as the input's ONLY where the c2rust input (`benchmarks/rs-crown`,
# what the pipeline is given) reproduces it on that input, or where the substrate equals C on it. The
# derived substrate alone is our own passes' output, not an oracle. The c2rust reproductions, each by
# its evidence (the harness does not build rs-crown itself):
C2RUST_REPRODUCES = {
    # native builds of rs-crown (flattened) needed the same unaligned-read repair rows
    # (BrotliUnalignedRead32 / 64) as the derived substrate's.
    ("brotli", r"(encode\.c|dictionary\.h|decode\.c)-q1-(compress|stream)"):
        "c2rust: misaligned BrotliUnaligned{Read,Write}64 (a native rs-crown build)",
}


def c2rust_reproduces(program, input_id):
    for (prog, pat), why in C2RUST_REPRODUCES.items():
        if prog == program and re.fullmatch(pat, input_id):
            return why
    return None


def panic_class(k):
    """The class of a classified panic, for the substrate-reproduces rule: the kind
    and the message with every number and address written `#` (`misaligned pointer dereference:
    address must be a multiple of 0x# but is 0x#`, `unsafe precondition(s) violated: ..`)."""
    return (k[0], re.sub(r"0x[0-9a-f]+|\d+", "#", k[3]).strip())


def known_defect(program, fn, msg, input_id=""):
    for kid, prog, fns, pat, quality in KNOWN:
        if program == prog and fn in fns and re.search(pat, msg) and (quality is None or f"-{quality}-" in input_id):
            return kid
    return None


PANIC = re.compile(rb"panicked at ([^:\n]+):(\d+):(\d+):\n(.*)")


def classify(stderr):
    m = PANIC.search(stderr)
    if not m:
        return None
    path, line, msg = m.group(1).decode(), int(m.group(2)), m.group(4).decode(errors="replace")
    if "unsafe precondition" in msg:
        kind = "ub-precondition"
    elif re.search(r"index out of bounds|out of range for slice|slice index starts at", msg):
        kind = "bounds"
    elif re.search(r"Option::unwrap\(\)|on a `None` value|non-null", msg):
        kind = "unwrap-none"
    elif re.search(r"with overflow|divide by zero|remainder with a divisor of zero", msg):
        kind = "overflow"
    else:
        kind = "other"
    fn = "-"
    if os.path.exists(path):
        toks, funcs, offs = _index(path)
        target = offs[line - 1]
        k = _first_at(toks, target)
        owner = owner_of(funcs, k)
        fn = owner[0] if owner else "-"
    return kind, f"{os.path.basename(path)}:{line}", fn, msg.strip()[:200]


def setup_dir(cfg, rundir):
    os.makedirs(rundir, exist_ok=True)
    for src in cfg.get("setup_abs", []):
        dst = os.path.join(rundir, os.path.basename(src))
        if os.path.isdir(src):
            shutil.copytree(src, dst, dirs_exist_ok=True)
        else:
            shutil.copy(src, dst)
    if not cfg["c_dir"]:
        return
    base = os.path.join(CROWN, cfg["c_dir"])
    for pat in cfg.get("setup", []):
        for src in glob.glob(os.path.join(base, pat)):
            dst = os.path.join(rundir, os.path.basename(src))
            if os.path.isdir(src):
                shutil.copytree(src, dst, dirs_exist_ok=True)
            else:
                shutil.copy(src, dst)


def run_program(program, cfg, census, work, extent=None):
    bins = build(program, cfg, census, work, extent)
    rows = []
    only = cfg.get("_only_inputs")
    for input_id, drv, argv, stdin, files in cfg["runs"]:
        if only and input_id not in only:
            continue
        res = {}
        for var in ("c", "substrate", "emitted"):
            b = bins[var].get(drv)
            rundir = os.path.join(work, "runs", input_id, var)
            if os.path.exists(rundir):
                shutil.rmtree(rundir)
            setup_dir(cfg, rundir)
            if b == "absent":
                res[var] = ("absent", b"", b"", 0.0, {})
                continue
            if isinstance(b, tuple):
                res[var] = ("abi-changed:" + ",".join(b[1]), b"", b"", 0.0, {})
                continue
            if not b:
                res[var] = ("build-failed", b"", b"", 0.0, {})
                continue
            fin = subprocess.DEVNULL
            if stdin and stdin.startswith("@stage:"):
                # the C variant's output of an earlier input, staged as this run's input file
                src, dst = stdin[len("@stage:"):].rsplit(":", 1)
                prior = os.path.join(work, "runs", src.split("/", 1)[0], "c", src.split("/", 1)[1])
                if not os.path.exists(prior):
                    prior = os.path.join(work, "runs", src.split("/", 1)[0], "substrate", src.split("/", 1)[1])
                shutil.copy(prior, os.path.join(rundir, dst))
            elif stdin:
                fin = open(stdin if os.path.isabs(stdin) else os.path.join(rundir, stdin), "rb")
            cmd = ["bash", "-c", argv[1]] if argv[:1] == ["@sh"] else [b, *argv]
            env = dict(os.environ, BIN=b)
            if argv[:1] == ["@pty"]:
                code, so, se, wall = run_pty(b, argv[1], rundir, cfg.get("timeout", 120))
            else:
                code, so, se, wall = run_cmd(cmd, cwd=rundir, stdin=fin, timeout=cfg.get("timeout", 120), env=env)
            outs = {f: open(os.path.join(rundir, f), "rb").read() if os.path.exists(os.path.join(rundir, f)) else None for f in files}
            open(os.path.join(rundir, "stdout"), "wb").write(so)
            open(os.path.join(rundir, "stderr"), "wb").write(se)
            res[var] = (code, norm(so, rundir, (program, input_id)), se, wall, outs)
        rows.append((input_id, res))
    return rows


def main(argv):
    census, work = argv[1], argv[2]
    only = set(argv[argv.index("--programs") + 1].split(",")) if "--programs" in argv else None
    extent = int(argv[argv.index("--extent") + 1]) if "--extent" in argv else None
    inputs = set(argv[argv.index("--inputs") + 1].split(",")) if "--inputs" in argv else None
    if "--no-ub-checks" in argv:
        # second configuration: the debug-assertion precondition
        # checks (alignment, from_raw_parts) off; bounds and overflow checks stay on
        RUST_FLAGS.extend(["-Zub-checks=no"])
    first = next(iter(glob.glob(os.path.join(census, "*.raw-boundary-subject-outcomes.tsv"))), None)
    frame = code = "-"
    if first:
        r = next(csv.DictReader(open(first), delimiter="\t"))
        frame, code = r["analysis_frame"], r["code_frame"][:9]
    for program, cfg in PROGRAMS.items():
        if only and program not in only:
            continue
        pw = os.path.join(work, program)
        if inputs:
            cfg = dict(cfg, _only_inputs=inputs)
        rows = run_program(program, cfg, census, pw, extent)
        panics = fabricated = other = mism = smism = e9 = ov = ub = abi = bfail = bounds = unexplained = input_ub_panics = 0
        known = {}
        reproduced, known_crash = [], 0
        substrate_only, sub_differs = [], 0
        n_eff = extent or tree_extent(os.path.join(census, "emitted-trees", program))

        def at_extent(k):
            """A bounds panic whose reported length IS the fabricated extent N: the
            fabricated-extent class by construction, wherever the site lies (the slice-length waiver)."""
            if not k or k[0] != "bounds" or not n_eff:
                return False
            m = re.search(r"the len is (\d+)|slice of length (\d+)", k[3])
            return bool(m) and int(m.group(1) or m.group(2)) == n_eff
        with open(os.path.join(pw, "runs.tsv"), "w") as t:
            t.write("input\tvariant\texit\twall_s\tpanic_kind\tsite\tfn\tmessage\tstdout_eq_c\tstdout_eq_substrate\tsubstrate_eq_c\n")
            for input_id, res in rows:
                c, s, e = res["c"], res["substrate"], res["emitted"]
                ran = lambda r: not (isinstance(r[0], str) and (r[0] in ("build-failed", "absent") or r[0].startswith("abi-changed")))
                # does the substrate equal C on this input? '-' where either did not run (no C baseline).
                sub_eq_c = (s[0] == c[0] and s[1] == c[1] and s[4] == c[4]) if ran(c) and ran(s) else None
                if sub_eq_c is False:
                    sub_differs += 1
                for var, r in res.items():
                    k = classify(r[2]) if var != "c" else None
                    if at_extent(k):
                        k = ("fabricated-extent",) + tuple(k[1:])
                    if k and known_defect(program, k[2], k[3], input_id):
                        k = ("known-defect:" + known_defect(program, k[2], k[3], input_id),) + tuple(k[1:])
                    eq_c = "-" if var == "c" else str(r[0] == c[0] and r[1] == c[1] and r[4] == c[4])
                    eq_s = "-" if var != "emitted" else str(r[0] == s[0] and r[1] == s[1] and r[4] == s[4])
                    t.write(f"{input_id}\t{var}\t{r[0]}\t{r[3]:.2f}\t" + ("\t".join(k) if k else "-\t-\t-\t-")
                            + f"\t{eq_c}\t{eq_s}\t{'-' if sub_eq_c is None else sub_eq_c}\n")
                k = classify(e[2])
                r481 = False
                if k and (program, input_id) in EXPLAINED_PANICS:
                    input_ub_panics += 1
                    k = None
                ks = classify(s[2]) if isinstance(s[2], bytes) else None
                repro = False
                c2rust = c2rust_reproduces(program, input_id)
                if k and ks and k[0] != "bounds" and panic_class(k) == panic_class(ks) and (sub_eq_c or c2rust):
                    # a panic class the substrate reproduces on the same
                    # input is the input's only where the c2rust input reproduces it too (or the
                    # substrate equals C there); listed with both sites and the c2rust evidence
                    input_ub_panics += 1
                    reproduced.append(f"{input_id}: {panic_class(k)[1]} (emitted {k[2]} {k[1]}; substrate {ks[2]} {ks[1]}; "
                                      f"{c2rust or 'substrate equals C'})")
                    k, repro = None, True
                elif k and ks and k[0] != "bounds" and panic_class(k) == panic_class(ks):
                    # the derived substrate alone reproduces it: counted, and listed as such
                    substrate_only.append(f"{input_id}: {panic_class(k)[1]} (emitted {k[2]} {k[1]}; substrate {ks[2]} {ks[1]}; "
                                          f"no c2rust evidence)")
                kc = KNOWN_CRASHES.get((program, input_id))
                if not k and kc and e[0] == kc[1]:
                    known_crash += 1
                if k and at_extent(k):
                    panics += 1
                    fabricated += 1
                    r481 = True
                elif k and known_defect(program, k[2], k[3], input_id):
                    panics += 1
                    kid = known_defect(program, k[2], k[3], input_id)
                    known[kid] = known.get(kid, 0) + 1
                elif k:
                    panics += 1
                    kind = k[0]
                    e9 += kind == "unwrap-none"
                    ov += kind == "overflow"
                    ub += kind == "ub-precondition"
                    other += kind in ("other", "ub-precondition")
                    bounds += kind == "bounds"
                ran = lambda r: not (isinstance(r[0], str) and (r[0] in ("build-failed", "absent") or r[0].startswith("abi-changed")))
                if e[0] == "build-failed" or s[0] == "build-failed":
                    bfail += 1
                if isinstance(e[0], str) and e[0].startswith("abi-changed"):
                    abi += 1
                    continue
                if ran(c) and ran(e) and not (e[0] == c[0] and e[1] == c[1] and e[4] == c[4]):
                    mism += 1
                    if (program, input_id) not in EXPLAINED and not r481 and not repro \
                            and not (kc and e[0] == kc[1]):
                        unexplained += 1
                if ran(s) and ran(e) and not (e[0] == s[0] and e[1] == s[1] and e[4] == s[4]):
                    smism += 1
        print(f"runtime program={program} inputs={len(rows)} panics={panics} fabricated_extent_panics={fabricated} "
              f"other_panics={other} bounds_unattributed={bounds} known_defect_panics={sum(known.values())}{'(' + ','.join(f'{k}:{v}' for k, v in sorted(known.items())) + ')' if known else ''} differential_mismatches={mism} N={extent or tree_extent(os.path.join(census, 'emitted-trees', program)) or '-'} "
              f"c_baseline={'absent' if not cfg['c_dir'] else ('built' if any(res['c'][0] != 'build-failed' for _, res in rows) else 'build-failed')} "
              f"substrate_mismatches={smism} substrate_differs_from_c={sub_differs} unwrap_none={e9} overflow={ov} ub_precondition={ub} "
              f"abi_changed_inputs={abi} build_failed_inputs={bfail} unexplained_mismatches={unexplained} input_ub_panics={input_ub_panics} "
              f"known_crashes={known_crash}{'(' + KNOWN_CRASHES[(program, 'test_binn')][0] + ')' if known_crash and program == 'binn' else ''} "
              f"landing={'pass' if panics == fabricated and known_crash == 0 and bfail == 0 and unexplained == 0 else 'fail'} frame={frame} code_frame={code}", flush=True)
        for line in reproduced:
            print(f"  input-ub (c2rust / substrate reproduces): {line}", flush=True)
        for line in substrate_only:
            print(f"  counted (the derived substrate alone reproduces it): {line}", flush=True)


if __name__ == "__main__":
    main(sys.argv)
