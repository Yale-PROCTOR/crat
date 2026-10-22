#!/usr/bin/env python3
"""six_suites.py <runtime-work-dir> [out.tsv] — the shipped test suites' verdicts.

The paper's test line is the six programs that SHIP a test suite (the same six as the Miri experiment):
libtree, rgba, quadtree, urlparser, genann, buffer. For each, the suite's OWN verdict on the emitted tree and, where
it builds, on the C original: the exit status the suite gives (its checks abort or fail the run). This reads the six
suites' rows out of the native runner's (`runtime_census.py`) work directory, so the suites run exactly once. Inputs authored by the harness (libtree's `/bin/ls`) are not
part of a suite and are not read.

A suite PASSES on a variant when every one of its runs exits 0. `stdout equals C` is printed beside it (the suites
print, and the harness compares), but the verdict is the suite's own.
"""
import csv, os, sys

SUITES = {  # program -> (what the shipped suite is, how it is run, the runs that make it up)
    "libtree": ("libtree-3.1.1/c/tests/: nine directories, each a Makefile `check` target that builds small ELF "
                "fixtures (rpath / runpath / $ORIGIN / symbol versions / 32-bit / nodeflib) and runs `libtree` on them; "
                "make fails on a nonzero exit",
                "per directory: `ln -sf <binary> libtree && make -s -C tests/<dir> check` (`make check`'s loop)",
                lambda inp: inp.startswith("test-")),
    "rgba": ("rgba/test.c: 20 assert() checks over rgba_from_string / rgba_to_string",
             "the test program built with the library; exit 0 = every assert held", lambda inp: inp == "test"),
    "quadtree": ("quadtree-0.1.0/test.c: 34 assert() checks over insert / search / walk / free",
                 "the test program built with the library", lambda inp: inp == "test"),
    "buffer": ("buffer-0.4.0/test.c: 36 assert() checks over the buffer API",
               "the test program built with the library", lambda inp: inp == "test"),
    "genann": ("genann-1.0.0/c/test.c: 9 lrun() cases (basic, xor, backprop, train and / or / xor, persist, copy, sigmoid), "
               "38 lok / lequal / lfequal checks; the examples (example1-4) are NOT the suite",
               "the test program built with the library; it prints its failure count and exits nonzero on any",
               lambda inp: inp == "test"),
    "urlparser": ("urlparser/test.c: 43 assert() checks over url_parse and the url_get_* accessors",
                  "the test program (header-only library)", lambda inp: inp == "test"),
}


NOTES = {  # what the verdict alone does not say
    "urlparser": "the C original aborts here: url.h's own 2-byte heap overflow (malloc(strlen(tmp_path)) then "
                 "sprintf(path, \"/%s\", tmp_path)) under this distro's gcc default _FORTIFY_SOURCE=3; unfortified it "
                 "exits 0. The emitted and substrate stdouts differ from C only in the garbage bytes of .query / .port",
}


def main(work, out=None):
    rows = []
    for program, (suite, how, pick) in SUITES.items():
        f = os.path.join(work, program, "runs.tsv")
        if not os.path.exists(f):
            rows.append((program, suite, how, "not run", "-", "-", "-"))
            continue
        by = {}
        for r in csv.DictReader(open(f), delimiter="\t"):
            if pick(r["input"]):
                by.setdefault(r["input"], {})[r["variant"]] = r
        runs = sorted(by)
        def verdict(variant):
            exits = [by[i].get(variant, {}).get("exit", "absent") for i in runs]
            if not runs or all(e in ("absent", "build-failed") for e in exits):
                return "not built" if any(e == "build-failed" for e in exits) else "absent"
            ok = sum(e == "0" for e in exits)
            return f"pass ({ok}/{len(runs)} exit 0)" if ok == len(runs) else f"FAIL ({ok}/{len(runs)} exit 0: " + \
                ", ".join(f"{i}={by[i].get(variant, {}).get('exit')}" for i in runs if by[i].get(variant, {}).get("exit") != "0") + ")"
        eq_c = sum(by[i].get("emitted", {}).get("stdout_eq_c") == "True" for i in runs)
        rows.append((program, suite, how, verdict("emitted"), verdict("c"), f"{eq_c}/{len(runs)}", ",".join(runs)))
    passed = sum(r[3].startswith("pass") for r in rows)
    print(f"six_suites: {passed}/6 pass on the emitted tree")
    for program, _, _, emitted, c, eq_c, _ in rows:
        print(f"  {program:10} emitted {emitted:40} C {c:40} stdout equals C {eq_c}"
              + (f"\n             note: {NOTES[program]}" if program in NOTES else ""))
    if out:
        with open(out, "w") as w:
            w.write("program\tshipped_suite\thow_run\temitted_verdict\tc_verdict\temitted_stdout_equals_c\truns\tnote\n")
            for r in rows:
                w.write("\t".join(r) + "\t" + NOTES.get(r[0], "-") + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None))
