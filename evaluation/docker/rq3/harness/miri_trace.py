#!/usr/bin/env python3
"""RQ4's prefix coverage (wave-6o relay 137 item 1): a function-entry trace on the Miri copy, a
harness edit (never the emitted program). Every function that holds a delivered declaration (the
census's realized rows, by owner_fn; its safe twin `__jobcrat_safe_<f>` too) starts with
`crate::jobcrat_cov_enter(K);`, which prints `jobcrat-cov-enter K` on its first entry. A run that stops
at a report has printed every such function it entered before the report."""
import csv, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from miri_oracle import mask  # noqa: E402
from pair_sites import module_spans  # noqa: E402

RUNTIME = r'''
// harness (wave-6o relay 137 item 1; NOT the emitted program): the function-entry trace
#[allow(static_mut_refs, dead_code)]
pub fn jobcrat_cov_enter(k: u32) {
    static mut SEEN: Vec<u32> = Vec::new();
    unsafe {
        if !SEEN.contains(&k) {
            SEEN.push(k);
            eprintln!("jobcrat-cov-enter {}", k);
        }
    }
}
'''


def owners(census, program):
    f = os.path.join(census, f"{program}.raw-boundary-subject-outcomes.tsv")
    return sorted({r["owner_fn"] for r in csv.DictReader(open(f), delimiter="\t")
                   if r["delivery"] == "realized-as-predicted" and r["emitted_form"] != "unchanged"})


def apply(body, census, program):
    """-> (body, [owner by K], receipt)"""
    own = owners(census, program)
    mk = mask(body)
    fns = module_spans(mk)
    edits = []
    for k, o in enumerate(own):
        parts = o.split("::")
        name, mods = parts[-1], tuple(parts[:-1])
        for (n, ms, s, e) in fns:
            if n in (name, "__jobcrat_safe_" + name) and (not mods or ms[-len(mods):] == mods):
                edits.append((s + 1, f" crate::jobcrat_cov_enter({k});"))
    edits.sort()
    out, i = [], 0
    for pos, ins in edits:
        out.append(body[i:pos]); out.append(ins); i = pos
    out.append(body[i:])
    return "".join(out) + RUNTIME, own, f"trace: {len(own)} functions with a delivered declaration, {len(edits)} bodies instrumented"


def entered(stderr_text):
    return {int(k) for k in re.findall(r"jobcrat-cov-enter (\d+)", stderr_text)}
