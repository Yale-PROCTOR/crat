#!/usr/bin/env python3
"""The input-repair pass (with the oracle extents: "pass D"): a run that stops at a report the INPUT itself has (class (a)) is repaired by one declared
edit, the same in the input and the output copy of the Miri project, and runs on. A harness edit,
never the emitted program; the analysis is not re-solved.

The edits are rows of `repairs.tsv` (keyed by expression, so that they carry over to a later frame):
  program  kind  fn  original  replacement  removes  why
  - kind: reference | uninitialised | input-defect
  - fn: the function the edit is scoped to (its safe twin `__jobcrat_safe_<fn>` too)
  - original / replacement: exact text (whitespace-normalised match), every occurrence in the scope
Rule 2: in the OUTPUT copy an edit applies only where the output's text at that site is
byte-equal to the input's; where the tool rewrote it the output is not edited, and the receipt says so.

apply(body, program, variant, repairs, substrate_body) -> (body, receipts)
"""
import csv, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from miri_oracle import mask  # noqa: E402
from pair_sites import module_spans  # noqa: E402

REPAIRS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "repairs.tsv")


def load(path=REPAIRS):
    if not os.path.exists(path):
        return []
    return [r for r in csv.DictReader((l for l in open(path) if not l.startswith("#")), delimiter="\t")]


def _norm(s):
    return re.sub(r"\s+", " ", s).strip()


def _find(text, fn, original):
    """[(start, end)] of `original` (whitespace-insensitive) inside fn's bodies (and its twin's)."""
    mk = mask(text)
    spans = [(0, len(text))] if fn == "*" else \
        [(s, e) for (n, _, s, e) in module_spans(mk) if n in (fn, "__jobcrat_safe_" + fn)]
    toks = [re.escape(t) for t in _norm(original).split(" ")]
    pat = re.compile(r"\s*".join(toks))
    out = []
    for s, e in spans:
        for m in pat.finditer(text, s, e):
            out.append((m.start(), m.end()))
    return out


RUNTIME = r'''
// harness (NOT the emitted program): the input-repair pass's helpers
pub trait JobcratRepairCstr { unsafe fn jobcrat_cstrlen(&self) -> usize; }
impl JobcratRepairCstr for *mut libc::c_char { unsafe fn jobcrat_cstrlen(&self) -> usize { libc::strlen(*self) } }
impl JobcratRepairCstr for *const libc::c_char { unsafe fn jobcrat_cstrlen(&self) -> usize { libc::strlen(*self) } }
impl JobcratRepairCstr for &[libc::c_char] { unsafe fn jobcrat_cstrlen(&self) -> usize { libc::strlen(self.as_ptr()) } }
impl JobcratRepairCstr for &mut [libc::c_char] { unsafe fn jobcrat_cstrlen(&self) -> usize { libc::strlen(self.as_ptr()) } }
/// the length of a C string plus its NUL, from the input's raw pointer or the output's slice
pub unsafe fn jobcrat_repair_cstrlen1<P: JobcratRepairCstr>(p: P) -> usize { p.jobcrat_cstrlen() + 1 }
/// zero-fill a freshly allocated block (the `uninitialised` repairs, round 2)
pub unsafe fn jobcrat_repair_zero(p: *mut u8, n: usize) { if !p.is_null() { core::ptr::write_bytes(p, 0, n) } }
'''


def apply(body, program, variant, repairs, substrate_body=None):
    rows = [r for r in repairs if r["program"] == program]
    receipts, edits = [], []
    for r in rows:
        here = _find(body, r["fn"], r["original"])
        if variant != "emitted" and r.get("scope", "both") == "output":
            continue   # a repair of the output's form only: the input is already raw there
        if variant == "emitted" and r.get("scope", "both") == "output":
            for a, b in here:
                edits.append((a, b, r))
            receipts.append(f"output hold [{r['kind']}] {r['fn']}: {len(here)}x `{_norm(r['original'])}` -> `{_norm(r['replacement'])}` ({r['why']})")
            continue
        if variant == "emitted" and r.get("scope", "both") == "input":
            # rule 2: the tool changed what the expression means in the output (its formal is now a
            # reference), so the edit would not type-check there: the input alone is repaired
            receipts.append(f"input-repair [{r['kind']}] {r['fn']}: input only ({r['why']})")
            continue
        if variant == "emitted":
            there = _find(substrate_body, r["fn"], r["original"]) if substrate_body is not None else []
            if not here:
                receipts.append(f"input-repair [{r['kind']}] {r['fn']}: NOT applied to the output "
                                f"(the output's text differs from the input's at this site; input sites {len(there)})")
                continue
            if len(here) != len(there):
                receipts.append(f"input-repair [{r['kind']}] {r['fn']}: occurrence count differs "
                                f"(output {len(here)}, input {len(there)}): applied to the {len(here)} byte-equal ones")
        for a, b in here:
            edits.append((a, b, r))
        receipts.append(f"input-repair [{r['kind']}] {r['fn']}: {len(here)}x `{_norm(r['original'])}` -> "
                        f"`{_norm(r['replacement'])}` (removes: {r['removes']}; why: {r['why']})")
    edits.sort(key=lambda x: x[0])
    out, i = [], 0
    for a, b, r in edits:
        if a < i:
            continue
        out.append(body[i:a]); out.append(r["replacement"]); i = b
    out.append(body[i:])
    body = "".join(out)
    if any("crate::jobcrat_repair_" in r["replacement"] for _, _, r in edits):
        body += RUNTIME
    return body, receipts
