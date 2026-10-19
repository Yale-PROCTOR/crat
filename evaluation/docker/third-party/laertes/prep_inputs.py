#!/usr/bin/env python3
"""Laertes's inputs of record: as close as the artifacts allow to the input each of CROWN's distributed Laertes trees
was produced from.
- CROWN's eleven (avl binn bst buffer heman ht json.h libtree lodepng quadtree rgba): the artifact's
  comparison/laertes-crown/before/<p> with the crate root's header set to the header of the artifact's Laertes OUTPUT
  (after/<p>): the three gates the tool's nightly-2020-10-15 rejects removed, and every `#![feature(..)]` line of the
  after root that the before root lacks added at the top, in the after's order (Laertes does not edit the header).
  binn: `#![feature(rustc_private)]` as well, so that its `extern crate libc;` resolves from the sysroot.
- brotli: CROWN's benchmark/brotli (no Laertes tree exists), the three gates removed, const_fn_fn_ptr_basics and
  const_mut_refs (the gates of Laertes's own benchmarks) added.
- Laertes's own eight: NOT prepared here -- the Laertes image's own initial-benchmarks/<p>, unchanged.
usage: prep_inputs.py <third-party dir>   (reads comparison/ and crown/benchmark/; writes laertes/inputs/<p> and
       laertes/inputs/ADAPTATION.tsv, which must equal laertes/ADAPTATION.tsv beside this script)"""
import os, re, shutil, sys

T = os.path.abspath(sys.argv[1])
OUT = os.path.join(T, "laertes", "inputs")
CROWN11 = ["avl", "binn", "bst", "buffer", "heman", "ht", "json.h", "libtree", "lodepng", "quadtree", "rgba"]
DROP = re.compile(r"^#!\[feature\((strict_provenance|core_intrinsics|raw_ref_op)\)\]\s*$")
FEAT = re.compile(r"^#!\[feature\(.*\)\]\s*$")
if os.path.exists(OUT):
    shutil.rmtree(OUT)
os.makedirs(OUT)
log = ["program\troot\tadded\tremoved"]
for p in CROWN11 + ["brotli"]:
    src = os.path.join(T, "crown", "benchmark", "brotli") if p == "brotli" else \
        os.path.join(T, "comparison", "laertes-crown", "before", p)
    dst = os.path.join(OUT, p)
    shutil.copytree(src, dst)
    root = os.path.join(dst, "lib.rs")
    lines = open(root, encoding="utf-8").read().split("\n")
    removed = [l for l in lines if DROP.match(l)]
    lines = [l for l in lines if not DROP.match(l)]
    if p == "brotli":
        add = ["#![feature(const_fn_fn_ptr_basics)]", "#![feature(const_mut_refs)]"]
    else:
        after = open(os.path.join(T, "comparison", "laertes-crown", "after", p, "lib.rs"), encoding="utf-8").read().split("\n")
        have = set(l.strip() for l in lines)
        add = [l.strip() for l in after if FEAT.match(l) and l.strip() not in have]
        if p == "binn":
            add.append("#![feature(rustc_private)]")
    open(root, "w", encoding="utf-8").write("\n".join(add + lines))
    log.append("%s\tlib.rs\t%s\t%s" % (p, " ".join(add) or "-", " ".join(x.strip() for x in removed) or "-"))
open(os.path.join(OUT, "ADAPTATION.tsv"), "w").write("\n".join(log) + "\n")
ref = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "ADAPTATION.tsv")).read()
if ref != "\n".join(log) + "\n":
    sys.exit("prep_inputs.py: the header adaptation differs from the record's ADAPTATION.tsv")
print("laertes inputs prepared: %d programs, adaptation = the record's" % (len(log) - 1))
