#!/usr/bin/env python3
"""prep_laertes2.py -- relay 149 B.2: Laertes's inputs OF RECORD, i.e. as close as the artifacts allow to the input each
of CROWN's distributed Laertes trees was produced from.
- laertes-crown (avl binn bst buffer heman ht json.h libtree lodepng quadtree rgba): CROWN's comparison/laertes-crown/
  before/<p> with the crate root's header set to the header of the artifact's Laertes OUTPUT (after/<p>): the three gates
  the tool's nightly-2020-10-15 rejects removed (050 V2), and every `#![feature(..)]` line of the after root that the
  before root lacks added at the top, in the after's order (Laertes does not edit the header: avl's run keeps it as
  given). binn: `#![feature(rustc_private)]` added as well, so that its `extern crate libc;` resolves from the sysroot in
  a cargo-less invocation (the after tree has no `extern crate libc;`).
- brotli: CROWN's benchmark/brotli (no Laertes tree exists: the README says the tool crashes on it), 050's V2 header
  (the three gates removed; const_fn_fn_ptr_basics and const_mut_refs, the gates of Laertes's own benchmarks, added).
- laertes-laertes (bzip2 genann libcsv libzahl lil robotfindskitten tulipindicators urlparser): NOT prepared here --
  the Laertes image's own initial-benchmarks/<p>, unchanged, with its own invocation (laertes-one2.sh mode own).
Writes r149/in2/<p> and r149/in2/ADAPTATION.tsv (program, root, lines added, lines removed)."""
import os, re, shutil

C = "crown-artifact"
R = os.path.dirname(os.path.abspath(__file__))
CROWN11 = ["avl", "binn", "bst", "buffer", "heman", "ht", "json.h", "libtree", "lodepng", "quadtree", "rgba"]
DROP = re.compile(r"^#!\[feature\((strict_provenance|core_intrinsics|raw_ref_op)\)\]\s*$")
FEAT = re.compile(r"^#!\[feature\(.*\)\]\s*$")
os.makedirs(R + "/in2", exist_ok=True)
log = ["program\troot\tadded\tremoved"]
for p in CROWN11 + ["brotli"]:
    src = C + ("/benchmark/brotli" if p == "brotli" else "/comparison/laertes-crown/before/" + p)
    dst = R + "/in2/" + p
    if os.path.exists(dst):
        raise SystemExit("exists: " + dst)
    shutil.copytree(src, dst)
    root = dst + "/lib.rs"
    lines = open(root, encoding="utf-8").read().split("\n")
    removed = [l for l in lines if DROP.match(l)]
    lines = [l for l in lines if not DROP.match(l)]
    if p == "brotli":
        add = ["#![feature(const_fn_fn_ptr_basics)]", "#![feature(const_mut_refs)]"]
    else:
        after = open(C + "/comparison/laertes-crown/after/" + p + "/lib.rs", encoding="utf-8").read().split("\n")
        have = set(l.strip() for l in lines)
        add = [l.strip() for l in after if FEAT.match(l) and l.strip() not in have]
        if p == "binn":
            add.append("#![feature(rustc_private)]")
    open(root, "w", encoding="utf-8").write("\n".join(add + lines))
    log.append("%s\tlib.rs\t%s\t%s" % (p, " ".join(add) or "-", " ".join(x.strip() for x in removed) or "-"))
open(R + "/in2/ADAPTATION.tsv", "w").write("\n".join(log) + "\n")
print("\n".join(log))
