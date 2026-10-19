#!/usr/bin/env python3
"""relay 152 (E4) harness edit, declared: a multi-file c2rust-layout tree (CROWN's output, or the
c2rust input it was given) is flattened into one crate root as our emitted trees are, so that
miri_census.py's single-file project builder takes it. Every `pub mod X;` is replaced by
`pub mod X { <contents of X.rs> }`; nothing else in the program text changes.
usage: flatten.py <tree> <out-tree>"""
import os, re, shutil, sys
src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
for f in ("Cargo.toml", "build.rs"):
    if os.path.exists(os.path.join(src, f)):
        shutil.copy(os.path.join(src, f), os.path.join(out, f))
stack, res, n = [], [], 0
root = next(r for r in ("lib.rs", "c2rust-lib.rs") if os.path.exists(os.path.join(src, r)))
for line in open(os.path.join(src, root)).read().split("\n"):
    m = re.match(r"^\s*pub mod (\w+)\s*\{", line)
    d = re.match(r"^\s*pub mod (\w+)\s*;", line)
    if m:
        stack.append(m.group(1)); res.append(line)
    elif d:
        p = os.path.join(src, *stack, d.group(1) + ".rs")
        res.append(f"pub mod {d.group(1)} {{\n" + open(p).read() + "\n}")
        n += 1
    elif re.match(r"^\s*\}", line) and stack:
        stack.pop(); res.append(line)
    else:
        res.append(line)
open(os.path.join(out, "lib.rs"), "w").write("\n".join(res))
print(f"flattened {n} module files from {src}")
