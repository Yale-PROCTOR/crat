#!/usr/bin/env python3
"""The kit copy inside the zip (evaluation/, relays 006-007, R1201-1), applied AFTER the rename on jobcrat-form text:
the zip's pass vocabulary (prepare / translate / check), the zip's name for the environment of record
(config/analysis-env.sh), the kit's statement of its own place, and the manifest's source lines (the identity grep of
relay 001 s4 must be empty before the zip). Exact strings; a missing string is reported, not fatal."""
import os
W = os.environ['W'].rstrip('/') + '/'
EDITS = [
 # relay 007: the trial script drives the zip's binary with the zip's pass name
 ('evaluation/rq3-trials/rq3_trials.py', "'--pass', 'expand,extern,preprocess'", "'--pass', 'prepare'"),
 ('evaluation/rq3-trials/rq3_trials.py', '"""jobcrat --pass expand,extern,preprocess (the 2026-08-06 substrate, default configs) on the c2rust crate."""', '"""jobcrat --pass prepare (the prepared substrate, default configs) on the c2rust crate."""'),
 ('evaluation/rq3-trials/rq3_trials.py', "note='jobcrat --pass expand,extern,preprocess (release jobcrat); output '", "note='jobcrat --pass prepare (release jobcrat); output '"),
 # the environment of record under the zip's name (relay 001 s5); the kit's place
 ('evaluation/README.md', '- **What it is not.** `evaluation/` is not built by the workspace, and it is not in the submission source zip.', '- **What it is not.** `evaluation/` is not built by the workspace.'),
 ('evaluation/README.md', 'The environment of record is `crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh`, referenced here, not copied.', 'The environment of record is `config/analysis-env.sh`.'),
 ('evaluation/MANIFEST.md', 'The environment of record is in the repository: `crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh` and `l01p14u-s39-mutlend-o-frame.md`.', 'The environment of record is in the repository: `config/analysis-env.sh`.'),
 # relay 001 s4: the identity grep is empty before the zip -- the manifest's source lines carry no URL, the fork no owner
 ('evaluation/MANIFEST.md', '- **Identity:** `Yale-PROCTOR/c2rust` at `e4a13cab5b6e53aba676d6b2505322425d269932` (C2Rust 0.21.0, built with nightly-2022-08-08 and clang 14), as the image `jobcrat-c2rust:yale-proctor-e4a13ca`', '- **Identity:** our C2Rust fork at `e4a13cab5b6e53aba676d6b2505322425d269932` (C2Rust 0.21.0, built with nightly-2022-08-08 and clang 14), as the image `jobcrat-c2rust:fork-e4a13ca`'),
 ('evaluation/MANIFEST.md', '- **Source:** https://github.com/Yale-PROCTOR/c2rust; the recipe is `inator/prep/Dockerfile.c2rust`.', '- **Source:** our C2Rust fork (not included); the recipe is `inator/prep/Dockerfile.c2rust`.'),
 ('evaluation/MANIFEST.md', '- **Source:** https://github.com/KomaEc/crown (no DOI found).', '- **Source:** `KomaEc/crown` on GitHub (no DOI found).'),
 ('evaluation/MANIFEST.md', '- **Source:** https://github.com/PLaSSticity/refinator-impl', '- **Source:** `PLaSSticity/refinator-impl` on GitHub'),
 ('evaluation/MANIFEST.md', '- **Source:** https://github.com/Z3Prover/z3/releases (tag `z3-4.15.4`).', '- **Source:** `Z3Prover/z3` on GitHub, the release tagged `z3-4.15.4`.'),
 ('evaluation/MANIFEST.md', '- **Source:** https://github.com/AlDanial/cloc/releases/tag/v2.00', '- **Source:** `AlDanial/cloc` on GitHub, the release tagged `v2.00`'),
]
applied = missing = 0
for rel, old, new in EDITS:
    p = W + rel
    try: s = open(p).read()
    except FileNotFoundError: print(f'MISSING-FILE\t{rel}'); missing += 1; continue
    c = s.count(old)
    if c == 1: open(p, 'w').write(s.replace(old, new)); applied += 1; print(f'APPLIED\t{rel}\t{old[:60]!r}')
    else: print(f'UNAPPLIED({c})\t{rel}\t{old[:70]!r}'); missing += 1
print(f'#KIT-EDITS applied={applied} unapplied={missing} of {len(EDITS)}')
