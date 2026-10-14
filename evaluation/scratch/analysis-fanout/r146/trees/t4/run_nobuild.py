#!/usr/bin/env python3
"""relay 116 / S25a: pos_census.py's run/summarize with build() replaced by the prebuilt binary (no cargo).
usage: run_nobuild.py {run|summarize} --side S --out DIR [--census C] [PROG ...]"""
import os, sys
TOOLS = 'tmp/scratchpad/wt067/agents/tools/rq2'
sys.path.insert(0, TOOLS)
import pos_census as P
assert os.path.isfile(P.EXE), P.EXE
P.build = lambda: P.EXE          # the binary built 2026-10-02 13:02 from pos_counter/ (unchanged since 9d79b3a)
sys.argv[0] = 'pos_census.py'
P.main()
