#!/bin/bash
# rq3: Table miri (Miri under Tree Borrows on buffer, genann, libtree, quadtree, rgba) and the shipped test suites
# of the six programs that have one, run natively. Writes results/rq3/keys.txt, results/tables/miri.{csv,tex}.
# usage: rq3/run.sh [--small] [--cap SECONDS] [--jobs N]
#   --small        skip the two runs that go to the eight-hour cap (genann: ours and CROWN's)
#   --cap SECONDS  the time limit of one Miri run (default 28800, the paper's eight hours)
#   --jobs N       Miri processes at a time (default 1)
# environment (lib/rq3.py): SRC (default .), RESULTS (default $SRC/results), TREES (default $RESULTS/trees),
#   SUBSTRATE (default $RESULTS/substrate), THIRD_PARTY (default $RESULTS/third-party), MIRI_TOOLCHAIN
#   (default nightly-2026-09-17). The Laertes / CROWN columns are run only when $THIRD_PARTY holds their outputs
#   (third-party/run.sh); otherwise their keys are written `skipped (no third-party outputs)`.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
while [ $# -gt 0 ]; do
  case $1 in
    --small) export SMALL=1 ;;
    --cap) export MIRI_CAP=$2; shift ;;
    --jobs) export RQ3_JOBS=$2; shift ;;
    *) echo "rq3/run.sh: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
export SRC=${SRC:-$(pwd)}
export RESULTS=${RESULTS:-$SRC/results}
export TREES=${TREES:-$RESULTS/trees}
export SUBSTRATE=${SUBSTRATE:-$RESULTS/substrate}
export THIRD_PARTY=${THIRD_PARTY:-$RESULTS/third-party}
export MIRI_TOOLCHAIN=${MIRI_TOOLCHAIN:-nightly-2026-09-17}
mkdir -p "$RESULTS/rq3"
python3 "$HERE/lib/rq3.py" native
python3 "$HERE/lib/rq3.py" miri ours
if [ -d "$THIRD_PARTY/trees/crown" ]; then python3 "$HERE/lib/rq3.py" miri crown; fi
if [ -d "$THIRD_PARTY/comparison" ]; then python3 "$HERE/lib/rq3.py" miri laertes; fi
python3 "$HERE/lib/rq3.py" keys
