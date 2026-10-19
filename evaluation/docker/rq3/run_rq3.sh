#!/bin/bash
# rq3: Table miri (Miri under Tree Borrows on buffer, genann, libtree, quadtree, rgba) and the shipped test suites
# of the six programs that have one, run natively. Writes <out>/keys.txt and results/tables/miri.{csv,tex}.
# usage: rq3/run_rq3.sh <trees> <substrate> <out> [--small] [--cap SECONDS] [--jobs N] [--tools ours[,crown,laertes]]
#   <trees>        the emitted trees, one directory per program (results/trees)
#   <substrate>    the prepared inputs, one directory per program (results/substrate): the text the declared
#                  repairs are matched against
#   <out>          this step's results (results/rq3); the tables go to its parent's tables/
#   --small        skip the two runs that go to the eight-hour cap (genann: ours and CROWN's)
#   --cap SECONDS  the time limit of one Miri run (default 28800, the paper's eight hours)
#   --jobs N       Miri processes at a time (default 1)
#   --tools LIST   whose translations run under Miri (default ours); crown and laertes read $THIRD_PARTY
#                  (default <out>/../third-party); a column not run is written `skipped (no third-party outputs)`
# environment: SRC (the source root; default .), MIRI_TOOLCHAIN (default nightly-2026-09-17)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
[ $# -ge 3 ] || { sed -n '2,15p' "$0" >&2; exit 2; }
export TREES=$(realpath "$1") SUBSTRATE=$(realpath "$2"); mkdir -p "$3"; export RQ3_OUT=$(realpath "$3"); shift 3
TOOLS=ours
while [ $# -gt 0 ]; do
  case $1 in
    --small) export SMALL=1 ;;
    --cap) export MIRI_CAP=$2; shift ;;
    --jobs) export RQ3_JOBS=$2; shift ;;
    --tools) TOOLS=$2; shift ;;
    *) echo "rq3/run_rq3.sh: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
export SRC=${SRC:-$(pwd)}
export RESULTS=${RESULTS:-$(dirname "$RQ3_OUT")}
export THIRD_PARTY=${THIRD_PARTY:-$RESULTS/third-party}
export MIRI_TOOLCHAIN=${MIRI_TOOLCHAIN:-nightly-2026-09-17}
python3 "$HERE/lib/rq3.py" native
for t in ${TOOLS//,/ }; do python3 "$HERE/lib/rq3.py" miri "$t"; done
python3 "$HERE/lib/rq3.py" keys
