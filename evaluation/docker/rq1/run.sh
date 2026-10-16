#!/bin/bash
# rq1: Tables effect-all, effect-crown and effect-inator, from the emitted trees and the inputs (and, for the
# comparison columns and CROWN's population, the third-party outputs). Writes results/rq1/keys.txt,
# results/tables/effect-{all,crown,inator}.{csv,tex}.
# usage: rq1/run.sh [--small]
# environment (lib/common.py): SRC (the source root; default .), RESULTS (default $SRC/results),
#   TREES (default $RESULTS/trees), THIRD_PARTY (default $RESULTS/third-party), RQ1_JOBS (default 4), CLOC
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
for a in "$@"; do
  case $a in
    --small) export SMALL=1 ;;
    *) echo "rq1/run.sh: unknown argument $a" >&2; exit 2 ;;
  esac
done
export SRC=${SRC:-$(pwd)}
export RESULTS=${RESULTS:-$SRC/results}
B=${RQ1_BIN:-$HERE/target/release}
[ -x "$B/typed_counter" ] && [ -x "$B/decl_counter" ] || bash "$HERE/build.sh"
python3 "$HERE/lib/count.py"
python3 "$HERE/lib/keys.py"
