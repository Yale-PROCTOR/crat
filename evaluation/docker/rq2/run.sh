#!/bin/bash
# rq2: Table scale's running times, from the translate step's receipts and GNU time files and the comparison tools'
# times (results/third-party/times.tsv). It translates nothing: the artifact's run.sh times the translate pass first.
# Writes results/rq2/keys.txt, results/rq2/runs.tsv, results/tables/scale.{csv,tex}.
# usage: rq2/run.sh [--small]
# environment: SRC (the source root; default .), RESULTS (default $SRC/results), RECEIPTS and TIMES (the directories
#   holding <p>.receipt and <p>.time / <p>.wall; default $RESULTS/rq2/runs), THIRD_PARTY (default $RESULTS/third-party)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
for a in "$@"; do
  case $a in
    --small) export SMALL=1 ;;
    *) echo "rq2/run.sh: unknown argument $a" >&2; exit 2 ;;
  esac
done
export SRC=${SRC:-$(pwd)}
export RESULTS=${RESULTS:-$SRC/results}
export PYTHONDONTWRITEBYTECODE=1
python3 "$HERE/times.py"
python3 "$HERE/table_scale.py"
