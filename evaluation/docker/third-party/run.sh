#!/bin/bash
# third-party/run.sh -- the comparison tools of the evaluation, fetched from their public archives and run with the
# protocols of record. Runs on the HOST: it needs a Docker daemon (the jobcrat image has none), curl, unzip, python3.
# Writes only under $THIRD_PARTY (default results/third-party); every step is optional and separate from the jobcrat
# columns, which run.sh produces without it.
#
# usage: third-party/run.sh [step ...] [--small] [--trials N]
#   steps (default: all, in this order):
#     crown    CROWN's image (Zenodo 10.5281/zenodo.7966511) on the twenty: rq3.<p>.crown-s; its output trees and
#              evaluation table; the artifact's comparison/ (Laertes's distributed trees) copied out
#     laertes  the Aliasing Limits image (Zenodo 10.5281/zenodo.7714175), Laertes's 2023 tool, on the twenty, in the
#              mode of record (--emulate-lifetime-only): rq3.<p>.laertes-s; and in its own mode: laertes-own-mode
#     inator   &inator's image (Zenodo 10.5281/zenodo.19650358) on its eight: rq3.inator.<q>.host-s, its types
#     c2rust   c2rust 0.21.0-p1 (upstream v0.21.0 + c2rust-0.21.0-p1.patch) on the eight: rq3.inator.<q>.c2rust-s
#     tables   times.tsv (the keys' values) and check.txt (the fetched trees against expected-trees.tsv)
#   --small    CROWN and Laertes on the twenty minus lil and brotli; &inator on ulidgen leftpad amp nandc carrays;
#              c2rust on the eight; one trial each
#   --trials N the trial count for every tool (default: the record's -- CROWN 3, Laertes 3 where it completes,
#              &inator 5 where trial 1 is under 600 s, c2rust 3)
# environment: SRC, RESULTS, THIRD_PARTY, TP_DOWNLOADS, DOCKER, INATOR_BENCHMARKS (lib/common.sh)
# Times are reported, not expected to equal the record's; run on an otherwise idle machine, as the record did.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
STEPS=()
while [ $# -gt 0 ]; do
  case $1 in
    --small) export SMALL=1 ;;
    --trials) export TRIALS=${2:?--trials N}; shift ;;
    crown|laertes|inator|c2rust|tables) STEPS+=("$1") ;;
    all) STEPS+=(crown laertes inator c2rust tables) ;;
    *) echo "third-party/run.sh: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
[ ${#STEPS[@]} -gt 0 ] || STEPS=(crown laertes inator c2rust tables)
command -v "${DOCKER:-docker}" >/dev/null || { echo "third-party/run.sh: needs docker on the host" >&2; exit 2; }
for s in "${STEPS[@]}"; do
  if [ "$s" = tables ]; then
    ( source "$HERE/lib/common.sh"; THIRD_PARTY=$THIRD_PARTY SMALL=$SMALL TWENTY="$TWENTY" EIGHT="$EIGHT" python3 "$HERE/lib/tables.py" )
  else
    bash "$HERE/$s/run.sh"
  fi
done
