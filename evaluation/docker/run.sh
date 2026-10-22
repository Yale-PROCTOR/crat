#!/bin/bash
# The evaluation's entry point (the image's ENTRYPOINT; it runs from the source root, results under ./results):
#   run.sh <translate|rq1|rq2|rq3|all> [--small] [--third-party] [--miri-cap SECONDS]
# translate  every program of lists/programs.tsv through prepare and translate, one at a time, as the paper's runs:
#              jobcrat --pass prepare -o results/substrate benchmarks/<suite>/<p>          (not timed)
#              cp -a results/substrate/<p> results/trees/<p>
#              JOBCRAT_ERA5C_RAW_CAUSE_LEDGER=off
#              [JOBCRAT_FALLBACK_SLICE_EXTENT=268435456: CROWN's twenty; unset for &inator's eight]
#              /usr/bin/time -v -o results/rq2/runs/<p>.time
#                jobcrat -v --pass translate --inplace --bo-receipt results/rq2/runs/<p>.receipt results/trees/<p>
#            every other switch exported from config/analysis-env.sh (analysis_env below: a variable already set in the
#            environment wins); jobcrat is target/release/jobcrat with the environment the
#            top-level wrapper gives it (DIR, SYSROOT, LD_LIBRARY_PATH), so that the times hold the pass alone;
#            results/rq2/runs/<p>.wall is the wall in seconds around the same command. A program whose
#            results/rq2/runs/<p>.rc reads 0 is not run again (delete results/ to start over).
# rq1, rq2, rq3  translate (as above), then that research question's script (rq1/run.sh, rq2/run.sh,
#            rq3/run_rq3.sh), which writes results/<rqN>/keys.txt and results/tables/.
# all        translate, rq1, rq2, rq3, then compare.py: results/compare.txt, every number beside the paper's.
# --small        without brotli and lil (32 GB of memory); rq3 skips genann's Miri run (its 8-hour cap)
# --third-party  the comparison tools' columns: requires results/third-party/, which third-party/run.sh writes on the
#                host (it needs a Docker daemon), before this run
# --miri-cap S   the cap of one Miri run in seconds (rq3's default: 28800)
set -uo pipefail
A=$(cd "$(dirname "$0")" && pwd); SRC=$(cd "$A/.." && pwd)
usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; }
STEP=${1:-}; [ $# -gt 0 ] && shift
SMALL=0; TP=0; CAP=
while [ $# -gt 0 ]; do
  case $1 in
    --small) SMALL=1 ;;
    --third-party) TP=1 ;;
    --miri-cap) CAP=${2:?--miri-cap SECONDS}; shift ;;
    *) echo "run.sh: unknown argument $1" >&2; usage >&2; exit 2 ;;
  esac
  shift
done
case $STEP in translate|rq1|rq2|rq3|all) ;; -h|--help|help|'') usage; exit 0 ;; *) echo "run.sh: unknown step $STEP" >&2; usage >&2; exit 2 ;; esac

export SRC SMALL RESULTS=${RESULTS:-$SRC/results}
export TREES=$RESULTS/trees SUBSTRATE=$RESULTS/substrate THIRD_PARTY=$RESULTS/third-party RUNS=$RESULTS/rq2/runs
export RECEIPTS=$RUNS TIMES=$RUNS
mkdir -p "$TREES" "$SUBSTRATE" "$RUNS" "$RESULTS/tables" "$RESULTS/logs"
if [ $TP = 1 ] && [ ! -d "$THIRD_PARTY" ]; then
  echo "run.sh: --third-party needs $THIRD_PARTY; on the host (with Docker), first run:" >&2
  echo "  bash artifact/third-party/run.sh$([ $SMALL = 1 ] && echo ' --small')     (from the source root)" >&2
  exit 2
fi
cd "$SRC"
exec > >(tee -a "$RESULTS/logs/run.log") 2>&1
small_flag() { [ $SMALL = 1 ] && echo --small; }
echo "RUN START $(date -u +%FT%TZ) step=$STEP small=$SMALL third-party=$TP host: $(nproc) threads, $(awk '/MemTotal/ {printf "%.0f GiB", $2/1048576}' /proc/meminfo)"

analysis_env() {  # analysis_env <file>: exports each `export NAME=value` of the file whose value is one plain word,
  local k v        # unless NAME is set already; the toolchain's four names are the wrapper's, not the analysis's
  while IFS='=' read -r k v; do
    k=${k//[[:space:]]/}; case $k in ''|SYSROOT|LD_LIBRARY_PATH|RUSTUP_TOOLCHAIN|TMPDIR) continue ;; esac
    v=${v#"${v%%[![:space:]]*}"}; v=${v%%[[:space:]]*}; v=${v#\"}; v=${v%\"}
    case $v in ''|'#'*|*'$'*) continue ;; esac
    [ -n "${!k+x}" ] || export "$k=$v"
  done < <(sed -n -E 's/^[[:space:]]*export[[:space:]]+//p' "$1")
}

translate() {
  local p suite small rc ext t0 t1 sysroot
  sysroot=$(rustc --print sysroot)
  while IFS=$'\t' read -r p suite small; do
    case $p in ''|'#'*) continue ;; esac
    [ $SMALL = 1 ] && [ "$small" != 1 ] && { echo "translate $p: skipped (--small)"; continue; }
    if [ "$(cat "$RUNS/$p.rc" 2>/dev/null)" = 0 ]; then echo "translate $p: done earlier"; continue; fi
    rm -rf "$SUBSTRATE/$p" "$TREES/$p" "$RUNS/$p.time" "$RUNS/$p.wall" "$RUNS/$p.receipt" "$RUNS/$p.rc"
    echo "translate $p ($suite): START $(date -u +%FT%TZ)"
    if ! ./jobcrat --pass prepare -o "$SUBSTRATE" "benchmarks/$suite/$p" > "$RESULTS/logs/prepare-$p.log" 2>&1; then
      echo "prepare-failed" > "$RUNS/$p.rc"; echo "translate $p: prepare FAILED (results/logs/prepare-$p.log)"; continue
    fi
    cp -a "$SUBSTRATE/$p" "$TREES/$p"
    ext=; [ "$suite" = crown ] && ext=JOBCRAT_FALLBACK_SLICE_EXTENT=268435456
    t0=$(date +%s.%N)
    ( analysis_env "$SRC/config/analysis-env.sh"
      env -u JOBCRAT_FALLBACK_SLICE_EXTENT JOBCRAT_ERA5C_RAW_CAUSE_LEDGER=off $ext \
        DIR="$SRC" SYSROOT="$sysroot" LD_LIBRARY_PATH="$sysroot/lib" \
        /usr/bin/time -v -o "$RUNS/$p.time" target/release/jobcrat -v --pass translate --inplace \
        --bo-receipt "$RUNS/$p.receipt" "$TREES/$p" > "$RESULTS/logs/translate-$p.log" 2>&1 )
    rc=$?; t1=$(date +%s.%N); echo $rc > "$RUNS/$p.rc"
    python3 -c "import sys; print(f'{float(sys.argv[2]) - float(sys.argv[1]):.3f}')" "$t0" "$t1" > "$RUNS/$p.wall"
    echo "translate $p: END $(date -u +%FT%TZ) rc=$rc wall=$(cat "$RUNS/$p.wall")s $(grep -m1 -o 'outcome=[^ ]*' "$RESULTS/logs/translate-$p.log")"
  done < "$A/lists/programs.tsv"
}

run_rq() {  # run_rq <rqN> <script> <args...>: runs a research question's script
  local rq=$1 s=$2 rc; shift 2
  echo "$rq START $(date -u +%FT%TZ)"; bash "$A/$s" "$@"; rc=$?; echo "$rq END $(date -u +%FT%TZ) rc=$rc"
}
rq1() { run_rq rq1 rq1/run.sh $(small_flag); }
rq2() { run_rq rq2 rq2/run.sh $(small_flag); }
rq3() {
  local tools=ours; [ -d "$THIRD_PARTY/trees/crown" ] && [ -d "$THIRD_PARTY/comparison" ] && tools=ours,crown,laertes
  run_rq rq3 rq3/run_rq3.sh "$TREES" "$SUBSTRATE" "$RESULTS/rq3" $(small_flag) ${CAP:+--cap "$CAP"} --tools $tools
}

case $STEP in
  translate) translate ;;
  rq1|rq2|rq3) translate; $STEP ;;
  all) translate; rq1; rq2; rq3; python3 "$A/compare.py" "$RESULTS"; tail -1 "$RESULTS/compare.txt" ;;
esac
echo "RUN END $(date -u +%FT%TZ) step=$STEP"
