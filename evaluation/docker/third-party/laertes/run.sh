#!/bin/bash
# third-party step `laertes`: the Aliasing Limits artifact image (Laertes's 2023 tool, nightly-2020-10-15) on the
# twenty, one program at a time, one throw-away container per trial (--rm --network none).
#   pass emulate   : the mode of record (--emulate-lifetime-only): trial 1, then trials 2..3 where trial 1 completes;
#                    the minimum wall is rq3.<p>.laertes-s, a program that does not complete is `crash`
#   pass noemulate : the tool's own mode, one trial: rq3.<p>.laertes-own-mode = ok | stops
# Needs the step `crown` first (the artifact's comparison/ and CROWN's benchmark/ are its inputs).
# Writes laertes/inputs/<p>, laertes/runs/{emulate,noemulate}/<p>/t<k>/ (command, status, time.txt, stdout, stderr, tree/).
set -euo pipefail
source "$(dirname "$0")/../lib/common.sh"
T=$THIRD_PARTY
LAERTES_IMAGE=aliasing-limits-oopsla23:final
[ -f "$T/crown/.comparison.done" ] || die "laertes needs the step crown first (the artifact's comparison/)"
if ! $DOCKER image inspect "$LAERTES_IMAGE" >/dev/null 2>&1; then
  fetch aliasing-limits-oopsla23.tar.gz
  log "load $LAERTES_IMAGE"
  $DOCKER load -i "$TP_DOWNLOADS/aliasing-limits-oopsla23.tar.gz" >/dev/null || die "load laertes failed"
fi
gnu_time
[ -f "$T/laertes/inputs/ADAPTATION.tsv" ] || python3 "$TP_HOME/laertes/prep_inputs.py" "$T"
chmod -R a+rX "$T/laertes/inputs"
OWN=" bzip2 genann libcsv libzahl lil robotfindskitten tulipindicators urlparser "
one() {  # pass program trial flag
  local pass=$1 p=$2 k=$3 flag=$4 mode=crown d
  case "$OWN" in *" $p "*) mode=own;; esac
  d=$T/laertes/runs/$pass/$p/t$k
  [ -f "$d/status" ] && return 0
  rm -rf "$d"; open_dir "$d"
  log "laertes $pass $p t$k load=$(cut -d' ' -f1-3 /proc/loadavg)"
  $DOCKER run --rm --network none -v "$T/laertes/inputs":/w/in:ro -v "$d":/w/out -v "$GNU_TIME":/opt/time:ro \
    -v "$TP_HOME/laertes/laertes-one.sh":/w/laertes-one.sh:ro "$LAERTES_IMAGE" \
    bash -lc "/w/laertes-one.sh $mode $p $flag" > "$d/container.log" 2>&1 || true
  log "laertes $pass $p t$k $(tr '\n' ' ' < "$d/status" 2>/dev/null) wall=$(wall_of "$d/time.txt")"
}
N=$(trials_of 3)
for p in $TWENTY_RUN; do
  one emulate "$p" 1 emu
  if grep -q '^complete=1' "$T/laertes/runs/emulate/$p/t1/status"; then
    for k in $(seq 2 "$N"); do one emulate "$p" "$k" emu; done
  fi
done
for p in $TWENTY_RUN; do one noemulate "$p" 1 noemu; done
log "laertes done"
