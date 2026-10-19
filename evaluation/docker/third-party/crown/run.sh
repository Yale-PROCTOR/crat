#!/bin/bash
# third-party step `crown`: CROWN's artifact image on the twenty, timed with the protocol of record (3 trials, the
# minimum is the key rq3.<p>.crown-s; one trial under --small), one program at a time, one throw-away container per
# trial (--rm --network none). Writes, under $THIRD_PARTY:
#   crown/runs/<p>/t<k>/   command, steps, time.txt (GNU time -v), stdout, stderr, status
#   trees/crown/<p>/       trial 1's output tree with analysis_results/ (CROWN's distributed translation for RQ1 / RQ3)
#   crown/evaluation.csv   CROWN's own evaluate.sh over those trees (full run only: it tabulates all twenty)
#   crown/benchmark/, comparison/   the image's inputs and the artifact's comparison/ (Laertes's trees), copied out
set -euo pipefail
source "$(dirname "$0")/../lib/common.sh"
crown_image; gnu_time
T=$THIRD_PARTY
if [ ! -f "$T/crown/.comparison.done" ]; then
  log "crown: copy the artifact's comparison/ and benchmark/ out of the image"
  open_dir "$T/crown"; rm -rf "$T/comparison" "$T/crown/benchmark"; open_dir "$T/.x"
  $DOCKER run --rm --network none -v "$T/.x":/w "$CROWN_IMAGE" bash -c \
    'cp -r /root/crown/comparison /root/crown/benchmark /w/ && chmod -R a+rwX /w'
  mv "$T/.x/comparison" "$T/comparison"; mv "$T/.x/benchmark" "$T/crown/benchmark"; rmdir "$T/.x"
  touch "$T/crown/.comparison.done"
fi
N=$(trials_of 3)
for p in $TWENTY_RUN; do
  for k in $(seq 1 "$N"); do
    d=$T/crown/runs/$p/t$k
    [ -f "$d/status" ] && continue
    rm -rf "$d"; open_dir "$d"
    log "crown $p t$k load=$(cut -d' ' -f1-3 /proc/loadavg)"
    $DOCKER run --rm --network none -v "$d":/w/out -v "$GNU_TIME":/opt/time:ro \
      -v "$TP_HOME/crown/crown-one.sh":/w/crown-one.sh:ro "$CROWN_IMAGE" bash -lc "/w/crown-one.sh $p" > "$d/container.log" 2>&1 || true
    log "crown $p t$k $(tr '\n' ' ' < "$d/status" 2>/dev/null) wall=$(wall_of "$d/time.txt")"
  done
  if [ ! -d "$T/trees/crown/$p" ] && grep -q '^exit=0' "$T/crown/runs/$p/t1/status" 2>/dev/null; then
    mkdir -p "$T/trees/crown"; cp -r "$T/crown/runs/$p/t1/tree" "$T/trees/crown/$p"
  fi
done
if [ "$SMALL" != 1 ] && [ ! -f "$T/crown/evaluation.csv" ]; then
  log "crown: evaluate.sh over the twenty trees"
  rm -rf "$T/crown/eval"; open_dir "$T/crown/eval"; cp -r "$T/trees/crown/." "$T/crown/eval/results/"; chmod -R a+rwX "$T/crown/eval"
  $DOCKER run --rm --network none -v "$T/crown/eval":/w "$CROWN_IMAGE" bash -lc \
    'cd /root/crown && ./evaluate.sh benchmark /w/results /w/results > /w/evaluate.log 2>&1; cp evaluation.csv /w/; chmod -R a+rwX /w'
  cp "$T/crown/eval/evaluation.csv" "$T/crown/evaluation.csv"
fi
log "crown done"
