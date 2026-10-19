#!/bin/bash
# third-party step `inator`: &inator's artifact image on its eight, with its own driver (`refinator <q>`), one trial at
# a time, one throw-away container per trial (--rm --network none), GNU time inside the container as the entrypoint.
# Trials (the protocol of record): trial 1; trials 2..5 where trial 1 completes in under 600 s (in-container wall);
# one under --small. tisp runs on the source build (the artifact's own Dockerfile on its Zenodo source): the shipped
# image stops on it before analysis, as in the record.
# rq3.inator.<q>.host-s = the minimum over completed trials of &inator's own phase timers (times.txt: representation +
# constraint generation + solving).
# Writes, under $THIRD_PARTY:
#   inator/src/<q>/          the eight's C benchmark directories (checked file by file against inputs-sha256.tsv)
#   inator/runs/<q>/t<k>/    meta.txt, inner.time, stdout, stderr, results/ (the driver's own output)
#   inator/<q>/              trial 1's rtypes.txt, stypes.txt, times.txt (the type comparison reads these)
#   INATOR_BENCHMARKS=<dir>  use a local copy of &inator's benchmarks/ instead of fetching it (still checked)
set -euo pipefail
source "$(dirname "$0")/../lib/common.sh"
T=$THIRD_PARTY
IMAGE=refinator:latest
SRC_IMAGE=tp-inator-src:4f1d6a5
if ! $DOCKER image inspect "$IMAGE" >/dev/null 2>&1; then
  fetch refinator-linux-amd64.tar.gz
  log "load $IMAGE"; $DOCKER load -i "$TP_DOWNLOADS/refinator-linux-amd64.tar.gz" >/dev/null || die "load inator failed"
fi
gnu_time

# the benchmarks: Zenodo carries six of the eight (no carrays, jccc, tisp); the authors' repository at the pinned
# commit carries all; every file is checked against the record's digests
B=$T/inator/benchmarks
if [ ! -f "$B/.ok" ]; then
  rm -rf "$B"; mkdir -p "$B"
  if [ -n "${INATOR_BENCHMARKS:-}" ]; then
    cp -r "$INATOR_BENCHMARKS"/. "$B"/
  else
    fetch inator-benchmarks.tar.gz; fetch inator-impl-4fdf3309.tar.gz
    tar --warning=no-unknown-keyword --exclude='._*' -xzf "$TP_DOWNLOADS/inator-impl-4fdf3309.tar.gz" -C "$B" \
      --strip-components=2 --wildcards '*/benchmarks/*'
    tar --warning=no-unknown-keyword --exclude='._*' -xzf "$TP_DOWNLOADS/inator-benchmarks.tar.gz" -C "$B" --strip-components=1
  fi
  python3 - "$B" "$TP_HOME/inator/inputs-sha256.tsv" <<'PY' || die "&inator's benchmarks differ from the record's digests"
import csv, hashlib, os, sys
b, m = sys.argv[1:3]
bad = [r["path"] for r in csv.DictReader(open(m), delimiter="\t")
       if not os.path.exists(os.path.join(b, r["path"]))
       or hashlib.sha256(open(os.path.join(b, r["path"]), "rb").read()).hexdigest() != r["sha256"]]
print("inator benchmarks: %s" % ("all files equal the record's digests" if not bad else "differ: %s" % bad))
sys.exit(1 if bad else 0)
PY
  touch "$B/.ok"
fi
for q in $EIGHT_RUN; do [ -d "$T/inator/src/$q" ] || { mkdir -p "$T/inator/src"; cp -r "$B/$q" "$T/inator/src/$q"; }; done

if echo " $EIGHT_INATOR " | grep -q ' tisp ' && ! $DOCKER image inspect "$SRC_IMAGE" >/dev/null 2>&1; then
  fetch refinator-src.tar.gz
  rm -rf "$T/inator/src-build"; mkdir -p "$T/inator/src-build"
  tar --warning=no-unknown-keyword --exclude='._*' -xzf "$TP_DOWNLOADS/refinator-src.tar.gz" -C "$T/inator/src-build"
  log "build $SRC_IMAGE (the artifact's own Dockerfile)"
  $DOCKER build -t "$SRC_IMAGE" "$T/inator/src-build/refinator-impl" > "$T/inator/src-build.log" 2>&1 || die "source build failed"
fi

inner_wall() { wall_of "$T/inator/runs/$1/t$2/inner.time"; }
one() {  # program trial
  local q=$1 k=$2 img=$IMAGE d
  [ "$q" = tisp ] && img=$SRC_IMAGE
  d=$T/inator/runs/$q/t$k
  [ -f "$d/meta.txt" ] && grep -q '^exit_code=' "$d/meta.txt" && return 0
  rm -rf "$d"; mkdir -p "$d/benchmarks"; cp -r "$B/$q" "$d/benchmarks/$q"; chmod -R a+rwX "$d"
  echo "program=$q trial=$k image=$img start_utc=$(date -u +%FT%TZ) load=$(cut -d' ' -f1-3 /proc/loadavg)" > "$d/meta.txt"
  log "inator $q t$k ($img)"
  set +e
  $DOCKER run --rm --network none --mount type=bind,src="$d/benchmarks",dst=/refinator/benchmarks \
    --mount type=bind,src="$GNU_TIME",dst=/opt/time,readonly --entrypoint /opt/time \
    "$img" -v -o /refinator/benchmarks/inner.time refinator "$q" > "$d/stdout" 2> "$d/stderr"
  local rc=$?; set -e
  echo "exit_code=$rc end_utc=$(date -u +%FT%TZ)" >> "$d/meta.txt"
  mv "$d/benchmarks/inner.time" "$d/inner.time" 2>/dev/null || true
  [ -d "$d/benchmarks/$q/results/latest" ] && cp -rL "$d/benchmarks/$q/results/latest" "$d/results"
  log "inator $q t$k exit=$rc inner=$(inner_wall "$q" "$k")"
}
N=$(trials_of 5)
for q in $EIGHT_INATOR; do
  one "$q" 1
  w=$(inner_wall "$q" 1)
  if [ -f "$T/inator/runs/$q/t1/results/times.txt" ] && [ -n "$w" ] && awk -v w="$w" 'BEGIN{exit !(w < 600)}'; then
    for k in $(seq 2 "$N"); do one "$q" "$k"; done
  fi
  if [ -f "$T/inator/runs/$q/t1/results/times.txt" ]; then
    mkdir -p "$T/inator/$q"
    cp "$T/inator/runs/$q/t1/results/"{rtypes.txt,stypes.txt,times.txt} "$T/inator/$q/"
  fi
done
log "inator done"
