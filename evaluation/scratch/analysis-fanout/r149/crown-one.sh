#!/bin/bash
# analysis-fanout relay 149 B.1 -- CONTAINER side (crown:latest, unmodified, --rm --network none).
# One program, one trial: the artifact's own configuration = run.sh's per-program OPTIONS, preceded by preprocess.sh's
# two steps (preprocess, explicit-addr); the whole tool invocation (the three crown calls) is wrapped in GNU time -v.
# Mounts: /w/out (writable: this trial's output dir), /opt/time (host GNU time 1.9, glibc 2.35 = the image's).
# Usage: crown-one.sh <program>
set -u
P=${1:?program}
cd /root/crown || exit 90
export LD_LIBRARY_PATH=$(rustc --print sysroot)/lib
source ./find_entry.sh
W=/tmp/ws; rm -rf $W; mkdir -p $W; cp -r benchmark/$P $W/$P
ENTRY=$(find_entry $W/$P)
OPTS=()
case $P in
  lil) OPTS=(--type-reconstruction --no-attempt '.*fnc_.*|do_exit|lil_find_var|lil_to_double');;
  libsamplerate) OPTS=(--no-attempt '.*_vari_process|.*_reset');;
  lodepng) OPTS=(--no-attempt 'bpmnode_create|uivector_resize');;
  quadtree) OPTS=(--force-box);;
  genann) OPTS=(--raw-mutability);;
esac
mkdir -p $W/$P/analysis_results
C=./target/release/crown
printf '%s\n' "$C $ENTRY preprocess in-place" "$C $ENTRY explicit-addr in-place" \
  "$C $ENTRY rewrite --results-path $W/$P/analysis_results ${OPTS[*]} in-place" > /w/out/command
cat > /tmp/inv.sh <<EOF
set -e
s0=\$(date +%s%N)
$C $ENTRY preprocess in-place
s1=\$(date +%s%N)
$C $ENTRY explicit-addr in-place
s2=\$(date +%s%N)
$C $ENTRY rewrite --results-path $W/$P/analysis_results ${OPTS[@]+$(printf "%q " "${OPTS[@]}")} in-place
s3=\$(date +%s%N)
echo "steps_ns preprocess=\$((s1-s0)) explicit_addr=\$((s2-s1)) rewrite=\$((s3-s2))" > /w/out/steps
EOF
timeout --kill-after=30 14400 /opt/time -v -o /w/out/time.txt bash /tmp/inv.sh > /w/out/stdout 2> /w/out/stderr
echo "exit=$?" > /w/out/status
mkdir -p /w/out/tree && cp -r $W/$P/. /w/out/tree/
chmod -R a+rwX /w/out
