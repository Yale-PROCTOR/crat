#!/bin/bash
# analysis-fanout relay 149 B.2 -- CONTAINER side (aliasing-limits-oopsla23:final, unmodified, --rm --network none).
# One program, one trial of the mode CROWN's log shows: resolve-lifetimes -f --emulate-lifetime-only, invoked as the
# artifact's own scripts invoke it (cargo run --release --bin resolve-lifetimes), on r101/in/<p> (CROWN's
# comparison/laertes-{crown,laertes}/before, brotli = benchmark/brotli; the three crate-root feature gates the tool's
# nightly-2020-10-15 rejects removed, 050 §V2). The tool rewrites in place: a fresh copy per trial.
# Mounts: /w/in (ro, r101/in), /w/out (this trial's dir), /opt/time (GNU time 1.7 from Ubuntu bionic's 'time' package).
# Usage: laertes-one.sh <program>
set -u
P=${1:?program}
L=${LAERTES_ARTIFACT:?set it to the Laertes image artifact directory, see evaluation/README.md}/laertes
cd $L || exit 90
root_of(){ case $1 in
  bzip2|libcsv|libzahl|robotfindskitten) echo rust/c2rust-lib.rs;;
  genann|lil|tulipindicators) echo c2rust-lib.rs;;
  urlparser) echo test.rs;;
  *) echo lib.rs;;
esac; }
R=$(root_of $P)
mkdir -p benchmark; rm -rf benchmark/$P; cp -r /w/in/$P benchmark/$P
CMD="cargo run --release --bin resolve-lifetimes -- -f --emulate-lifetime-only -- benchmark/$P/$R"
echo "$CMD" > /w/out/command
timeout --kill-after=30 14400 /opt/time -v -o /w/out/time.txt $CMD > /w/out/stdout 2> /w/out/stderr
echo "exit=$?" > /w/out/status
{ echo "iterations=$(grep -c '^iteration ' /w/out/stdout)"; echo "done=$(grep -c '^DONE' /w/out/stdout)"; } >> /w/out/status
mkdir -p /w/out/tree && cp -r benchmark/$P/. /w/out/tree/
chmod -R a+rwX /w/out
