#!/bin/bash
# analysis-fanout relay 149 B.2 -- CONTAINER side, the inputs and commands OF RECORD (aliasing-limits-oopsla23:final,
# unmodified, --rm --network none). Two modes, by where the artifact's Laertes tree came from:
#   crown <p>: CROWN's laertes-crown before-tree (+ brotli), header as prep_laertes2.py sets it (/w/in2/<p>), the command
#              CROWN's log shows: cargo run --release --bin resolve-lifetimes -- -f --emulate-lifetime-only -- benchmark/<p>/lib.rs
#   own <p>:   the image's own initial-benchmarks/<p>, unchanged, run as the Laertes artifact's baseline step runs it
#              (scripts/run-all-invocations.sh ../invocations --emulate-lifetime-only): RUST_LOG=off cargo run --release
#              --bin resolve-lifetimes -- -f --merge-field-lifetimes --emulate-lifetime-only -- $(cat ../invocations/<p>)
# The tool rewrites in place: a fresh copy per trial. GNU time 1.7 (bionic's package) wraps the whole invocation.
# Usage: laertes-one2.sh <mode> <program>
set -u
M=${1:?mode}; P=${2:?program}
A=${LAERTES_ARTIFACT:-~reviewer/artifact}
cd $A/laertes || exit 90
if [ $M = crown ]; then
  mkdir -p benchmark; rm -rf benchmark/$P; cp -r /w/in2/$P benchmark/$P
  echo "cargo run --release --bin resolve-lifetimes -- -f --emulate-lifetime-only -- benchmark/$P/lib.rs" > /w/out/command
  timeout --kill-after=30 14400 /opt/time -v -o /w/out/time.txt \
    cargo run --release --bin resolve-lifetimes -- -f --emulate-lifetime-only -- benchmark/$P/lib.rs > /w/out/stdout 2> /w/out/stderr
  rc=$?
  T=benchmark/$P
else
  rm -rf $A/workdir/$P; cp -r $A/initial-benchmarks/$P $A/workdir/$P
  INV=$(cat $A/invocations/$P)
  echo "RUST_LOG=off cargo run --release --bin resolve-lifetimes -- -f --merge-field-lifetimes --emulate-lifetime-only -- $INV" > /w/out/command
  RUST_LOG=off timeout --kill-after=30 14400 /opt/time -v -o /w/out/time.txt \
    cargo run --release --bin resolve-lifetimes -- -f --merge-field-lifetimes --emulate-lifetime-only -- $INV > /w/out/stdout 2> /w/out/stderr
  rc=$?
  T=$A/workdir/$P
fi
{ echo "exit=$rc"; echo "iterations=$(grep -c '^iteration ' /w/out/stdout)"; echo "done=$(grep -c '^DONE' /w/out/stdout)"; } > /w/out/status
mkdir -p /w/out/tree && cp -r $T/. /w/out/tree/
chmod -R a+rwX /w/out 2>/dev/null
