#!/bin/bash
# CONTAINER side (the Aliasing Limits image, unmodified, --network none): Laertes's 2023 tool on one program, one trial.
#   <mode> crown : the prepared input /w/in/<p> (prep_inputs.py), the command CROWN's distributed logs show:
#                  cargo run --release --bin resolve-lifetimes -- -f [--emulate-lifetime-only] -- benchmark/<p>/lib.rs
#          own   : the image's own initial-benchmarks/<p>, unchanged, as the artifact's baseline step runs it:
#                  cargo run --release --bin resolve-lifetimes -- -f --merge-field-lifetimes [--emulate-lifetime-only] -- $(cat invocations/<p>)
#   <flag> emu   : with --emulate-lifetime-only (the mode of record: rq3.<p>.laertes-s)
#          noemu : without it (the tool's own mode: rq3.<p>.laertes-own-mode)
# RUST_LOG=off: the tool's logging is not part of its result. The tool rewrites in place: a fresh copy per trial.
# GNU time 1.9 (static, /opt/time) wraps the invocation.
# Usage: laertes-one.sh <mode> <program> <flag>
set -u
M=${1:?mode}; P=${2:?program}; FL=${3:?flag}
A=$HOME/artifact   # the image's own home (its user's)
case $FL in emu) EMU=--emulate-lifetime-only;; noemu) EMU=;; *) exit 91;; esac
export RUST_LOG=off
cd $A/laertes || exit 90
if [ $M = crown ]; then
  mkdir -p benchmark; rm -rf benchmark/$P; cp -r /w/in/$P benchmark/$P
  set -- -f $EMU -- benchmark/$P/lib.rs
  T=benchmark/$P
else
  rm -rf $A/workdir/$P; cp -r $A/initial-benchmarks/$P $A/workdir/$P
  set -- -f --merge-field-lifetimes $EMU -- $(cat $A/invocations/$P)
  T=$A/workdir/$P
fi
echo "RUST_LOG=$RUST_LOG cargo run --release --bin resolve-lifetimes -- $*" > /w/out/command
timeout --kill-after=30 14400 /opt/time -v -o /w/out/time.txt cargo run --release --bin resolve-lifetimes -- "$@" > /w/out/stdout 2> /w/out/stderr
rc=$?
{ echo "exit=$rc"; echo "iterations=$(grep -c '^iteration ' /w/out/stdout)"
  echo "complete=$([ $rc = 0 ] && grep -q '^DONE: The compiler successfully compiles the code' /w/out/stdout && echo 1 || echo 0)"; } > /w/out/status
mkdir -p /w/out/tree && cp -r $T/. /w/out/tree/
chmod -R a+rwX /w/out 2>/dev/null
