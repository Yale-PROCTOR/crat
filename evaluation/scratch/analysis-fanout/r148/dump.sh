#!/bin/bash
# analysis-fanout relay 148: dump mir_promoted (the T2 counter's phase: mir_built + const promotion + SimplifyCfg, the
# last pass being SimplifyCfg-promote-consts) of one crate with the stock nightly-2025-06-23 rustc -- no build of any
# tool; the counter's own compiler options (rlib, edition 2021, --cap-lints allow, deps_crate's rlibs as externs).
# (the official column: runtime-post-cleanup = the end of mir_drops_elaborated_and_const_checked)
# usage: dump.sh <side: input|substrate|ours> <program>
set -eu
S=$1; P=$2
R=scratch/analysis-fanout/r148
case $S in
  input) D=crat/benchmarks/rs-crown/$P;;
  ours) D=scratch/main/batch60sp/emitted-trees/$P;;
  substrate) D=scratch/analysis-fanout/r148/substrate/$P;;  # the rewriter input: emitted tree with emitted.patch reversed
esac
for f in lib.rs c2rust-lib.rs src/lib.rs rust/src/lib.rs test.rs; do [ -f $D/$f ] && { ROOT=$D/$f; break; }; done
DEP=crat/deps_crate/target/debug/deps
EXT=(); for f in $DEP/*.rlib; do b=$(basename $f); n=${b#lib}; n=${n%%-*}; EXT+=(--extern "$n=$f"); done
O=$R/mir/$S/$P; rm -rf $O; mkdir -p $O
rustc +nightly-2025-06-23 --edition 2021 --crate-type rlib --cap-lints allow -L dependency=$DEP "${EXT[@]}" \
  -Zdump-mir="SimplifyCfg-promote-consts | runtime-post-cleanup" -Zdump-mir-dir=$O/dump -Zmir-include-spans=yes -Zdump-mir-exclude-pass-number \
  --emit=mir -o $O/out.mir $ROOT > $O/rustc.log 2>&1 || { echo "rustc failed $S $P"; tail -5 $O/rustc.log; exit 1; }
echo "$S $P root=$ROOT files=$(ls $O/dump | wc -l)"
