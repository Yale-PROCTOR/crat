#!/bin/bash
# r146 run_tools.sh: analysis-fanout 061's release-tool and 062's deref-tool (prebuilt binaries of record, no build) over the
# emitted trees of main/batch58pps39 (control) and main/batch60sp (60s') and the derived inputs; gated, START/END in SLOT-FREE.
S=scratch/analysis-fanout/r146/waivers; O=$S/out146; F=scratch/main/SLOT-FREE
RT=scratch/analysis-fanout/r080/release-tool/target/release/release-tool
DT=scratch/analysis-fanout/r083/taskB/deref-tool/target/release/deref-tool
D=crat/benchmarks/rs-crown-derived
$S/scripts/gate.sh || exit 1
echo "$(date -u +%FT%TZ) analysis-fanout run START (relay 146): syn 2 counters release-tool + deref-tool (prebuilt, no build) over batch58pps39/batch60sp emitted trees + derived inputs, ~minutes, no lock" >> $F
for c in batch58pps39 batch60sp; do
  E=scratch/main/$c/emitted-trees; o=$O/tools-$c; mkdir -p $o; : > $o/out.tsv; : > $o/rows.tsv; : > $o/errors.txt
  for d in $E/*; do p=$(basename $d)
    for f in $d/*.rs; do [ $(basename $f) = build.rs ] && continue
      (ulimit -v 4194304; nice -n 10 $RT output $p $f) >> $o/out.tsv 2>>$o/errors.txt
      (ulimit -v 4194304; nice -n 10 $DT out $p $f) >> $o/rows.tsv 2>>$o/errors.txt; done
    for f in $D/$p/*.rs; do [ $(basename $f) = build.rs ] && continue
      (ulimit -v 4194304; nice -n 10 $RT input $p $f) >> $o/out.tsv 2>>$o/errors.txt
      (ulimit -v 4194304; nice -n 10 $DT in $p $f) >> $o/rows.tsv 2>>$o/errors.txt; done
  done
done
echo "$(date -u +%FT%TZ) analysis-fanout run END (relay 146): syn 2 counters" >> $F
