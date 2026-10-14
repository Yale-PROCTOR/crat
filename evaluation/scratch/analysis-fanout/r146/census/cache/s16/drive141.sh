#!/bin/bash
# r141: r110 s16u drive.sh, offsets located afresh per solve (offsets141.py). $1 = tag (s39|ctl), $2 = solve dir.
D=scratch/analysis-fanout/r146/census/cache/s16
T=$1; S=$2; W=$D/work-$T; mkdir -p $W; cd $W
cp $D/return_port_port.py $D/markers.py $D/locate_licensing.py .
sed "s#^C = .*#C = '$S/cache/era5b-model-cache-v1/'#" $D/run_frame.py > run_frame.py
cp $D/run_big.py run_big.py
nice -n 10 ionice -c2 -n7 python3 $D/offsets141.py $S licensing-offsets.txt > offsets.log 2>&1 || { echo "$T OFFSETS FAILED" >> $D/status; exit 1; }
rm -f admitted-rows.tsv
nice -n 10 ionice -c2 -n7 python3 run_frame.py > run_frame.log 2>&1
grep SKIP-LARGE run_frame.log | while read _ name len; do
  read s e < <(awk -v n=$name '$1==n{print $3, $4}' licensing-offsets.txt)
  nice -n 10 ionice -c2 -n7 python3 markers.py $S/cache/era5b-model-cache-v1/$name $s $e > $name.markers.all
  grep -E ',"(metadata|no_ref_carriers|value_origins|offset)"' $name.markers.all > $name.markers
  nice -n 10 ionice -c2 -n7 python3 run_big.py $S/cache/era5b-model-cache-v1/$name $name.markers $e >> run_frame.log 2>&1
done
echo "$T DONE $(date -u +%FT%TZ)" >> $D/status
