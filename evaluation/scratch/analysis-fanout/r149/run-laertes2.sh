#!/bin/bash
# analysis-fanout relay 149 B -- HOST side (host-a). CROWN's and Laertes's tools TIMED on the twenty (R1091-2):
# one program at a time, one throw-away container per run (--rm --network none --memory 48g), the window checked
# before every run (guard.py; a closed window pauses the driver), host load sampled every 30 s (load.tsv).
# THIS PASS (run-laertes2.sh): Laertes on its inputs OF RECORD (prep_laertes2.py; laertes-one2.sh): trial 1 over the
# twenty, trials 2 and 3 over the programs whose trial 1 completed (exit 0 and DONE). Per-run bound 4 h.
# Writes one START line and one END line into main's SLOT-FREE. Kill only by the pid in run-all.pid.
set -u
R=scratch/analysis-fanout/r149
IN=scratch/analysis-fanout/r101/in
F=scratch/main/SLOT-FREE
OUT=$R/out
PROGS="avl binn brotli bst buffer bzip2 genann heman ht json.h libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser"
echo $$ > $R/run-laertes2.pid
mkdir -p $OUT
log(){ echo "$(date -u +%FT%TZ) $*" | tee -a $R/run-laertes2.log; }
( while true; do echo -e "$(date -u +%FT%TZ)\t$(cut -d' ' -f1-3 /proc/loadavg)\t$(awk '/MemAvailable/{print $2}' /proc/meminfo)" >> $R/load.tsv; sleep 30; done ) &
SAMPLER=$!
echo $SAMPLER > $R/sampler2.pid
wait_window(){ until python3 $R/guard.py > /tmp/r149-guard.$$ 2>&1; do log "PAUSE $(cat /tmp/r149-guard.$$)"; sleep 120; done; }
echo "$(date -u +%FT%TZ) analysis-fanout run START (relay 149 B, R1091-2): Laertes's tool timed on its inputs of record, one program at a time, 3 trials (image aliasing-limits-oopsla23:final; no crat binary, no corpus slot)" >> $F
run(){ # tool program trial
  local t=$1 p=$2 k=$3 d=$OUT/$1/$2/t$3
  [ -e $d/status ] && { log "SKIP $t $p t$k (done)"; return; }
  rm -rf $d 2>/dev/null; mkdir -p $d; chmod 777 $d
  wait_window
  log "RUN $t $p t$k load=$(cut -d' ' -f1 /proc/loadavg)"
  if [ $t = crown ]; then
    docker run --rm --network none --memory 48g -v $d:/w/out -v /usr/bin/time:/opt/time:ro \
      -v $R/crown-one.sh:/w/crown-one.sh:ro crown:latest bash -lc "/w/crown-one.sh $p" > $d/container.log 2>&1
  else
    local mode=crown; case $p in bzip2|genann|libcsv|libzahl|lil|robotfindskitten|tulipindicators|urlparser) mode=own;; esac
    docker run --rm --network none --memory 48g -v $R/in2:/w/in2:ro -v $d:/w/out -v $R/bin/time-bionic:/opt/time:ro \
      -v $R/laertes-one2.sh:/w/laertes-one2.sh:ro aliasing-limits-oopsla23:final bash -lc "/w/laertes-one2.sh $mode $p" > $d/container.log 2>&1
  fi
  log "END $t $p t$k $(tr '\n' ' ' < $d/status 2>/dev/null) $(grep -h 'Elapsed' $d/time.txt 2>/dev/null | sed 's/.*: //')"
  # the window is checked again at the run's end: a run another lane overlapped is set aside and repeated (at most 5 times)
  if ! python3 $R/guard.py > $d/guard-at-end 2>&1; then
    local n=1; while [ -e $d.contaminated.$n ]; do n=$((n+1)); done
    mv $d $d.contaminated.$n; log "CONTAMINATED $t $p t$k ($(cat $d.contaminated.$n/guard-at-end)); repeat $n"
    [ $n -lt 5 ] && run $t $p $k
  fi
}
for p in $PROGS; do run laertes2 $p 1; done
for k in 2 3; do for p in $PROGS; do
  grep -q '^exit=0' $OUT/laertes2/$p/t1/status 2>/dev/null && grep -q '^done=[1-9]' $OUT/laertes2/$p/t1/status && run laertes2 $p $k
done; done
kill $SAMPLER
echo "$(date -u +%FT%TZ) analysis-fanout run END (relay 149 B): Laertes's tool timed on its inputs of record" >> $F
log "ALL DONE"
