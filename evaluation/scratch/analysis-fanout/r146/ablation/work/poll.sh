#!/bin/bash
F=scratch/main/SLOT-FREE
for i in $(seq 1 52); do
  if grep -q "^main BATCH 60SP CENSUS ENDED" $F; then echo ENDED; exit 0; fi
  if grep -q "^main BATCH 60SP CENSUS STOPPED" $F; then echo STOPPED; exit 0; fi
  sleep 10
done
echo WAITING; date -u; tail -2 $F
