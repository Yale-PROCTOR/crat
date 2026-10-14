#!/bin/bash
# r146/trees: the binary runs (prebuilt typed counter r043 + decl driver r10; nothing built):
# control = main/batch58pps39 (58''', must reproduce r141/trees), then 60s' = main/batch60sp.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
T=scratch/analysis-fanout/r146/trees
M=scratch/main
SF=$M/SLOT-FREE
gate() { bash $T/gate.sh || { echo "GATE FAILED before $1"; exit 3; }; }
start() { gate "$1"; echo "$(date -u +%FT%TZ) analysis-fanout run START (relay 146): $1" >> $SF; }
end() { echo "$(date -u +%FT%TZ) analysis-fanout run END (relay 146): $1" >> $SF; }

W="trees group: typed counter rq2_pos_counter (prebuilt r043) t4+t5 ours side on main/batch58pps39 (control) and main/batch60sp (60s'), ~2 min"
start "$W"
for pair in "out-ours-58pps39:$M/batch58pps39" "out-ours-60sp:$M/batch60sp"; do
  d=${pair%%:*}; c=${pair#*:}
  python3 $T/t4/run_nobuild.py run --side ours --out $T/t4/$d --census $c > $T/t4/$d/run.stdout
done
python3 $T/t5/run_t5.py ours58pps39 > $T/t5/ours58pps39-run.stdout
python3 $T/t5/run_t5.py ours60sp > $T/t5/ours60sp-run.stdout
end "$W"

W="trees group: decl driver rq2_decl_driver (prebuilt r10) twin + strict ties on main/batch58pps39 (control) and main/batch60sp (60s'), ~2 min"
start "$W"
python3 $T/twin/decl_twin.py $M/batch58pps39 $T/twin/batch58pps39 > $T/twin/batch58pps39.log
python3 $T/twin/decl_twin.py $M/batch60sp $T/twin/batch60sp > $T/twin/batch60sp.log
python3 $T/ties/ties_decl.py $M/batch58pps39 --out $T/ties/out-batch58pps39 --label batch58pps39 > $T/ties/b58pps39.log
python3 $T/ties/ties_decl.py $M/batch60sp --out $T/ties/out-batch60sp --label batch60sp > $T/ties/b60sp.log
end "$W"
echo BINS DONE
