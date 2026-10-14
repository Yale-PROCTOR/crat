#!/bin/bash
# r146/trees: the pure-Python producers over the counter / driver outputs, control (58''' = batch58pps39) then 60s' (batch60sp).
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
T=scratch/analysis-fanout/r146/trees
M=scratch/main
TOOLS=tmp/scratchpad/wt067/agents/tools/rq2
# t4: summarize, seed_pos, stage
for d in out-ours-58pps39 out-ours-60sp; do
  python3 $T/t4/run_nobuild.py summarize --out $T/t4/$d > $T/t4/$d/summarize.out
  python3 $TOOLS/seed_pos.py --out $T/t4/$d > $T/t4/$d/seed_pos.out
  OUTSUB=$d python3 $T/t4/build_stage.py > $T/t4/$d/build_stage.stdout
done
# t5: seed + as emitted
OURS=ours58pps39 python3 $T/t5/seed_t5.py > $T/t5/ours58pps39-seed.out
OURS=ours60sp python3 $T/t5/seed_t5.py > $T/t5/ours60sp-seed.out
python3 $T/t5/as_emitted.py ours58pps39 > $T/t5/as-emitted.out
python3 $T/t5/as_emitted.py ours60sp > $T/t5/as-emitted-60sp.out
# r118 (strict alldecl; feeds t4r945's control assertion)
for pair in b58pps39:out-ours-58pps39 b60sp:out-ours-60sp; do
  h=${pair%%:*}; o=${pair#*:}
  mkdir -p $T/r118/$h
  HERE=$T/r118/$h OURSDIR=$T/t4/$o/ours python3 $T/r118/alldecl.py > $T/r118/$h/alldecl.out
  (cd $T/r118/$h && python3 $T/r118/build_stage.py > $T/r118/$h/build_stage.out)
done
# t4r945
OURSDIR=$T/t4/out-ours-58pps39/ours TREES=$M/batch58pps39/emitted-trees CTL_DECLS=$T/r118/b58pps39/decls python3 $T/t4r945/alldecl945.py > $T/t4r945/alldecl945.out
python3 $T/t4r945/table945.py > $T/t4r945/table945.out
OURSDIR=$T/t4/out-ours-60sp/ours TREES=$M/batch60sp/emitted-trees CTL_DECLS=$T/r118/b60sp/decls python3 $T/t4r945-60sp/alldecl945.py > $T/t4r945-60sp/alldecl945.out
python3 $T/t4r945-60sp/table945.py > $T/t4r945-60sp/table945.out
# t5r945
for d in t5r945 t5r945-60sp; do
  python3 $T/$d/code/compute.py > $T/$d/compute.out
  python3 $T/$d/code/keys.py > $T/$d/keys.out
done
# twin decl-uses
python3 $T/twin/decl_uses_twin.py ours58pps39 > $T/twin/du-ours58pps39.tsv
python3 $T/twin/decl_uses_twin.py ours60sp > $T/twin/du-ours60sp.tsv
# own
for d in own own-60sp; do
  python3 $T/$d/scripts/own_scan.py > $T/$d/own_scan.stdout
  python3 $T/$d/scripts/examples.py > $T/$d/examples.stdout
  python3 $T/$d/scripts/vec_check.py > $T/$d/vec_check.stdout
done
# ties (R945-1)
python3 $T/ties/ties945.py $T/t5r945 $T/ties/out945-58pps39 > /dev/null
python3 $T/ties/ties945.py $T/t5r945-60sp $T/ties/out945-60sp > /dev/null
echo PY DONE
