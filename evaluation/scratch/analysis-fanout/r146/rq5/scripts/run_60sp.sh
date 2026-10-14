#!/usr/bin/env bash
# r146 group rq5: the re-pointed producers on main/batch60sp (60s', head 32d966b9f, the 60-KINDORDER cache's fatness file
# streamed by run_qfacts.sh), then the control (run_control_58ppp.sh + build_staged_60sp.py control) and the stage. Fails closed.
set -euo pipefail
cd "$(dirname "$0")/.."
C=scratch/main/batch60sp
B=scratch/analysis-fanout/r141/rq5/out/rq5-rows-58ppp.tsv
X=out60sp
python3 docsx/agents/tools/rq5_columns.py $C --rows $X/rows-batch60sp-main.tsv > $X/cols-batch60sp.out
python3 scripts/rq5_cause_map.py $X/rows-batch60sp-main.tsv $X/map60sp $C > $X/map60sp.out
python3 scripts/audit_rowlevel.py --base $B --census $C --out $X --cols $X/rows-batch60sp-main.tsv --map $X/map60sp --tag 60sp --n-base 1623 --n-rows 1815 --prev 58ppp --cur 60sp --tree-custody > $X/audit-60sp.out
python3 scripts/check_unchanged.py $C $X/rq5-rows-60sp.tsv > $X/check-unchanged-60sp.out
python3 scripts/rq5_forms_tree.py $C $X/rows-final-b60sp.tsv --emitted-form $X/rows-batch60sp-main.tsv $X/qfacts-60sp.tsv.fat --tree-custody > $X/forms-60sp-rowlevel.out
python3 scripts/rq5_forms_tree.py $C $X/rows-final-b60sp.tsv --emitted-form $X/rows-batch60sp-main.tsv $X/qfacts-60sp.tsv.fat > $X/forms-60sp-ledger.out
python3 scripts/verify_tree.py $C --tree-custody > $X/verify-batch60sp.out
python3 scripts/verify_tree.py $C | head -3 > $X/verify-batch60sp.ledger.out
python3 scripts/reverted_split.py $C brotli tulipindicators quadtree libzahl > $X/reverted-split-60sp.out
python3 scripts/d6_rate.py $C $X/rate 4530 2715 --tree-custody > $X/rate-60sp.log
python3 scripts/form_fact_join.py $X/rq5-rows-60sp.tsv 60sp $X/form-fact-60sp.tsv > /dev/null
cmp $X/qfacts-60sp.tsv.fat scratch/analysis-fanout/r141/rq5/out/qfacts-s39.tsv.fat && echo "fatness 60s' = S39 byte for byte"
scripts/run_control_58ppp.sh > ctl58ppp/controls.out
tail -1 ctl58ppp/controls.out
python3 scripts/build_staged_60sp.py control
python3 scripts/build_staged_60sp.py stage
