#!/usr/bin/env bash
# r146 group rq5 CONTROL: every re-pointed producer on main/batch58pps39 (58''', the S39 cache's fatness file streamed by
# run_qfacts.sh) against r141/rq5/out (byte comparisons); fails closed.
set -euo pipefail
cd "$(dirname "$0")/.."
C=scratch/main/batch58pps39
P=scratch/analysis-fanout/r141/rq5/out
B=scratch/analysis-fanout/r141/rq5/prev58pp/out/rq5-rows-58pp.tsv
X=ctl58ppp
FAT=${FAT:-$X/qfacts-s39.tsv.fat}
# okp: identical up to this group's own directory name in a printed path (r146/rq5 vs r141/rq5)
okp() { if cmp -s <(sed "s#/r146/rq5/#/r141/rq5/#g" "$1") "$2"; then echo "IDENT(path) $1 = $2"; else echo "DIFFER $1 vs $2"; exit 1; fi; }
ok() { if cmp -s "$1" "$2"; then echo "IDENT $1 = $2"; else echo "DIFFER $1 vs $2"; exit 1; fi; }
python3 docsx/agents/tools/rq5_columns.py $C --rows $X/rows-batch58ppp-main.tsv > $X/cols-batch58ppp.out
ok $X/rows-batch58ppp-main.tsv $P/rows-batch58ppp-main.tsv; okp $X/cols-batch58ppp.out $P/cols-batch58ppp.out
python3 scripts/rq5_cause_map.py $X/rows-batch58ppp-main.tsv $X/map58ppp $C > $X/map58ppp.out
for f in label-defaults.tsv rows.tsv totals.tsv; do ok $X/map58ppp/$f $P/map58ppp/$f; done
ok $X/map58ppp.out $P/map58ppp.out
python3 scripts/audit_rowlevel.py --base $B --census $C --out $X --cols $X/rows-batch58ppp-main.tsv --map $X/map58ppp --tag 58ppp --n-base 1623 --n-rows 1623 --prev 58pp --cur 58ppp --tree-custody > $X/audit-58ppp.out
for f in rq5-rows-58ppp.tsv rows-final-b58ppp.tsv totals-b58ppp.tsv label-map-58ppp.tsv left-b58ppp.tsv audit-58ppp.out; do ok $X/$f $P/$f; done
python3 scripts/check_unchanged.py $C $X/rq5-rows-58ppp.tsv > $X/check-unchanged-58ppp.out
ok $X/check-unchanged-58ppp.out $P/check-unchanged-58ppp.out
python3 scripts/rq5_forms_tree.py $C $X/rows-final-b58ppp.tsv --emitted-form $X/rows-batch58ppp-main.tsv $FAT --tree-custody > $X/forms-58ppp-rowlevel.out
ok $X/forms-58ppp-rowlevel.out $P/forms-58ppp-rowlevel.out
python3 scripts/rq5_forms_tree.py $C $X/rows-final-b58ppp.tsv --emitted-form $X/rows-batch58ppp-main.tsv $FAT > $X/forms-58ppp-ledger.out
ok $X/forms-58ppp-ledger.out $P/forms-58ppp-ledger.out
python3 scripts/verify_tree.py $C --tree-custody > $X/verify-batch58ppp.out
ok $X/verify-batch58ppp.out $P/verify-batch58ppp.out
python3 scripts/verify_tree.py $C | head -3 > $X/verify-batch58ppp.ledger.out
ok $X/verify-batch58ppp.ledger.out $P/verify-batch58ppp.ledger.out
python3 scripts/reverted_split.py $C brotli tulipindicators quadtree libzahl > $X/reverted-split-58ppp.out
ok $X/reverted-split-58ppp.out $P/reverted-split-58ppp.out
python3 scripts/d6_rate.py $C $X/rate 4301 2678 --tree-custody > $X/rate-58ppp.log
ok $X/rate-58ppp.log $P/rate-58ppp.log; ok $X/rate/holds.tsv $P/rate/holds.tsv; ok $X/rate/rate.tsv $P/rate/rate.tsv
python3 scripts/form_fact_join.py $X/rq5-rows-58ppp.tsv 58ppp $X/form-fact-58ppp.tsv > /dev/null
ok $X/form-fact-58ppp.tsv $P/form-fact-58ppp.tsv
echo CONTROL-PRODUCERS-OK
