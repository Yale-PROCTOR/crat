#!/bin/bash
# run146.sh FRAME -- analysis-fanout r146 / census (relay 146): every census-side producer of r141/census, re-pointed.
#   FRAME=s39  : the CONTROL (main/batch58pps39 read BY THE EMITTED TREE = r146/census/cen-s39-tree (cp of r141's), the S39 cache
#                era5c-r211-s39pp); with build146.py s39 it must reproduce r141/census/staged.tsv value_58ppp.
#   FRAME=60sp : 60s' (main/batch60sp at 32d966b9f; ledger = tree, custody data=true, so the census itself is the tree reading;
#                era-5c's 60-KINDORDER cache era5c-r215-kindorder).
# Pure Python over census tables and the streamed / bounded-head cache products; no rustc / cargo / counter / driver.
set -u
F=${1:?FRAME}
W=scratch/analysis-fanout/r146/census/work
M=scratch/main
AW=dev/worktrees
case $F in
  s39)  CEN=$W/../cen-s39-tree; RAW=$M/batch58pps39; SOLVE=$AW/era5c-r211-s39pp; NAME=batch58pps39
        ROWS=$W/in141/rows-final-b58ppp.tsv; RMAIN=$W/in141/rows-batch58ppp-main.tsv
        QF=$W/../cache/qfacts/qfacts-s39.tsv; DELIV=2678; UNIV=4301; PREVC=$M/batch58pp; SNSOLVE=$AW/era5c-l01p14u-solve ;;
  60sp) CEN=$M/batch60sp; RAW=$M/batch60sp; SOLVE=$AW/era5c-r215-kindorder; NAME=batch60sp
        ROWS=$W/in146/rows-final-b60sp.tsv; RMAIN=$W/in146/rows-batch60sp-main.tsv
        QF=$W/../cache/qfacts/qfacts-60sp.tsv; DELIV=2715; UNIV=4530; PREVC=$W/../cen-s39-tree; SNSOLVE=$SOLVE ;;
  *) echo "FRAME?"; exit 2 ;;
esac
export FRAME=$F
O=$W/out146/$F; mkdir -p $O $O/rate $O/s17
FAT=$O/fatfacts-$F.tsv
cd $W
fail() { echo "FAIL $*" >> $O/run.status; }
step() { echo "$(date -u +%T) $*" >> $O/run.status; }
step start $F
awk -F'\t' 'NR>1 && $3==0 {print $1"\t"$2"\t"$4":"$5}' $QF > $FAT
python3 d6prod/p1_count_d6.py $CEN > $O/p1_count-d6.out || fail p1d6
python3 g088a/p1_count.py $CEN > $O/p1_count-old.out || fail p1old
python3 p141/d6_rate.py $CEN $O/rate > $O/rate-d6.log || fail rate
python3 d6prod/layers141.py $RAW - $O/layers-d6.tsv 2> $O/layers-d6.log || fail layers
python3 d6prod/strata_d6.py $CEN $SOLVE --out $O/strata-d6.tsv --rows $O/strata-rows-d6.tsv > $O/strata-d6.log 2>&1 || fail strata
python3 d6prod/rq5_forms_d6.py $CEN $ROWS --emitted-form $RMAIN $FAT > $O/forms-d6.out || fail forms
RQ5_FORMS_DUMP=$O/forms-dump.tsv python3 g088a/p4/cand/rq5_forms_ef.py $CEN $ROWS --emitted-form $RMAIN $FAT > $O/forms-ef.out || fail formsef
python3 g088a/p4/cand/cand.py $CEN $QF $O/forms-dump.tsv > $O/cand.out || fail cand
python3 g088a/pairhold/pending_hold_price.py $CEN $O/hold-price.tsv > $O/hold-price.txt || fail hold
python3 g088a/pairhold/raw_view_peers.py $CEN $O/hold-price.tsv $O/raw-view-peers.tsv > $O/raw-view-peers.txt || fail peers
python3 d6prod/clause_holds_d6.py $CEN $DELIV $UNIV $O/hold-price.tsv $O/raw-view-peers.tsv > $O/clause-holds-d6.txt || fail clause
python3 g088a/crown61.py $CEN > $O/crown61.out || fail crown61
python3 $M/crown_name_join.py $CEN $O/crown61.out > $O/crown-name-join.txt || fail crownjoin
python3 g088a/pairs_read.py $M/b55 $CEN g088a/era5c-144-the-24-pairs.tsv > $O/pairs-b55.txt || fail pairs55
python3 g088a/pairs_read.py $M/batch58 $CEN g088a/era5c-144-the-24-pairs.tsv > $O/pairs-batch58.txt || fail pairs58
python3 g088a/pairs_read.py $PREVC $CEN g088a/era5c-144-the-24-pairs.tsv > $O/pairs-prev.txt || fail pairsprev
python3 n141/famdiff141.py $M/b55 $CEN > $O/famdiff-vs-b55.out || fail famdiff55
python3 n141/famdiff141.py $M/batch58 $CEN > $O/famdiff-vs-batch58.out || fail famdiff58
python3 n141/famdiff141.py $PREVC $CEN > $O/famdiff-vs-prev.out || fail famdiffprev
if [ $F = 60sp ]; then python3 n141/famdiff141.py $M/b55 $M/batch60 > $O/famdiff-b55-vs-batch60.out || fail famdiff6055; python3 n141/famdiff141.py $M/batch60 $CEN > $O/famdiff-batch60-vs-60sp.out || fail famdiff6060; fi
python3 n141/ident141.py $M/batch58 $CEN > $O/ident-vs-batch58.out || fail ident58
python3 n141/ident141.py $PREVC $CEN > $O/ident-vs-prev.out || fail identprev
python3 n141/ownpref141.py $F > $O/ownpref.out || fail ownpref
python3 g088b/rq5/pair_table.py $CEN > $O/pair-table.out || fail pairtable
python3 g088b/rq5/verify_frame13.py $CEN > $O/verify.out || fail verify
python3 n141/premise_bd141.py $M/batch58 $CEN > $O/premise-bd-vs-batch58.out || fail p7a
python3 n141/premise_bd141.py $PREVC $CEN > $O/premise-bd-vs-prev.out || fail p7b
python3 g088b/p7/optview.py $CEN > $O/optview.out || fail optview
python3 g088b/p7/optview_split.py $CEN > $O/optview-split.out || fail optsplit
python3 n141/cv_rows141.py $M/batch58 $CEN > $O/cv-rows-vs-batch58.out || fail cv58
python3 n141/cv_rows141.py $PREVC $CEN > $O/cv-rows-vs-prev.out || fail cvprev
python3 n141/cvformals146.py $PREVC $CEN > $O/cvformals-vs-prev.out || fail cvformals
python3 alloc_contract_r140.py $CEN > $O/alloc-contract.out || fail alloc
python3 g088b/raw_twin.py batch58 $NAME > $O/raw-twin.out || fail rawtwin
python3 p141/owning_params_58pp.py $CEN > $O/owning-params.out || fail owning
( cd $O/s17 && rm -f decl-*.txt && python3 $W/p141/premise_join.py > join.out ) || fail s17
python3 p141/seed_g5.py $CEN $SOLVE --out $O/seed-g5.tsv > $O/seed-g5.log 2>&1 || fail seedg5
python3 g088a/p4/g5/seed_numbers.py --census $CEN --label "r146 $F" --solve $SNSOLVE --record $W/g088a/p4/g5/record-copy.r146.md --dry-run > $O/seed_numbers.out 2> $O/seed_numbers.err || fail seednumbers
python3 n141/leak141.py $CEN > $O/leak.out || fail leak
python3 n141/rq3times146.py $SNSOLVE > $O/rq3times.tsv || fail rq3times
python3 g088b/ec/ec3_keys.py $RAW > $O/ec3.txt || fail ec3
[ "$(md5sum < $W/g088a/p4/g5/record-copy.r146.md | cut -c1-32)" = "$(cut -c1-32 $W/g088a/p4/g5/record-copy.r146.md5)" ] || fail record-copy-changed
step end $F
