#!/usr/bin/env bash
# r146 group rq5: stream the QualifierFacts of (1) the S39 cache (control: must equal r141/rq5/out/qfacts-s39.tsv{,.fat,.counts})
# and (2) era-5c's 60-KINDORDER cache (60s'). Read only on the caches; 64 MiB chunks; MemAvailable >= 30 GiB guard in the script.
set -euo pipefail
cd "$(dirname "$0")/.."
M=scratch/main
python3 scripts/qfacts_stream2.py --manifest $M/batch58pps39-manifest.tsv worktrees/era5c-r211-s39pp/cache/era5b-model-cache-v1 ctl58ppp/qfacts-s39.tsv 2> ctl58ppp/qfacts-s39.log
for s in '' .fat .counts; do cmp ctl58ppp/qfacts-s39.tsv$s scratch/analysis-fanout/r141/rq5/out/qfacts-s39.tsv$s && echo "IDENT qfacts-s39.tsv$s"; done
cmp ctl58ppp/qfacts-s39.log scratch/analysis-fanout/r141/rq5/out/qfacts-s39.log && echo "IDENT qfacts-s39.log"
python3 scripts/qfacts_stream2.py --manifest $M/batch60sp-manifest.tsv worktrees/era5c-r215-kindorder/cache/era5b-model-cache-v1 out60sp/qfacts-60sp.tsv 2> out60sp/qfacts-60sp.log
echo QFACTS-DONE
