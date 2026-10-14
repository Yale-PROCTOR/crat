#!/bin/bash
# r146 conf: is wave-6o's 60s' validator report (151) filed? writes validator-state.json
set -u
O=scratch/analysis-fanout/r146/conf; DOCS=crat/docs
git -C $DOCS fetch -q origin || { echo "fetch failed"; exit 1; }
T=$(date -u +%FT%TZ)
L=$(git -C $DOCS ls-tree --name-only origin/main agents/reports/wave-6o/ | sed 's#.*/##' | sort | tail -1)
F=$(git -C $DOCS ls-tree --name-only origin/main agents/reports/wave-6o/ | grep -c '/151' || true)
python3 -c "import json,sys; json.dump({'filed': int(sys.argv[1])>0, 'last': sys.argv[2][:3], 'last_file': sys.argv[2], 'checked': sys.argv[3]}, open(sys.argv[4],'w'))" "$F" "$L" "$T" $O/validator-state.json
cat $O/validator-state.json; echo
