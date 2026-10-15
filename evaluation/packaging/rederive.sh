#!/bin/bash
# Re-derive the submission source zip from a borrow-ownership head (crat-packaging relays 001-008). See README.md.
# usage: rederive.sh <head> <tag>
#   <tag> names the derivation branch (rederive-<tag>), its worktree and the scratch directory.
# Environment (all optional):
#   REPO               the repository (default: the one containing this script)
#   SCRATCH            work directory: logs, build targets, the zip (default: $REPO/target/packaging/<tag>)
#   WORKTREES          where the derivation worktree is created (default: $SCRATCH/worktrees)
#   TOOLS_TARGET       cargo target of the two helper binaries under tools/ (default: $SCRATCH/tools-target)
#   CARGO              the cargo command (default: cargo). The solver and libclang variables the top-level README
#                      names must be in the environment, as for any build of the repository.
#   ENVREL             the environment of record, relative to the head (default: the final frame's env file)
#   IDENTITY_PATTERNS  the identity grep (grep -E, case-insensitive) that must be empty before the zip; the default
#                      covers paths and services, the operator adds the names of the authors and of the hosts.
set -u
HEAD=${1:?head}; TAG=${2:?tag}
P=$(cd "$(dirname "$0")" && pwd)
REPO=${REPO:-$(git -C "$P" rev-parse --show-toplevel)}
SCRATCH=${SCRATCH:-$REPO/target/packaging/$TAG}; ZS=$SCRATCH
WORKTREES=${WORKTREES:-$SCRATCH/worktrees}; W=$WORKTREES/rederive-$TAG
TOOLS_TARGET=${TOOLS_TARGET:-$SCRATCH/tools-target}; TOOLS=$TOOLS_TARGET/release
CARGO=${CARGO:-cargo}
ENVREL=${ENVREL:-crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh}
IDENTITY_PATTERNS=${IDENTITY_PATTERNS:-'/home/|agent-worktrees|anthropic|claude|codex|openai|github\.com|Co-Authored'}
SR=$(rustup run nightly-2025-06-23 rustc --print sysroot); export LD_LIBRARY_PATH=$SR/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
export W ZS KEPT=$ZS/kept-rs-files.txt ORPHANS=$ZS/orphans.txt CARGO_INCREMENTAL=0
mkdir -p $ZS $WORKTREES; rm -rf $ZS/stage $ZS/unzipped $ZS/tok; log=$ZS/rederive.log; : > $log; exec > >(tee -a $log) 2>&1
echo "START $(date -u +%FT%TZ) head=$HEAD tag=$TAG env=$ENVREL repo=$REPO scratch=$ZS"
step() { echo "== $(date -u +%T) $*"; }
commit() { git -C $W add -A >/dev/null; git -C $W -c user.name=submission -c user.email=submission@localhost commit -q -m "$1" && echo "   commit $(git -C $W rev-parse --short=9 HEAD): $1"; }
build() { local label=$1 dir=$2; shift 2; echo "   build $label: $CARGO build --release --manifest-path $dir/Cargo.toml $* (target $CARGO_TARGET_DIR)"; $CARGO build --release --manifest-path $dir/Cargo.toml "$@" > $ZS/build-$label.log 2>&1; local rc=$?; echo "   build $label END $(date -u +%FT%TZ) rc=$rc"; return $rc; }

step "0 the helper binaries (cfgcut, rslex)"
if [ ! -x $TOOLS/cfgcut ] || [ ! -x $TOOLS/rslex ]; then export CARGO_TARGET_DIR=$TOOLS_TARGET; build tools $P/tools || { echo "the tools do not build: $ZS/build-tools.log"; exit 1; }; fi
echo "   $TOOLS/cfgcut, $TOOLS/rslex"

step "1 worktree"
git -C $REPO worktree remove --force $W 2>/dev/null; [ -d $W ] && rm -rf $W; git -C $REPO branch -D rederive-$TAG 2>/dev/null
git -C $REPO worktree add $W -b rederive-$TAG $HEAD >/dev/null 2>&1 || { echo "worktree failed"; exit 1; }
echo "   base tree $(git -C $W rev-parse $HEAD^{tree}) files $(git -C $W ls-files | wc -l)"
[ -f $W/$ENVREL ] || { echo "env of record $ENVREL absent"; exit 1; }
mkdir -p $W/config; grep -E '^export ' $W/$ENVREL | sed -E 's/[[:space:]]+#.*$//' | grep -v -E '^export (SYSROOT|LD_LIBRARY_PATH|TMPDIR)=' > $ZS/env-exports.txt
{ echo '#!/bin/bash'; cat $ZS/env-exports.txt; echo 'export SYSROOT="$(rustc --print sysroot)"'; echo 'export LD_LIBRARY_PATH="$SYSROOT/lib:$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"'; } > $W/config/analysis-env.sh; chmod +x $W/config/analysis-env.sh
echo "   config/analysis-env.sh: $(grep -c '^export' $W/config/analysis-env.sh) exports from $ENVREL"

step "2 removals (001 s2, 002 item 1, 003, 004, 005 s1; evaluation/packaging = this pipeline, which carries the identity list and the rename map)"
for p in .compound-engineering .github .gitignore .claudignore CLAUDE.md AGENTS.md .claude .codex .vscode M0-KNOWN-DEFECTS.md README.md LICENSE benchmarks tool.py rustfmt.toml examples crates/pointer_replacer/frames crates/pointer_replacer/tools crates/finders crates/io_replacer crates/merger crates/outparam_replacer crates/static_replacer crates/union_replacer src/bin/crat-finder.rs src/bin/crat-merge.rs crat-finder crat-merge crates/passes/src/bin_file_adder.rs crates/passes/src/enum_replacer crates/passes/src/formatter.rs crates/passes/src/interface_fixer.rs crates/passes/src/libc_replacer crates/passes/src/simplifier crates/passes/src/simplifier.rs crates/passes/src/splitter.rs crates/passes/src/unexpander.rs crates/passes/src/unsafe_resolver crates/utils/src/bit_set.rs crates/utils/src/unsafety.rs evaluation/packaging; do [ -e $W/$p ] && git -C $W rm -r -q -f -- $p; done
find $W/crates $W/src -type f \( -name '*_tests.rs' -o -name 'tests.rs' -o -name 'test_*.py' \) -print0 | xargs -0 -r git -C $W rm -q -f --
find $W/crates $W/src -type d -name tests -print0 | xargs -0 -r git -C $W rm -r -q -f --
python3 - <<'PY'
import os, re
W=os.environ['W']
p=W+'/crates/passes/src/lib.rs'; s=open(p).read()
s=''.join(l for l in s.splitlines(True) if not (l.startswith('pub mod ') and l.strip() not in ('pub mod expander;','pub mod extern_resolver;','pub mod preprocessor;')))
open(p,'w').write(s)
p=W+'/crates/utils/src/lib.rs'; s=open(p).read(); s=s.replace('pub mod bit_set;\n','').replace('pub mod unsafety;\n',''); open(p,'w').write(s)
p=W+'/Cargo.toml'; s=open(p).read()
for m in ['finders','io_replacer','merger','outparam_replacer','static_replacer','union_replacer']:
    s=s.replace(f'  "crates/{m}",\n','').replace(f'{m} = {{ path = "crates/{m}" }}\n','')
s=re.sub(r'exclude = \["deps_crate", "examples"\]','exclude = ["deps_crate"]',s)
open(p,'w').write(s)
for root,_,files in os.walk(W+'/crates'):
    for f in files:
        if f=='Cargo.toml':
            p=os.path.join(root,f); s=open(p).read(); n=re.sub(r'\n\[dev-dependencies\]\n(?:[^\[\n][^\n]*\n|\n)*?(?=\[|\Z)','\n',s)
            if n!=s: open(p,'w').write(n); print('   dev-dependencies removed:',p.replace(W+'/',''))
PY
python3 -I $P/option3.py
cp $P/driver-template.crat.rs $W/src/bin/crat.rs
cp $P/README-template.md $W/README.md
echo "   removed: $(git -C $W diff --cached --name-only --diff-filter=D | wc -l) tracked paths"
commit "Packaging A: removals, the trim, option 3 (the legacy rewriter out), the driver template, config and README"

step "3 cfg(test) cut + orphans"
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
$TOOLS/cfgcut $(cat $KEPT) > $ZS/cfgcut.tsv 2> $ZS/cfgcut.err; tail -1 $ZS/cfgcut.err
for i in 1 2 3; do python3 -I $P/reach.py > $ZS/reach-$i.txt; grep -E '^UNRESOLVED' $ZS/reach-$i.txt | while read _ f name _; do sed -i -E "/^\s*(pub(\([a-z]+\))? )?mod $name;\s*$/d" $W/$f; echo "   unresolved mod $name removed from $f"; done; grep -q '^UNRESOLVED' $ZS/reach-$i.txt || break; done
head -1 $ZS/reach-$i.txt
sed "s#^#$W/#" $ORPHANS | xargs -r git -C $W rm -q -f -- 2>/dev/null; sed "s#^#$W/#" $ORPHANS | xargs -r rm -f --
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
for f in $(find $W/crates/*/src -type f ! -name '*.rs' ! -name 'Cargo.toml'); do b=$(basename $f); grep -q -l -F -- "$b" $(cat $KEPT) || { git -C $W rm -q -f -- $f 2>/dev/null || rm -f $f; echo "   unreferenced data file removed: ${f#$W/}"; }; done
find $W/crates $W/src -type d -empty -delete
python3 -I $P/reach.py | head -1
commit "Packaging B: the cfg(test) cut, unresolved test modules, orphans, unreferenced data"

step "4 comment strip"
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
$TOOLS/rslex strip $(cat $KEPT) > $ZS/strip-rs.tsv; awk -F'\t' '{f++; c+=$2} END {printf "   rs files=%d comments_removed=%d\n", f, c}' $ZS/strip-rs.tsv
python3 -I $P/strip_misc.py toml $W/Cargo.toml $W/crates/*/Cargo.toml $W/deps_crate/Cargo.toml $W/deps_crate/Cargo.lock > $ZS/strip-toml.tsv; awk -F'\t' '{c+=$2} END {printf "   toml comments_removed=%d\n", c}' $ZS/strip-toml.tsv
commit "Packaging C: the comment strip"

step "5 rename crat -> jobcrat (rules 1-6, the kit included) + file moves"
python3 -I $P/rename.py apply > $ZS/rename-map.tsv 2> $ZS/rename-map.err; grep '#COUNTS' $ZS/rename-map.err
echo "   in evaluation/: $(grep -c '^evaluation/' $ZS/rename-map.tsv) occurrences in $(cut -f1 $ZS/rename-map.tsv | grep '^evaluation/' | sort -u | wc -l) files"
git -C $W mv src/bin/crat.rs src/bin/jobcrat.rs; git -C $W mv crat jobcrat
commit "Packaging D: the rename"

step "6 string edits (001 s4, 003, 005), the kit copy's edits (007), lint reasons"
python3 -I $P/edits.py | tee $ZS/edits.txt | tail -3
python3 -I $P/kit_edits.py | tee $ZS/kit-edits.txt | tail -1
git -C $W grep -l -E 'reason\s*=\s*"' -- '*.rs' | sort > $ZS/reason-files.txt; python3 -I $P/strip_reasons.py $ZS/reason-files.txt > $ZS/reasons-deleted.tsv 2> $ZS/reasons.err; cat $ZS/reasons.err
commit "Packaging E: the string edits, the kit copy's edits and the lint reasons"

step "7 build, lock, checks"
export CARGO_TARGET_DIR=$ZS/target; build derived $W || { echo "the derived tree does not build: $ZS/build-derived.log"; tail -30 $ZS/build-derived.log; exit 1; }
python3 -I $P/strip_misc.py toml $W/Cargo.lock > /dev/null; git -C $W add -A; git -C $W -c user.name=submission -c user.email=submission@localhost commit -q -m "Packaging F: the lockfile as cargo resolved it, header stripped" 2>/dev/null && echo "   lock committed"
echo "   TREE $(git -C $W rev-parse HEAD^{tree}) files $(git -C $W ls-files | wc -l)"
echo "   crat word: $(git -C $W grep -n -w -e crat -- . | wc -l); bCRAT_: $(git -C $W grep -n -P '\bCRAT_' -- . | wc -l); __crat_: $(git -C $W grep -n -e '__crat_' -e '__CRAT_' -- . | wc -l); Crat: $(git -C $W grep -n -w -e Crat -- . | wc -l)"
echo "   identity grep (minus the registry URL in lockfiles): $(git -C $W grep -n -i -E -e "$IDENTITY_PATTERNS" -- . | grep -v -F 'registry+https://github.com/rust-lang/crates.io-index' | wc -l)"
echo "   fingerprints: $(git -C $W grep -n -E -e '@2026-|"r[0-9]{3}-|"s23-|s23-force|r385-force|wave5p|era5c-l01p14|-PORT subset tripwire|addendum|user ruling|\bR[0-9]{3,4}-[0-9]\b' -- '*.rs' ':!evaluation' | wc -l); reason attrs: $(git -C $W grep -n -E '^\s*reason\s*=\s*"' -- '*.rs' ':!evaluation' | wc -l); cfg(test): $(git -C $W grep -n -E '#\!?\[cfg\(test\)\]|^\s*#\[test\]' -- '*.rs' ':!evaluation' | wc -l)"
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT; echo "   comments left: $($TOOLS/rslex count $(cat $KEPT) | awk -F'\t' '{c+=$2} END {print c}')"
rm -rf $ZS/tok; mkdir -p $ZS/tok; for f in $(cat $KEPT); do $TOOLS/rslex dump "$f" > "$ZS/tok/$(echo ${f#$W/} | tr '/' '_')"; done
echo "   list-2 in literals: $(cat $ZS/tok/* | grep -E '^Literal' | grep -i -w -E -c 'seat|relay|lane|wave|era5|batch|census'); comment markers in literals: $(cat $ZS/tok/* | grep -E '^Literal' | grep -c -E '\\n\s*(//|/\*)'); README internal words: $(grep -n -i -w -E 'expand|extern|preprocess|bo|wave|era5|census|crat' $W/README.md | wc -l)"
echo "   kit (evaluation/): files $(git -C $W ls-files -- evaluation | wc -l); bare CRAT words: $(git -C $W grep -n -w -e CRAT -- evaluation | wc -l); _CRAT suffix: $(git -C $W grep -n -P '_CRAT\b' -- evaluation | wc -l); list-2 word lines: $(git -C $W grep -n -i -w -E 'seat|relay|lane|wave|era5|batch|census' -- evaluation | wc -l); ruling ids: $(git -C $W grep -n -E '\bR[0-9]{3,4}-[0-9]\b|addendum|user ruling' -- evaluation | wc -l); old pass names: $(git -C $W grep -n -E -e '--pass[^|]*(expand|extern|preprocess|pointer|bo\b)|bo-env|bo-receipt' -- evaluation | wc -l)"

step "8 zip + from-zip build"
$P/mkzip.sh | tail -4
rm -rf $ZS/zip-target; export CARGO_TARGET_DIR=$ZS/zip-target; build from-zip $ZS/unzipped/jobcrat-source --locked || { echo "the zip does not build: $ZS/build-from-zip.log"; tail -30 $ZS/build-from-zip.log; exit 1; }
echo "ZIP $ZS/jobcrat-source.zip sha256=$(sha256sum $ZS/jobcrat-source.zip | cut -c1-64) bytes=$(stat -c %s $ZS/jobcrat-source.zip) entries=$(unzip -Z1 $ZS/jobcrat-source.zip | wc -l)"
echo "END $(date -u +%FT%TZ)"
