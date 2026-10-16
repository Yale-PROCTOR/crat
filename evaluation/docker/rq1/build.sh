#!/bin/bash
# Builds rq1's two counters into rq1/target/release (RQ1_TARGET overrides the target directory):
#   typed_counter  the typed pointer-position counter, a rustc driver on nightly-2025-06-23 (needs rustc-dev)
#   decl_counter   CROWN's declaration counter (syn / quote / proc-macro2 / serde_json from crates.io)
# Run once when the image is built (crates.io reachable); rq1/run.sh calls it when a binary is missing.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
T=${RQ1_TARGET:-$HERE/target}
for c in typed decl; do
  cargo +nightly-2025-06-23 build --release --locked --quiet --manifest-path "$HERE/counters/$c/Cargo.toml" --target-dir "$T"
done
ls -l "$T/release/typed_counter" "$T/release/decl_counter"
