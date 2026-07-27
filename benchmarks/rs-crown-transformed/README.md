# CROWN artifact outputs

This directory contains the unmodified outputs produced by the CROWN
artifact Docker image for the 20 programs in `benchmarks/rs-crown/`.
Each program contains emitted Rust plus CROWN's
`analysis_results/{ownership,statistics,mutability,fatness}.json`.

The program outputs are reference data and must not be reformatted or
edited. This README is the only agent-authored file; the user-provided
`evaluation.tsv` is additional immutable reference data.

## Artifact provenance

- CROWN artifact version: **TODO(user): provide the artifact version**
- Artifact DOI: **TODO(user): provide the DOI**
- Docker image tag: **TODO(user): provide the image tag**
- Docker image digest: **TODO(user): provide the immutable image digest**
- Exact artifact command:

  ```text
  TODO(user): provide the exact Docker/artifact command
  ```

- Artifact execution date: **TODO(user): provide the run date**
- Machine: **TODO(user): provide the machine/OS/architecture details**

## Official evaluation table

- File: `evaluation.tsv` (comma-separated despite the extension)
- Provenance: **user-extracted from the CROWN artifact**
- SHA-256:
  `7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7`

The 2026-07-27 integer-exact check reproduced all 20 declaration
`before` and `after` values in this table. The artifact outputs are
**paper-consistent AT THE DECLARATION METRIC**: all Table 2 declaration
reduction rates agree with the official table. Two source-level
differences are recorded separately, not reconciled: Table 2 lists
`buffer` as 38 declarations and 56 uses before transformation while the
official table lists 37 and 54 (both reductions remain 100%), and the paper
prose describes `rgba` declaration reduction as 100% while both Table 2 and
the official table report 83.3%. Pointer-use rates are paper-only context
and were not independently recounted.

## Local inventory

The reproducible syntax-aware inventory tool is
`crates/pointer_replacer/tools/crown_artifact_inventory/`. Its report and
five per-program CSVs are recorded under
`docs/agents/tasks/2026-07-27-crown-artifact-output-inventory.md`.

The inventory reads this directory and frozen `benchmarks/rs-crown/`
without modifying either data set.
