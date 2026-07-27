# CROWN artifact outputs

This directory contains the unmodified outputs produced by the CROWN
artifact Docker image for the 20 programs in `benchmarks/rs-crown/`.
Each program contains emitted Rust plus CROWN's
`analysis_results/{ownership,statistics,mutability,fatness}.json`.

The program outputs are reference data and must not be reformatted or
edited. This README is the only added file.

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

## Local inventory

The reproducible syntax-aware inventory tool is
`crates/pointer_replacer/tools/crown_artifact_inventory/`. Its report and
three per-program CSVs are recorded under
`docs/agents/tasks/2026-07-27-crown-artifact-output-inventory.md`.

The inventory reads this directory and frozen `benchmarks/rs-crown/`
without modifying either data set.
