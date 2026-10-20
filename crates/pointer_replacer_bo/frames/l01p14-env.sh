#!/bin/bash
# R517-2(2): the COMPLETE environment of the L01¹⁴ solve (R545-1/R545-2), on disk, beside the
# cache directory, written before any worker starts. main's census recipe reads
# the identity variables from here by name.
#
# Provenance, corrected per R519-9 (report 035b §1): the L01⁵ solve is
# `agent-worktrees/era5c-l015-night-solve`, launch digest
#   88052ad34ad6744216b2429e5811aeda19522cb418f32d5dd3f469f4e8e8a01c
# (identical in all 20 of its jobs; matches main 069c's worker-record read),
# semantic analysis `deff5e92…`, configuration `e16f23c7…`. Report 035 §2 read
# `era5c-l01pppp-night-solve` instead -- that is the L01⁗ solve, digest
# `c0018b363f2a…`. Both of 035 §2's findings survive on the right worktree.
#
# Every L01⁵ job JSON carries an `environment` block of 22 variables, so the
# premise that "the L01⁵ solve recorded no environment anywhere" is not right.
# This file is additive -- a second, shell-shaped copy in one place -- and the
# per-job blocks stay authoritative.
#
# The L01⁶ launch digest is the sha256 of THIS solve's launch-manifest.json and
# is written into each job's environment as CRAT_ERA5_LAUNCH_DIGEST when the
# manifest is generated, exactly as the L01⁵ worker records did. main's
# `check-frame-configuration.py <frame> <solve>` is the instrument that checks
# it before `l01p6`.
#
# The identity-bearing variables are the ones `solver_identity` reads. Every one
# of them is now IN the identity (R517-2(1)); before this frame,
# CRAT_ERA5C_FIELD_MOVE and CRAT_ERA5C_LEAK_PARITY were not.

# --- era-5b licensing arms (unchanged from L01⁵) ---
export CRAT_ERA5B_PASS=joint
export CRAT_ERA5B_INTERFACE_OWN=on
export CRAT_ERA5B_RETURN_PORT=on

# --- era-5c arms ---
export CRAT_ERA5C_MOVE_TRACKING=on          # L01⁗, unchanged
export CRAT_ERA5C_ALLOCATOR_CONTRACT=off    # L01¹³ off (a control, not the frame)
export CRAT_ERA5C_FIELD_MOVE=on              # L01⁷: R538-1, decided in era-5c report 041
                                            #   ABSENT in all 20 L01⁵ jobs, and
                                            #   absent = off (fail-loud default)
export CRAT_ERA5C_LEAK_PARITY=on            # L01⁵ (i)  -- ON FOR THE FIRST TIME
export CRAT_ERA5C_FINALIZE_SOFT=off         # R518-2 arm 3 -- premise refuted (035 §5)
export CRAT_ERA5C_MUT_MODEL=on              # L01⁸ R545-1: a table's reborrow is unique only under a written Ref level (047)
export CRAT_ERA5C_LEND_FORMAL=off            # L01⁸ R545-2 lend formals (047); 049: loses Ref on lodepng
export CRAT_ERA5C_DEREF_READER=on         # L01⁹ 1b (056, R565-3)
export CRAT_ERA5C_FIELD_OWN_REPAIR=on     # L01⁹ 1b's companion (056)
export CRAT_ERA5C_ORIGIN_SET=on           # L01⁹ 1a′ (057)
export CRAT_ERA5C_MOVED_INPUT=on          # L01⁹ 2′ (058, R568-4)
export CRAT_ERA5C_MOVE_STORE=on           # L01⁹ wall 4 (061, R574-5; the record reviewed)
export CRAT_ERA5C_NULL_EXIT=off           # off until the lend (R565-3 (a))
export CRAT_ERA5C_EXIT_CLOSE=off          # off until the lend
export CRAT_ERA5C_DEAD_JOIN=off           # a measurement (056 §4)
export CRAT_ERA5C_OWN_NAMED=off           # arm 3, a measurement
export CRAT_ERA5C_REF_WEIGHT_NAMED=off    # a measurement (056 §5)
export CRAT_ERA5C_COPY_LEND=on            # L01¹⁴: the A12 arm with the R804-1 guard (era-5c 133/134)
export CRAT_ERA5C_LEND=on                 # L01¹⁰ the lend (R590-5, record 2026-09-27-lend-interior-window)
export CRAT_ERA5C_TYPED_RELEASE=on        # L01¹⁰ (β), TypedReleaseDiscipline ADOPTED (R604-1)
export CRAT_ERA5C_ARG_ORDER=on            # L01¹⁰ R609-3 (a), the argument-order premise (the rewriter's hoist: record §9)
export CRAT_ERA5C_OVERLAP_TYPE_ROUTE=on   # L01¹⁰ R609-3 (b), the A5 type route under R542
export CRAT_ERA5C_RAW_CAUSE_LEDGER=on     # R607-1 the raw-cause ledger: a sidecar, not a model input (not in the identity)
export CRAT_ERA5C_RAW_CAUSE_BUDGET_S=3600 # R631-6 its per-program query budget
export CRAT_ERA5C_REF_PEEL_ZERO=on        # L01¹¹ the zero law at the by-reference boundary (R645-2)
export CRAT_ERA5C_RETIRE_FRESH=on         # L01¹¹ (γ) fresh-in-route (R659-1)
export CRAT_ERA5C_RETIRE_ROUTE_USE=on     # L01¹¹ (α⁺) the post-release use along the route (R659-1)
export CRAT_ERA5C_TYPED_SOLE=on           # L01¹¹ (β′) the containment refusal sharpened within R604 (R659-1)
export CRAT_ERA5C_ALPHA_RETURNS=on        # L01¹¹ (α) needs the route below to return (R666-1)
export CRAT_ERA5C_REALLOC_REFUTE=on       # L01¹² (α)'s refuted realloc-null branch (R677-4)
export CRAT_ERA5C_REALLOC_NONZERO=on      # L01¹² the zero-size realloc premise, provisional (R682-3; receipted premise=realloc-nonzero)
export CRAT_ERA5C_OWN_PREFER_LOCAL=on       # lever (b), FIXED at acc4edcdb (R536-4): never on a caller-derived value
export CRAT_ERA5C_RESEAT_A1=on              # narrow A1 (ab7050810): local-callee re-seats
export CRAT_ERA5C_TRAVERSAL_REF=off         # L01⁶ A2 -- NOT BUILT (report 035 §5)

# --- solver configuration (unchanged from L01⁵) ---
export CRAT_BO_A2_MODE=off
export CRAT_BO_A5_ATTESTATION=frozen_benchmark_graph
export CRAT_BO_FORK_ENGINE=fork
export CRAT_BO_L2_GUARDED_COMMITS=0
export CRAT_BO_REPAIR=guarded          # L01¹² the guarded repair (R617-1, R677-4)
export CRAT_BO_SAFE_MONO=per_site
export CRAT_NB4R_ROUTING=on

# --- toolchain / host (unchanged from L01⁵) ---
export RUSTUP_TOOLCHAIN=nightly-2025-06-23-x86_64-unknown-linux-gnu
export SYSROOT=/home/p51lee/.rustup/toolchains/nightly-2025-06-23-x86_64-unknown-linux-gnu
export LD_LIBRARY_PATH=$SYSROOT/lib:$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/lib:/home/p51lee/.local/opt/z3-solver-4.15.4.0/z3/lib
export TMPDIR=/home/p51lee/dev/agent-worktrees/era5c-l01p14-restored-solve/temp
export CRAT_ERA5_EXECUTION_ROLE=derive
export CRAT_ERA5_TOOLCHAIN_DIGEST=6735e704a73322e53cb1232d13385c3d34cf74df769eb40dba88a5eeac8bf951
export CRAT_ERA5_DEPENDENCY_DIGEST=a69f265575ecd9b6ee35fde64f4f36e5c766f59cd743d68c343abad5ce987a51

# NOT set here, because they are per program and the job JSON supplies them:
#   CRAT_ERA5_PROGRAM, CRAT_ERA5_INPUT_ROOT, CRAT_ERA5_LAUNCH_DIGEST, DIR
