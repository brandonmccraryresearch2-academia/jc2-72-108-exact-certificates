#!/usr/bin/env bash
# Restore Mathlib for the GGHV lake project after a VM reset.
# Mathlib itself is NOT a conda package (conda-forge has no Mathlib
# and its lean tops out at 4.33.0), so it is fetched by Lake into
# this project's .lake/ directory, which lives under ~/workspace
# (home persists across VM replacements; system root does not).
# This script re-runs exactly the steps that install it, so a
# reset costs one command, not a rebuild from memory:
#   1. lake update        (clone/checkout Mathlib v4.34.0 per lakefile.toml)
#   2. lake exe cache get (download prebuilt Mathlib oleans)
#   3. lake build         (build the GGHV lib, Parts 1-8)
set -euo pipefail
export PATH="$HOME/.elan/bin:$HOME/miniconda3/envs/jacobian-conjecture-2d/bin:$PATH"
cd "$(dirname "$0")"
lake update
lake exe cache get
lake build
echo "Mathlib + GGHV build restored."
