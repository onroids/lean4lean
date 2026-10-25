#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
python3 research/check_sources.py
lake build Lean4Lean.Research
lake env lean research/AxiomAudit.lean
