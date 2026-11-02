#!/usr/bin/env bash
# Reproduce the numbers of the paper. See README.md.
set -euo pipefail
cd "$(dirname "$0")"
export WORK="${WORK:-$PWD/work}"
echo "== 1. validator records (Tables V and VI)"
python3 scripts/check_validator.py
echo "== 2. counter over all repository states (Section II manifest, Table IV)"
python3 scripts/counter.py | tee results-counter.txt
echo "== 3. rebuild baseline and Claude Code endpoints, run Lean audits"
bash scripts/run_audit.sh
echo "== 4. recompute and check every reported number"
python3 scripts/analysis.py --work "$WORK" --check expected/expected.json
