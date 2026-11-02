#!/usr/bin/env bash
# Rebuild the frozen baseline, the four Claude Code proving endpoints, and the
# repaired translation with
# Lean 4.29.1 and batteries, then run the Lean audit scripts.
#
# Environment:
#   LEAN       path to the lean binary of Lean 4.29.1 (default: lean on PATH)
#   BATTERIES  path to a checkout of batteries at 756e3321fd3b02a85ffda19fef789916223e578c
#   WORK       output directory (default: ./work)
#   JOBS       not used, builds are sequential
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
LEAN="${LEAN:-$(command -v lean)}"
BATTERIES="${BATTERIES:?set BATTERIES to a batteries checkout at commit 756e3321}"
WORK="${WORK:-$HERE/work}"
mkdir -p "$WORK"
echo "Lean: $("$LEAN" --version)"

build () {   # build <commit>
  local c="$1" src="$HERE/snapshots/$1/lean_type_sound" out="$WORK/out-$1"
  mkdir -p "$out"
  echo "== building $c"
  BUILD_FLAGS=--keep-going python3 "$HERE/scripts/build.py" "$LEAN" "$out" \
    "Batteries:$BATTERIES" "LeanTypeSound:$src" -- LeanTypeSound > "$WORK/build-$c.log" 2>&1
  if grep -q '^FAIL' "$WORK/build-$c.log"; then
    echo "build of $c had failures, see $WORK/build-$c.log"; grep '^FAIL' "$WORK/build-$c.log" | head
  fi
}

run_lean () {  # run_lean <commit> <script> <outdir>
  mkdir -p "$3"
  (cd "$3" && LEAN_PATH="$WORK/out-$1" timeout 3600 "$LEAN" "$HERE/scripts/lean/$2" > "${2%.lean}.log" 2>&1) \
    || { echo "lean script $2 failed on $1, see $3/${2%.lean}.log"; return 1; }
}

# Batteries is built once into the baseline output directory and copied.
build 252eab2cf
for c in aef82615e 0d1173557 88927cb6f 9f5188d63 4841f993e; do
  mkdir -p "$WORK/out-$c"
  cp -r "$WORK/out-252eab2cf/Batteries" "$WORK/out-$c/" 2>/dev/null || true
  cp "$WORK/out-252eab2cf/Batteries.olean" "$WORK/out-252eab2cf/Batteries.ilean" "$WORK/out-$c/" 2>/dev/null || true
  build "$c"
done

# Baseline: admitted definitions, statement taint and roots, refutations.
run_lean 252eab2cf DefSorry.lean   "$WORK/audit/252eab2cf"
run_lean 252eab2cf StmtTaint.lean  "$WORK/audit/252eab2cf"
run_lean 252eab2cf StmtRoots.lean  "$WORK/audit/252eab2cf"
run_lean 252eab2cf Refute_nsLookup_nsBind.lean "$WORK/audit/252eab2cf"
run_lean 252eab2cf Refute_explode_thm.lean     "$WORK/audit/252eab2cf"
run_lean 252eab2cf Vacuous.lean                "$WORK/audit/252eab2cf"

# Endpoints: transitive axiom audit of every theorem.
for c in aef82615e 0d1173557 88927cb6f 9f5188d63; do
  run_lean "$c" Axioms.lean "$WORK/audit/$c"
done
run_lean 9f5188d63 DefSorry.lean "$WORK/audit/9f5188d63"

# Repaired translation (4841f993e, two repair commits on 252eab2cf): admitted
# definitions, statement taint, proofs of the repaired statements, and vacuous
# statements. The two refutations are expected to fail here.
run_lean 4841f993e DefSorry.lean      "$WORK/audit/4841f993e"
run_lean 4841f993e StmtTaint.lean     "$WORK/audit/4841f993e"
run_lean 4841f993e StmtRoots.lean     "$WORK/audit/4841f993e"
run_lean 4841f993e Check_repairs.lean "$WORK/audit/4841f993e"
run_lean 4841f993e Check_computed.lean "$WORK/audit/4841f993e"
run_lean 4841f993e Vacuous.lean       "$WORK/audit/4841f993e"
run_lean 4841f993e Refute_nsLookup_nsBind.lean "$WORK/audit/4841f993e" || echo "  (expected: the repaired statement is not refutable)"
run_lean 4841f993e Refute_explode_thm.lean     "$WORK/audit/4841f993e" || echo "  (expected: the repaired statement is not refutable)"
echo "audit outputs in $WORK/audit"
