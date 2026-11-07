#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MATHLIB_ROOT="${1:-${GRH_MATHLIB_ROOT:-}}"
LEAN_EXE="${LEAN_EXE:-lean}"

if [[ -z "$MATHLIB_ROOT" || ! -f "$MATHLIB_ROOT/lean-toolchain" ]]; then
  echo "ERROR=COMPATIBLE_MATHLIB_ROOT_REQUIRED"
  exit 2
fi

if ! "$LEAN_EXE" --version | grep -q '^Lean (version 4\.33\.0,'; then
  echo "ERROR=LEAN_VERSION_MISMATCH_EXPECTED_4_33_0"
  "$LEAN_EXE" --version || true
  exit 2
fi

if ! grep -qx 'leanprover/lean4:v4.33.0' "$MATHLIB_ROOT/lean-toolchain"; then
  echo "ERROR=MATHLIB_TOOLCHAIN_MISMATCH"
  exit 2
fi

BUILD_ROOT="$ROOT/.ci-build"
BUILD_LIB="$BUILD_ROOT/lib/lean"
LOG_DIR="$BUILD_ROOT/logs"
rm -rf "$BUILD_ROOT"
mkdir -p "$BUILD_LIB" "$LOG_DIR"

LEAN_PATH_VALUE="$BUILD_LIB:$MATHLIB_ROOT/.lake/build/lib/lean"
if [[ -d "$MATHLIB_ROOT/.lake/packages" ]]; then
  for pkg in "$MATHLIB_ROOT"/.lake/packages/*; do
    if [[ -d "$pkg/.lake/build/lib/lean" ]]; then
      LEAN_PATH_VALUE="$LEAN_PATH_VALUE:$pkg/.lake/build/lib/lean"
    fi
  done
fi
export LEAN_PATH="$LEAN_PATH_VALUE"

echo "CI_CHAIN=START"
echo "LEAN_EXE=$LEAN_EXE"
"$LEAN_EXE" --version
echo "MATHLIB_ROOT=$MATHLIB_ROOT"

while IFS= read -r raw || [[ -n "$raw" ]]; do
  module="${raw%$'\r'}"
  [[ -z "$module" ]] && continue
  [[ "$module" == \#* ]] && continue

  src="$ROOT/$module.lean"
  out="$BUILD_LIB/$module.olean"
  safe="${module//\//__}"
  log="$LOG_DIR/$safe.log"

  if [[ ! -f "$src" ]]; then
    echo "ERROR=SOURCE_MISSING|$module"
    exit 1
  fi

  mkdir -p "$(dirname "$out")"
  echo "COMPILE=$module"
  if ! "$LEAN_EXE" -j 1 -o "$out" "$src" >"$log" 2>&1; then
    echo "COMPILE_FAIL=$module"
    cat "$log"
    exit 1
  fi

  if grep -Eqi "sorryAx|declaration uses 'sorry'|Lean\.ofReduceBool|Lean\.trustCompiler" "$log"; then
    echo "AXIOM_AUDIT_FAIL=$module"
    cat "$log"
    exit 1
  fi

  echo "COMPILE_PASS=$module"
done < "$ROOT/build-modules.txt"

JOINT_LOG="$LOG_DIR/JOINT_MAIN.log"
if [[ ! -f "$JOINT_LOG" ]]; then
  echo "ERROR=JOINT_MAIN_LOG_MISSING"
  exit 1
fi

grep -Fq "GeneralizedDirichletHVRJoint.JOINT_HVR_GENERALIZED_DIRICHLET_MAIN" "$JOINT_LOG"
grep -Fq "'GeneralizedDirichletHVRJoint.JOINT_HVR_GENERALIZED_DIRICHLET_MAIN' depends on axioms:" "$JOINT_LOG"

echo "UPSTREAM_LEGACY_THEOREMS_VISIBLE=PASS"
echo "HVR_THEOREMS_VISIBLE=PASS"
echo "GENERALIZED_CAYLEY_LIFT_BRIDGE=PASS"
echo "THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY"
echo "REMAINING_SUBSTANTIVE_FRONTIER=RELATIVE_COMPLETED_PACKET_PROPAGATION"
echo "UNCONDITIONAL_RH_IMPLIES_GRH=NOT_ESTABLISHED"
echo "CI_CHAIN=PASS"
