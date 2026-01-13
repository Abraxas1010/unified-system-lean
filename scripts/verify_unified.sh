#!/usr/bin/env bash
set -euo pipefail

# Unified System Verification Script
# Runs all verification steps for the paper pack

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

echo "═══════════════════════════════════════════════════════════════════"
echo "  Unified System Verification"
echo "═══════════════════════════════════════════════════════════════════"
echo ""

FAIL=0

# Step 1: Check for sorry/admit
echo "▶ Step 1: Checking for sorry/admit..."
if grep -rn "\bsorry\b\|\badmit\b" HeytingLean/ 2>/dev/null; then
  echo "  ✗ FAIL: Found sorry or admit in source"
  FAIL=1
else
  echo "  ✓ PASS: No sorry or admit found"
fi
echo ""

# Step 2: Lake update
echo "▶ Step 2: Updating dependencies..."
lake update
echo "  ✓ Dependencies updated"
echo ""

# Step 3: Build library
echo "▶ Step 3: Building library (strict mode)..."
if lake build HeytingLean --wfail; then
  echo "  ✓ PASS: Library builds successfully"
else
  echo "  ✗ FAIL: Library build failed"
  FAIL=1
fi
echo ""

# Step 4: Build unified_demo executable
echo "▶ Step 4: Building unified_demo executable..."
if lake build unified_demo; then
  echo "  ✓ PASS: unified_demo builds successfully"
else
  echo "  ✗ FAIL: unified_demo build failed"
  FAIL=1
fi
echo ""

# Step 5: Run unified_demo
echo "▶ Step 5: Running unified_demo..."
if lake exe unified_demo --rules data/unified_demo/rules.json --facts data/unified_demo/facts.tsv --mode heyting > /dev/null 2>&1; then
  echo "  ✓ PASS: unified_demo runs successfully"
else
  echo "  ✗ FAIL: unified_demo failed to run"
  FAIL=1
fi
echo ""

# Summary
echo "═══════════════════════════════════════════════════════════════════"
if [ $FAIL -eq 0 ]; then
  echo "  ✓ ALL CHECKS PASSED"
else
  echo "  ✗ SOME CHECKS FAILED"
fi
echo "═══════════════════════════════════════════════════════════════════"

exit $FAIL
