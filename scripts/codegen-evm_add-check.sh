#!/usr/bin/env bash
# codegen-evm_add-check.sh — M2 verification.
#
# Builds the verified `evm_add` program through codegen → as → ld,
# runs the resulting ELF on ziskemu, and diffs the first 32 bytes of
# ziskemu's public output against the expected 256-bit sum.
#
# Test case (hardcoded in EvmAsm.Codegen.Programs):
#   A = 0xFFFF_FFFF_FFFF_FFFF (limb 0; limbs 1..3 zero)
#   B = 0x1                    (limb 0; limbs 1..3 zero)
#   sum = 2^64, so LE limbs are [0x0, 0x1, 0x0, 0x0]
#
# Exit:
#   0 — output matches expected
#   1 — emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

# Expected 32 bytes (4 LE u64 limbs): 0x0, 0x1, 0x0, 0x0.
EXPECTED_HEX_PADDED="0000000000000000010000000000000000000000000000000000000000000000"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found — install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit evm_add ELF"
lake exe codegen --program evm_add --halt linux93 -o gen-out/evm_add

echo "==> ziskemu -e gen-out/evm_add.elf -o gen-out/evm_add.output"
"$ZISKEMU" -e gen-out/evm_add.elf -o gen-out/evm_add.output -n 100000 \
  >gen-out/evm_add.emu.log 2>&1

# First 32 bytes of the output buffer = the 256-bit sum.
ACTUAL_HEX="$(xxd -p -c 64 -l 32 gen-out/evm_add.output | tr -d '\n')"

echo
echo "expected (32 bytes, LE limbs [0, 1, 0, 0]):"
echo "  $EXPECTED_HEX_PADDED"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX_PADDED" ]]; then
  echo "==> PASS: evm_add output matches expected 2^64 sum"
  exit 0
else
  echo "==> FAIL: evm_add output mismatch"
  exit 1
fi
