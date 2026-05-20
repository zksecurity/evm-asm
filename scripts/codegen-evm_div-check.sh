#!/usr/bin/env bash
# codegen-evm_div-check.sh — M2 verification for DIV.
#
# Builds the verified `evm_div` program through codegen → as → ld,
# runs the resulting ELF on ziskemu, and diffs the first 32 bytes of
# ziskemu's public output against the expected 256-bit quotient.
#
# Test case (hardcoded in EvmAsm.Codegen.Programs):
#   dividend = 2^64    (LE limbs [0, 1, 0, 0])
#   divisor  = 2       (LE limbs [2, 0, 0, 0])
#   quotient = 2^63    (LE limbs [0x8000000000000000, 0, 0, 0])
#
# Exit:
#   0 — output matches expected
#   1 — emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

# Expected 32 bytes (4 LE u64 limbs): 0x8000000000000000, 0, 0, 0.
EXPECTED_HEX_PADDED="0000000000000080000000000000000000000000000000000000000000000000"

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

echo "==> emit evm_div ELF"
lake exe codegen --program evm_div --halt linux93 -o gen-out/evm_div

echo "==> ziskemu -e gen-out/evm_div.elf -o gen-out/evm_div.output"
"$ZISKEMU" -e gen-out/evm_div.elf -o gen-out/evm_div.output -n 500000 \
  >gen-out/evm_div.emu.log 2>&1

# First 32 bytes of the output buffer = the 256-bit quotient.
ACTUAL_HEX="$(xxd -p -c 64 -l 32 gen-out/evm_div.output | tr -d '\n')"

echo
echo "expected (32 bytes, LE limbs [0x8000000000000000, 0, 0, 0]):"
echo "  $EXPECTED_HEX_PADDED"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX_PADDED" ]]; then
  echo "==> PASS: evm_div output matches expected 2^63 quotient"
  exit 0
else
  echo "==> FAIL: evm_div output mismatch"
  exit 1
fi
