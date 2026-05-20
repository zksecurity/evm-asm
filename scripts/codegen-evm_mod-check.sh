#!/usr/bin/env bash
# codegen-evm_mod-check.sh — M2 verification for MOD.
#
# Builds the `evm_mod` program through codegen → as → ld, runs the
# resulting ELF on ziskemu, and diffs the first 32 bytes of ziskemu's
# public output against the expected 256-bit remainder.
#
# Test case (hardcoded in EvmAsm.Codegen.Programs):
#   dividend = 2^64   (LE limbs [0, 1, 0, 0])
#   divisor  = 3      (LE limbs [3, 0, 0, 0])
#   remainder = 1     (LE limbs [1, 0, 0, 0])
#     since 2^64 = 3 * 6148914691236517205 + 1
#
# Exit:
#   0 — output matches expected
#   1 — emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX_PADDED="0100000000000000000000000000000000000000000000000000000000000000"

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

echo "==> emit evm_mod ELF"
lake exe codegen --program evm_mod --halt linux93 -o gen-out/evm_mod

echo "==> ziskemu -e gen-out/evm_mod.elf -o gen-out/evm_mod.output"
"$ZISKEMU" -e gen-out/evm_mod.elf -o gen-out/evm_mod.output -n 500000 \
  >gen-out/evm_mod.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -c 64 -l 32 gen-out/evm_mod.output | tr -d '\n')"

echo
echo "expected (32 bytes, LE limbs [1, 0, 0, 0]):"
echo "  $EXPECTED_HEX_PADDED"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX_PADDED" ]]; then
  echo "==> PASS: evm_mod output matches expected 2^64 mod 3 remainder"
  exit 0
else
  echo "==> FAIL: evm_mod output mismatch"
  exit 1
fi
