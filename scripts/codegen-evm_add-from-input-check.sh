#!/usr/bin/env bash
# codegen-evm_add-from-input-check.sh — M4 verification.
#
# Like codegen-evm_add-check.sh, but the two 256-bit operands are loaded
# at runtime from the ziskemu `-i <input>` channel instead of being
# baked into the .data section. Exercises the empirical input layout
# documented in EvmAsm/Codegen/Programs.lean (INPUT_DATA_OFFSET = 16).
#
# Input file format (length-prefixed record):
#   8 bytes  LE u64 length = 64
#   32 bytes operand A (LE limbs, low limb first)
#   32 bytes operand B (LE limbs, low limb first)
#
# Test case (same as M2 to make results directly comparable):
#   A    = 0xFFFF_FFFF_FFFF_FFFF (limb 0; limbs 1..3 zero)
#   B    = 0x1                    (limb 0; limbs 1..3 zero)
#   sum  = 2^64 → LE limbs [0, 1, 0, 0]
#
# Exit:
#   0 — output matches expected
#   1 — emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="0000000000000000010000000000000000000000000000000000000000000000"

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

echo "==> emit evm_add_from_input ELF"
lake exe codegen --program evm_add_from_input --halt linux93 \
  -o gen-out/evm_add_from_input

echo "==> pack input file (8B length + 64B operands)"
python3 - <<'PY'
import struct, pathlib
A = bytes.fromhex("ffffffffffffffff") + bytes(24)   # 32 bytes, LE, A = 2^64-1
B = bytes.fromhex("0100000000000000") + bytes(24)   # 32 bytes, LE, B = 1
data = A + B
record = struct.pack("<Q", len(data)) + data
pathlib.Path("gen-out/evm_add_from_input.input.bin").write_bytes(record)
PY

echo "==> ziskemu -e ... -i ... -o ..."
"$ZISKEMU" -e gen-out/evm_add_from_input.elf \
           -i gen-out/evm_add_from_input.input.bin \
           -o gen-out/evm_add_from_input.output \
           -n 100000 \
  >gen-out/evm_add_from_input.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -c 64 -l 32 gen-out/evm_add_from_input.output | tr -d '\n')"

echo
echo "expected: $EXPECTED_HEX"
echo "actual:   $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: evm_add_from_input output matches expected 2^64 sum"
  exit 0
else
  echo "==> FAIL: evm_add_from_input output mismatch"
  exit 1
fi
