#!/usr/bin/env bash
# codegen-zisk-zkvm-keccak256-check.sh -- PR-K3 parameterised keccak256.
#
# Builds the `zisk_zkvm_keccak256` ELF: a parameterised
# `zkvm_keccak256(data, len, output)` function matching the
# zkvm-standards C signature, plus a test driver that calls it
# three times (empty / "abc" / 200×0xaa) writing three 32-byte
# digests at OUTPUT[0..96]. Verifies the concatenated 96 bytes.
#
# Concatenated expected (32 bytes each, hex-encoded back-to-back):
#   empty     : c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#   "abc"     : 4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
#   200×0xaa  : ebad1a36949340cbc35b0906948677ac8a062fffa62ee131ae893d81acba7763
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a4704e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45ebad1a36949340cbc35b0906948677ac8a062fffa62ee131ae893d81acba7763"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_zkvm_keccak256 ELF"
lake exe codegen --program zisk_zkvm_keccak256 --halt linux93 \
  -o gen-out/zisk_zkvm_keccak256

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_zkvm_keccak256.elf \
  -o gen-out/zisk_zkvm_keccak256.output -n 500000 \
  >gen-out/zisk_zkvm_keccak256.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 96 gen-out/zisk_zkvm_keccak256.output | tr -d '\n')"

echo
echo "expected (96 bytes: 3 × 32-byte keccak256 digest):"
echo "  ${EXPECTED_HEX:0:96}..."
echo "actual:"
echo "  ${ACTUAL_HEX:0:96}..."
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: zkvm_keccak256 wrapper produces 3 correct digests"
  exit 0
else
  echo "==> FAIL"
  echo "expected: $EXPECTED_HEX"
  echo "actual:   $ACTUAL_HEX"
  exit 1
fi
