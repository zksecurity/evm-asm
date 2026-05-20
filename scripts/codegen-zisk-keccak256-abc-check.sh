#!/usr/bin/env bash
# codegen-zisk-keccak256-abc-check.sh -- PR-K2a keccak256("abc") probe.
#
# Single-block input. Builds and runs the `zisk_keccak256_abc`
# program, verifies the 32-byte digest equals the canonical
#
#   keccak256(b"abc") =
#     4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
#
# Exercises the absorb path where the input fits in the rate
# window (3 bytes < 136-byte rate) and the padding shifts to byte
# 3 instead of byte 0.
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

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

echo "==> emit zisk_keccak256_abc ELF"
lake exe codegen --program zisk_keccak256_abc --halt linux93 \
  -o gen-out/zisk_keccak256_abc

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_keccak256_abc.elf \
  -o gen-out/zisk_keccak256_abc.output -n 200000 \
  >gen-out/zisk_keccak256_abc.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 32 gen-out/zisk_keccak256_abc.output | tr -d '\n')"

echo
echo "expected (keccak256 of b\"abc\"):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS"
  exit 0
else
  echo "==> FAIL: keccak256(\"abc\") output mismatch"
  exit 1
fi
