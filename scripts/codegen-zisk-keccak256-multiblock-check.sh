#!/usr/bin/env bash
# codegen-zisk-keccak256-multiblock-check.sh -- PR-K2b multi-block keccak256 probe.
#
# 200 bytes of 0xaa: forces one full-block absorb (136 bytes) plus
# one final block with 64 bytes of remainder + padding. Exercises
# the absorb-loop iteration and the byte-by-byte remainder XOR.
#
#   keccak256(b"\xaa" * 200) =
#     ebad1a36949340cbc35b0906948677ac8a062fffa62ee131ae893d81acba7763
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="ebad1a36949340cbc35b0906948677ac8a062fffa62ee131ae893d81acba7763"

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

echo "==> emit zisk_keccak256_multiblock ELF"
lake exe codegen --program zisk_keccak256_multiblock --halt linux93 \
  -o gen-out/zisk_keccak256_multiblock

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_keccak256_multiblock.elf \
  -o gen-out/zisk_keccak256_multiblock.output -n 500000 \
  >gen-out/zisk_keccak256_multiblock.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 32 gen-out/zisk_keccak256_multiblock.output | tr -d '\n')"

echo
echo "expected (keccak256 of 200 × 0xaa):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
