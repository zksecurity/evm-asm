#!/usr/bin/env bash
# codegen-zisk-keccak256-empty-check.sh -- PR-K2 keccak256(empty) probe.
#
# Builds the `zisk_keccak256_empty` program and verifies that the
# 32-byte digest it writes at OUTPUT_ADDR matches the canonical
# Ethereum keccak256 hash of the empty byte string:
#
#   keccak256(b"") =
#     c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#
# This is the simplest exercise of the full sponge wrapper: no
# input to absorb, just the padded final block (0x01 at byte 0,
# 0x80 at byte 135 — Ethereum Keccak padding for the 1088-bit
# rate). The keccak-f permutation is the intrinsic pinned in
# PR-K1.
#
# Exit:
#   0 -- ziskemu output matches the canonical hash
#   1 -- build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

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

echo "==> emit zisk_keccak256_empty ELF"
lake exe codegen --program zisk_keccak256_empty --halt linux93 \
  -o gen-out/zisk_keccak256_empty

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_keccak256_empty.elf \
  -o gen-out/zisk_keccak256_empty.output -n 200000 \
  >gen-out/zisk_keccak256_empty.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 32 gen-out/zisk_keccak256_empty.output | tr -d '\n')"

echo
echo "expected (keccak256 of empty input):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: keccak256(empty) sponge round-trip matches"
  exit 0
else
  echo "==> FAIL: keccak256(empty) output mismatch"
  exit 1
fi
