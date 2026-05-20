#!/usr/bin/env bash
# codegen-zisk-ssz-merkleize-pow2-check.sh -- PR-S6 verification.
#
# Exercises the `ssz_merkleize_pow2` reduction over power-of-two
# chunk counts of all-zero chunks. With all-zero leaves at depth
# 0, the SSZ Merkle root at depth d equals Z_d in the PR-S5
# zero-hashes table:
#
#   n = 1   → Z_0 = 0000...00
#   n = 2   → Z_1 = f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b
#   n = 4   → Z_2 = db56114e00fdd4c1f85c892bf35ac9a89289aaecb1ebd0a96cde606a748b5d71
#   n = 8   → Z_3 = c78009fdf07fc56a11f122370658a353aaa542ed63e44c4bc15ff4cd105ab33c
#   n = 16  → Z_4 = 536d98837f2dd165a55d5eeae91485954472d56f246df256bf3cae19352a123c
#   n = 32  → Z_5 = 9efde052aa15429fae05bad4d0b1d7c64da64d03d7a1854a588c2cb8430c0d30
#
# This confirms the reduction loop walks the tree correctly at
# every depth up to the function's cap (32 chunks). The input
# file layout is the standard ziskemu format:
#   bytes 0..8 : LE u64 n
#   bytes 8..  : n * 32 zero bytes (the chunks)
set -euo pipefail

cd "$(dirname "$0")/.."

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

echo "==> emit zisk_ssz_merkleize_pow2 ELF"
lake exe codegen --program zisk_ssz_merkleize_pow2 --halt linux93 \
  -o gen-out/zisk_ssz_merkleize_pow2

# Precompute Z_0..Z_5 once with Python.
EXPECTED_TABLE="$(python3 -c "
import hashlib
z = [b'\x00' * 32]
for _ in range(5):
    z.append(hashlib.sha256(z[-1]+z[-1]).digest())
for v in z:
    print(v.hex())
")"

FAILED=0
for n in 1 2 4 8 16 32; do
  case "$n" in
    1) d=0 ;; 2) d=1 ;; 4) d=2 ;; 8) d=3 ;; 16) d=4 ;; 32) d=5 ;;
  esac
  INPUT_FILE="gen-out/zisk_ssz_merkleize_pow2_n${n}.input"
  python3 -c "
import struct, sys
n = $n
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', n))
    f.write(b'\x00' * (n * 32))
" "$INPUT_FILE"

  "$ZISKEMU" -e gen-out/zisk_ssz_merkleize_pow2.elf \
    -i "$INPUT_FILE" \
    -o "gen-out/zisk_ssz_merkleize_pow2_n${n}.output" -n 500000 \
    >"gen-out/zisk_ssz_merkleize_pow2_n${n}.emu.log" 2>&1

  ACTUAL="$(xxd -p -l 32 gen-out/zisk_ssz_merkleize_pow2_n${n}.output | tr -d '\n')"
  EXPECTED="$(echo "$EXPECTED_TABLE" | sed -n "$((d+1))p")"

  if [[ "$ACTUAL" == "$EXPECTED" ]]; then
    printf "  n=%2d (depth %d) OK   %s\n" "$n" "$d" "$EXPECTED"
  else
    printf "  n=%2d (depth %d) FAIL\n    expected: %s\n    actual:   %s\n" \
      "$n" "$d" "$EXPECTED" "$ACTUAL"
    FAILED=1
  fi
done

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ssz_merkleize_pow2 reduces all-zero chunks to Z_d at every depth 0..5"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
