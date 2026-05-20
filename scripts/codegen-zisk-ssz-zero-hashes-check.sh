#!/usr/bin/env bash
# codegen-zisk-ssz-zero-hashes-check.sh -- PR-S5 verification.
#
# Iterates `i = 0..31`, asks the `zisk_ssz_zero_hashes` probe for
# Z_i, and diffs against Python's recomputation of
#   Z_0 = b'\x00' * 32
#   Z_i = sha256(Z_{i-1} + Z_{i-1})
#
# The probe BuildUnit reads the depth index from the ziskemu
# input file (LE u64 at file bytes 0..8) and writes 32 bytes of
# the looked-up Z_i to OUTPUT_ADDR.
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

echo "==> emit zisk_ssz_zero_hashes ELF"
lake exe codegen --program zisk_ssz_zero_hashes --halt linux93 \
  -o gen-out/zisk_ssz_zero_hashes

echo "==> precompute Python reference Z_0..Z_31"
EXPECTED_TABLE="$(python3 -c "
import hashlib
z = [b'\x00' * 32]
for _ in range(31):
    z.append(hashlib.sha256(z[-1]+z[-1]).digest())
for v in z:
    print(v.hex())
")"

FAILED=0
for i in $(seq 0 31); do
  INPUT_FILE="gen-out/zisk_ssz_zero_hashes_${i}.input"
  python3 -c "
import struct, sys
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', $i))
" "$INPUT_FILE"

  "$ZISKEMU" -e gen-out/zisk_ssz_zero_hashes.elf \
    -i "$INPUT_FILE" \
    -o "gen-out/zisk_ssz_zero_hashes_${i}.output" -n 50000 \
    >"gen-out/zisk_ssz_zero_hashes_${i}.emu.log" 2>&1

  ACTUAL="$(xxd -p -l 32 gen-out/zisk_ssz_zero_hashes_${i}.output | tr -d '\n')"
  EXPECTED="$(echo "$EXPECTED_TABLE" | sed -n "$((i+1))p")"

  if [[ "$ACTUAL" == "$EXPECTED" ]]; then
    printf "  Z_%-2d  OK  %s\n" "$i" "$EXPECTED"
  else
    printf "  Z_%-2d  FAIL\n    expected: %s\n    actual:   %s\n" "$i" "$EXPECTED" "$ACTUAL"
    FAILED=1
  fi
done

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ssz_zero_hashes table matches Python over all 32 entries"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
