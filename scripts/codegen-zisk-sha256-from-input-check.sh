#!/usr/bin/env bash
# codegen-zisk-sha256-from-input-check.sh -- PR-S3 host-supplied SHA-256.
#
# Mirror of PR-K4 `codegen-zisk-keccak256-from-input-check.sh`
# but with the SHA-256 wrapper from PR-S2 instead of keccak256.
# The guest reads byte length from INPUT_ADDR + 8 (ziskemu's
# length-prefix slot), points at INPUT_ADDR + 16, calls
# zkvm_sha256, writes the 32-byte digest at OUTPUT_ADDR.
#
# Fixture: 200 bytes of 0xaa (same content as PR-S2's third
# probe, but now driven through ziskemu's -i input file).
# Expected:
#   sha256(b"\xaa" * 200) =
#     605ed279d0a1af786c79054f9424d196ed6a1f0331100a923d711885d42099bb
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="605ed279d0a1af786c79054f9424d196ed6a1f0331100a923d711885d42099bb"

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

echo "==> emit zisk_sha256_from_input ELF"
lake exe codegen --program zisk_sha256_from_input --halt linux93 \
  -o gen-out/zisk_sha256_from_input

echo "==> generate ziskemu input file (200 × 0xaa, length-prefixed)"
INPUT_FILE="gen-out/zisk_sha256_from_input.input"
python3 -c "
import struct, sys
data = b'\xaa' * 200
total = 8 + len(data)
pad = (-total) % 8     # round file to multiple of 8 bytes
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(data)))
    f.write(data)
    if pad:
        f.write(b'\x00' * pad)
" "$INPUT_FILE"

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_sha256_from_input.elf \
  -i "$INPUT_FILE" \
  -o gen-out/zisk_sha256_from_input.output -n 500000 \
  >gen-out/zisk_sha256_from_input.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 32 gen-out/zisk_sha256_from_input.output | tr -d '\n')"

echo
echo "expected (sha256 of 200 × 0xaa):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: zkvm_sha256 round-trip on host-supplied input"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
