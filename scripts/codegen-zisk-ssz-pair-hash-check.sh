#!/usr/bin/env bash
# codegen-zisk-ssz-pair-hash-check.sh -- PR-S4 verification.
#
# Exercises the SSZ merkleization primitive
#   sha256_pair(L, R) = sha256(L || R)
# via `Stateless.SSZ.HashTreeRoot.sszPairHashCallAsm` (an a1=64
# wrapper) and the PR-S2 `zkvm_sha256` Merkle-Damgaard wrapper.
#
# Fixture: L = R = 0x00..00 (32 zero bytes each), so the call
# digests 64 zero bytes. That's `Z_1` in the SSZ "zero hashes"
# sequence; its value is fully defined by the SSZ spec and is a
# well-known SHA-256 test value:
#
#   sha256(b'\x00' * 64) =
#     f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b
#
# The ziskemu run consumes a 72-byte input file:
#   bytes 0..8  : LE u64 length = 64
#   bytes 8..40 : L (32 zero bytes)
#   bytes 40..72: R (32 zero bytes)
# (Length prefix is ignored by the shim itself; the BuildUnit
#  expects L||R at INPUT_ADDR + 16 and pins the length to 64.)
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"

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

echo "==> emit zisk_ssz_pair_hash ELF"
lake exe codegen --program zisk_ssz_pair_hash --halt linux93 \
  -o gen-out/zisk_ssz_pair_hash

echo "==> generate ziskemu input file (length=64, L||R = 64 × 0x00)"
INPUT_FILE="gen-out/zisk_ssz_pair_hash.input"
python3 -c "
import struct, sys
data = b'\x00' * 64
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(data)))
    f.write(data)
" "$INPUT_FILE"

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_ssz_pair_hash.elf \
  -i "$INPUT_FILE" \
  -o gen-out/zisk_ssz_pair_hash.output -n 500000 \
  >gen-out/zisk_ssz_pair_hash.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 32 gen-out/zisk_ssz_pair_hash.output | tr -d '\n')"

echo
echo "expected (Z_1 = sha256(64 × 0x00)):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: ssz_pair_hash(0, 0) = SSZ Z_1"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
