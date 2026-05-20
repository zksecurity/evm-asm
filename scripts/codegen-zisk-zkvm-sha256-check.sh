#!/usr/bin/env bash
# codegen-zisk-zkvm-sha256-check.sh -- PR-S2 verification.
#
# Builds the `zisk_zkvm_sha256` ELF and runs it on ziskemu. The
# test driver calls `zkvm_sha256(data, len, output)` three times
# (empty / "abc" / 200×0xaa) and writes the canonical 32-byte
# SHA-256 digests at OUTPUT[0..96].
#
# Expected (concatenated canonical wire bytes):
#   sha256(b"")        = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
#   sha256(b"abc")     = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
#   sha256(b"\xaa"*200) = 605ed279d0a1af786c79054f9424d196ed6a1f0331100a923d711885d42099bb
#
# These are FIPS 180-4 test vectors / well-known values
# verified independently via `hashlib.sha256` in Python.
set -euo pipefail

cd "$(dirname "$0")/.."

EXPECTED_HEX="e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad605ed279d0a1af786c79054f9424d196ed6a1f0331100a923d711885d42099bb"

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

echo "==> emit zisk_zkvm_sha256 ELF"
lake exe codegen --program zisk_zkvm_sha256 --halt linux93 \
  -o gen-out/zisk_zkvm_sha256

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_zkvm_sha256.elf \
  -o gen-out/zisk_zkvm_sha256.output -n 500000 \
  >gen-out/zisk_zkvm_sha256.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 96 gen-out/zisk_zkvm_sha256.output | tr -d '\n')"

echo
echo "expected (96 bytes: 3 × 32-byte sha256 digest):"
echo "  ${EXPECTED_HEX:0:96}..."
echo "actual:"
echo "  ${ACTUAL_HEX:0:96}..."
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: zkvm_sha256 wrapper produces 3 correct digests"
  exit 0
else
  echo "==> FAIL"
  echo "expected: $EXPECTED_HEX"
  echo "actual:   $ACTUAL_HEX"
  exit 1
fi
