#!/usr/bin/env bash
# codegen-zisk-keccak256-from-input-check.sh -- PR-K4 host-supplied input.
#
# First real-shape consumer of `zkvm_keccak256`:
#   1. Python (via `keccak256-gen-input.py`) generates an
#      RLP-encoded amsterdam Block Header (or another shape) and
#      writes a ziskemu-format input file + expected hash.
#   2. The guest reads length from INPUT_ADDR+8, points at
#      INPUT_ADDR+16, calls `zkvm_keccak256`, writes the 32-byte
#      digest at OUTPUT_ADDR.
#   3. We diff the digest bytes against Python's expected.
#
# Override the shape via $SHAPE (default: header). Available
# shapes are declared in `scripts/keccak256-gen-input.py`'s SHAPES
# dict.
set -euo pipefail

cd "$(dirname "$0")/.."

SHAPE="${SHAPE:-header}"

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

REPO_ROOT="$(pwd)"
GEN="$REPO_ROOT/scripts/keccak256-gen-input.py"

mkdir -p gen-out

INPUT_FILE="$REPO_ROOT/gen-out/zisk_keccak256_from_input-${SHAPE}.input"
HASH_FILE="$REPO_ROOT/gen-out/zisk_keccak256_from_input-${SHAPE}.expected"
OUTPUT_FILE="$REPO_ROOT/gen-out/zisk_keccak256_from_input-${SHAPE}.output"
LOG_FILE="$REPO_ROOT/gen-out/zisk_keccak256_from_input-${SHAPE}.emu.log"

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_keccak256_from_input ELF"
lake exe codegen --program zisk_keccak256_from_input --halt linux93 \
  -o gen-out/zisk_keccak256_from_input

echo "==> gen Python fixture (shape=$SHAPE)"
uv run --directory execution-specs --quiet python3 \
  "$GEN" --shape "$SHAPE" "$INPUT_FILE" "$HASH_FILE"

EXPECTED_HEX="$(cat "$HASH_FILE")"

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_keccak256_from_input.elf \
  -i "$INPUT_FILE" -o "$OUTPUT_FILE" -n 1000000 \
  >"$LOG_FILE" 2>&1

ACTUAL_HEX="$(xxd -p -l 32 "$OUTPUT_FILE" | tr -d '\n')"

echo
echo "expected (keccak256 of $SHAPE input):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: zkvm_keccak256 round-trip on host-supplied $SHAPE"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
