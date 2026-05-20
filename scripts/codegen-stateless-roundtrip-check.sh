#!/usr/bin/env bash
# codegen-stateless-roundtrip-check.sh -- Stateless guest PR4 verification.
#
# Builds the `stateless_guest` program through codegen -> as -> ld,
# generates SSZ-encoded `SszStatelessInput`s (via the
# `execution-specs` reference library) carrying a known `chain_id`
# and either an empty witness or a witness with one zero-length
# header, feeds each to ziskemu, and diffs the first 41 bytes of
# ziskemu's public output against the expected SSZ encoding of
# `SszStatelessValidationResult`.
#
# What's exercised:
#   * `Stateless.SSZ.Decode.read_chain_id` -- u64 LE at byte 24 of
#     INPUT_ADDR.
#   * `Stateless.SSZ.Decode.decode_validation_bit` -- reads
#     offset_1 and offset_3 from the outer container header (u32 LE
#     at bytes 20 and 32) and sets `x11 = 1` iff
#     `offset_3 - offset_1 == 12` (empty SszExecutionWitness body).
#   * `Stateless.SSZ.Encode.serialize_stateless_output` -- packs both
#     into the 41-byte SSZ result at OUTPUT_ADDR.
#
# Fixtures:
#   1. chain_id = 1,                  empty witness     -> bool=1
#   2. chain_id = 0x1234567890ABCDEF, empty witness     -> bool=1
#   3. chain_id = 0xDEADBEEF,         one empty header  -> bool=0
#
# Exit:
#   0 -- all fixtures match expected
#   1 -- emission / build / emulation failed, or output mismatch
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

REPO_ROOT="$(pwd)"
INPUT_GEN="$REPO_ROOT/scripts/stateless-gen-input.py"

echo "==> lake build codegen"
lake build codegen

echo "==> emit stateless_guest ELF"
lake exe codegen --program stateless_guest --halt linux93 \
  -o gen-out/stateless_guest

# Hex-encode a chain_id as the 16 hex chars that should appear at
# bytes 33..41 of the output (u64 LE).
chain_id_le_hex() {
  python3 -c "
import sys
c = int(sys.argv[1], 0)
print(c.to_bytes(8, 'little').hex())
" "$1"
}

# Build the 82-hex-char expected output for a given chain_id + bool:
#   32 zero bytes (hash) | 1 byte bool | 8 LE bytes of chain_id
expected_hex_for() {
  local cid="$1"
  local bool_hex="$2"  # "00" or "01"
  local low8
  low8="$(chain_id_le_hex "$cid")"
  echo "$(printf '00%.0s' $(seq 1 32))${bool_hex}${low8}"
}

run_fixture() {
  local label="$1"
  local cid="$2"
  local bool_hex="$3"
  shift 3
  local extra_args=("$@")

  local safe_label="${label//[^0-9A-Za-z_]/_}"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-${safe_label}.input"
  local output_file="$REPO_ROOT/gen-out/stateless_guest-${safe_label}.output"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-${safe_label}.emu.log"

  echo "==> [$label] gen SSZ input  (chain_id=$cid${extra_args[*]:+, ${extra_args[*]}})"
  uv run --directory execution-specs --quiet python3 \
    "$INPUT_GEN" "$cid" "$input_file" "${extra_args[@]}"

  echo "==> [$label] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$output_file" -n 100000 >"$log_file" 2>&1

  local actual expected
  actual="$(xxd -p -l 41 "$output_file" | tr -d '\n')"
  expected="$(expected_hex_for "$cid" "$bool_hex")"

  echo "    expected: $expected"
  echo "    actual:   $actual"

  if [[ "$actual" == "$expected" ]]; then
    echo "    PASS"
    return 0
  else
    echo "    FAIL"
    return 1
  fi
}

fail=0
run_fixture "empty_witness_chain1" 1 "01"                          || fail=1
run_fixture "empty_witness_chain_big" 0x1234567890ABCDEF "01"      || fail=1
run_fixture "one_empty_header_chain_dead" 0xDEADBEEF "00" \
            --with-empty-header                                    || fail=1

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: all stateless_guest fixtures match expected SSZ output"
  exit 0
else
  echo "==> FAIL: at least one fixture mismatched"
  exit 1
fi
