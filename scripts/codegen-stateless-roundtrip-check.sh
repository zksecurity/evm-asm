#!/usr/bin/env bash
# codegen-stateless-roundtrip-check.sh -- Stateless guest PR6 verification.
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
#   * `Stateless.SSZ.Decode.decode_validation_bit` -- chases the
#     outer SSZ → witness → headers offset chain and sets `x11 = 1`
#     iff the `witness.headers` list section is empty (regardless of
#     what's in `state` or `codes`).
#   * `Stateless.SSZ.Decode.decode_header_count` -- reads first u32
#     of the headers list (`= 4 * count`) and divides by 4, leaving
#     `header_count` in `x16` (or 0 if list empty).
#   * `Stateless.SSZ.Encode.serialize_stateless_output` -- packs
#     all three into a 56-byte tail: 41-byte SSZ result + 7 zero
#     bytes + 8-byte LE u64 header_count diagnostic.
#
# Fixtures:
#   1. chain_id = 1,                  empty witness        -> bool=1, count=0
#   2. chain_id = 0x1234567890ABCDEF, empty witness        -> bool=1, count=0
#   3. chain_id = 0xDEADBEEF,         one empty header     -> bool=0, count=1
#   4. chain_id = 0xC0FFEE,           one empty state node -> bool=1, count=0
#   5. chain_id = 0xBEEF,             two empty headers    -> bool=0, count=2
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

# Build the 112-hex-char expected output (= 56 bytes):
#   32 zero bytes (hash) | 1 byte bool | 8 LE bytes chain_id
# | 7 zero bytes (gap)   | 8 LE bytes header_count (PR6 diagnostic)
expected_hex_for() {
  local cid="$1"
  local bool_hex="$2"      # "00" or "01"
  local count_dec="$3"     # decimal header_count
  local chain_le hcount_le
  chain_le="$(chain_id_le_hex "$cid")"
  hcount_le="$(python3 -c "print(int('$count_dec').to_bytes(8, 'little').hex())")"
  echo "$(printf '00%.0s' $(seq 1 32))${bool_hex}${chain_le}$(printf '00%.0s' $(seq 1 7))${hcount_le}"
}

run_fixture() {
  local label="$1"
  local cid="$2"
  local bool_hex="$3"
  local count_dec="$4"
  shift 4
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
  actual="$(xxd -p -l 56 "$output_file" | tr -d '\n')"
  expected="$(expected_hex_for "$cid" "$bool_hex" "$count_dec")"

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
run_fixture "empty_witness_chain1" 1 "01" 0                        || fail=1
run_fixture "empty_witness_chain_big" 0x1234567890ABCDEF "01" 0    || fail=1
run_fixture "one_empty_header_chain_dead" 0xDEADBEEF "00" 1 \
            --with-empty-header                                    || fail=1
run_fixture "one_empty_state_node_chain_coffee" 0xC0FFEE "01" 0 \
            --with-empty-state-node                                || fail=1
run_fixture "two_empty_headers_chain_beef" 0xBEEF "00" 2 \
            --with-two-empty-headers                               || fail=1

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: all stateless_guest fixtures match expected SSZ output"
  exit 0
else
  echo "==> FAIL: at least one fixture mismatched"
  exit 1
fi
