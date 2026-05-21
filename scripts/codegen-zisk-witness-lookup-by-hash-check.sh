#!/usr/bin/env bash
# codegen-zisk-witness-lookup-by-hash-check.sh -- PR-K19.
#
# Lookup an SSZ-list element by its keccak256 digest. Returns
# (status, offset, length) where offset+length identify the
# matched element's bytes within the section.
#
# Linear-scan implementation: walks the list computing keccak
# per entry until either a match or exhaustion. PR-K20+ will
# replace with a pre-built bucket table for faster lookups.
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

echo "==> emit zisk_witness_lookup_by_hash ELF"
lake exe codegen --program zisk_witness_lookup_by_hash --halt linux93 \
  -o gen-out/zisk_witness_lookup_by_hash

REPO_ROOT="$(pwd)"

# build_ssz_section_and_target
#   - elements_hex... target_hex
#   builds the SSZ list section + emits computed expected
#   (status, offset, length) for the target hash via uv python.
run_case() {
  local name="$1" mode="$2"
  shift 2
  local args=("$@")

  local in_file="$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_${name}.expected"

  # mode forms:
  #   "hit elem_idx elements..."  -- target = keccak(elements[elem_idx])
  #   "miss elements..."          -- target = junk
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak

def k(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

mode = '$mode'
parts = mode.split()
which = parts[0]
if which == 'hit':
    elem_idx = int(parts[1])
    elements = [bytes.fromhex(a) for a in parts[2:]]
    target = k(elements[elem_idx])
    expected_status = 0
    n = len(elements)
    inner_off = 4 * n + sum(len(e) for e in elements[:elem_idx])
    expected_offset = inner_off
    expected_length = len(elements[elem_idx])
elif which == 'miss':
    elements = [bytes.fromhex(a) for a in parts[1:]]
    target = bytes.fromhex('deadbeef' * 8)
    expected_status = 1
    expected_offset = 0
    expected_length = 0
elif which == 'empty':
    elements = []
    target = bytes.fromhex('deadbeef' * 8)
    expected_status = 1
    expected_offset = 0
    expected_length = 0

n = len(elements)
section = b''
if n > 0:
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    for e in elements:
        section += e

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(section)))
    f.write(target)
    pad_after_hash = 0  # already aligned
    f.write(section)
    pad = (-(8 + 32 + len(section))) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected.txt', 'w') as f:
    f.write(f'{expected_status} {expected_offset} {expected_length}')
" "$in_file" "${args[@]+"${args[@]}"}"

  "$ZISKEMU" -e gen-out/zisk_witness_lookup_by_hash.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_witness_lookup_by_hash_${name}.emu.log" 2>&1 || true

  if [[ ! -f "$in_file.expected.txt" ]]; then
    printf "  %-20s FAIL (Python helper failed to write expected)\n" "$name"
    return 1
  fi
  local expected_line; expected_line="$(cat "$in_file.expected.txt")"
  local expected_status expected_offset expected_length
  read -r expected_status expected_offset expected_length <<<"$expected_line"

  local actual_status actual_offset actual_length
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_offset="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_length="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le exp_offset_le exp_length_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_offset_le="$(python3 -c "print(int('$expected_offset').to_bytes(8, 'little').hex())")"
  exp_length_le="$(python3 -c "print(int('$expected_length').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_offset" == "$exp_offset_le" && \
        "$actual_length" == "$exp_length_le" ]]; then
    printf "  %-20s OK   status=%d off=%d len=%d\n" \
      "$name" "$expected_status" "$expected_offset" "$expected_length"
    return 0
  else
    printf "  %-20s FAIL\n    expected: %d / %d / %d\n    actual:   0x%s / 0x%s / 0x%s\n" \
      "$name" "$expected_status" "$expected_offset" "$expected_length" \
      "$actual_status" "$actual_offset" "$actual_length"
    return 1
  fi
}

FAILED=0
run_case "empty_list"   "empty"                                                                  || FAILED=1
run_case "n1_hit"       "hit 0 deadbeef"                                                         || FAILED=1
run_case "n1_miss"      "miss deadbeef"                                                          || FAILED=1
run_case "n3_hit_0"     "hit 0 aabb cc ddeeff"                                                   || FAILED=1
run_case "n3_hit_1"     "hit 1 aabb cc ddeeff"                                                   || FAILED=1
run_case "n3_hit_2"     "hit 2 aabb cc ddeeff"                                                   || FAILED=1
run_case "n3_miss"      "miss aabb cc ddeeff"                                                    || FAILED=1
run_case "n5_hit_3"     "hit 3 aa bb cc dd ee"                                                   || FAILED=1
run_case "n1_long_hit"  "hit 0 $(printf 'aa%.0s' $(seq 1 100))"                                  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_lookup_by_hash matches Python over all 9 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
