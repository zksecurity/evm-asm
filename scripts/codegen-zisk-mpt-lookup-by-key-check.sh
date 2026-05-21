#!/usr/bin/env bash
# codegen-zisk-mpt-lookup-by-key-check.sh -- PR-K26.
#
# End-to-end MPT lookup by raw key:
#   keccak256(key) -> nibbles -> mpt_walk -> value bytes
#
# This is the standard Ethereum state/storage trie shape, where
# the "key" is either a 20-byte address (state trie) or a
# 32-byte storage slot index (storage trie).
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

echo "==> emit zisk_mpt_lookup_by_key ELF"
lake exe codegen --program zisk_mpt_lookup_by_key --halt linux93 \
  -o gen-out/zisk_mpt_lookup_by_key

REPO_ROOT="$(pwd)"

# Run a fixture: Python builds the trie, generates expected output, and
# we compare ziskemu's output against it.
#
# mode forms (passed as second arg, single string with spaces):
#   "single_leaf key_hex value_hex"  -- 1-leaf trie keyed by keccak256(key)
#   "miss key_hex"                   -- 1-leaf trie (different key), lookup misses
#   "empty_witness"                  -- empty witness, lookup misses
run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_mpt_lookup_by_key_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_lookup_by_key_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak
import rlp

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def hp_encode(nibbles, is_leaf):
    flag = 2 if is_leaf else 0
    if len(nibbles) % 2 == 1:
        flag |= 1
        result = bytes([flag * 0x10 + nibbles[0]])
        nibbles = nibbles[1:]
    else:
        result = bytes([flag * 0x10])
    for i in range(0, len(nibbles), 2):
        result += bytes([nibbles[i] * 0x10 + nibbles[i+1]])
    return result

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xf)
    return out

def build_ssz_section(elements):
    n = len(elements)
    if n == 0:
        return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    for e in elements:
        section += e
    return section

mode = '$mode'
parts = mode.split()
which = parts[0]

if which == 'single_leaf':
    lookup_key = bytes.fromhex(parts[1])
    value = bytes.fromhex(parts[2])
    trie_key = lookup_key  # trie has the same key
    path = bytes_to_nibbles(k256(trie_key))
    leaf = leaf_node(path, value)
    root_hash = k256(leaf)
    witness_section = build_ssz_section([leaf])
    expected_status = 0
    expected_value = value
elif which == 'miss':
    lookup_key = bytes.fromhex(parts[1])
    other_key = bytes.fromhex(parts[2])
    value = bytes.fromhex(parts[3])
    # Trie keyed by other_key, but we look up lookup_key.
    path = bytes_to_nibbles(k256(other_key))
    leaf = leaf_node(path, value)
    root_hash = k256(leaf)
    witness_section = build_ssz_section([leaf])
    expected_status = 1
    expected_value = b''
elif which == 'empty_witness':
    lookup_key = bytes.fromhex(parts[1])
    root_hash = b'\x00' * 32
    witness_section = b''
    expected_status = 1
    expected_value = b''

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(witness_section)))      # witness_len
    f.write(struct.pack('<Q', len(lookup_key)))           # key_len
    f.write(root_hash)                                    # 32 bytes
    f.write(lookup_key)
    f.write(witness_section)
    total = 8 + 8 + 32 + len(lookup_key) + len(witness_section)
    pad = (-total) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected.txt', 'w') as f:
    f.write(f'{expected_status} {expected_value.hex()}')
" "$in_file"

  if [[ ! -f "$in_file.expected.txt" ]]; then
    printf "  %-26s FAIL (Python helper crashed)\n" "$name"
    return 1
  fi

  "$ZISKEMU" -e gen-out/zisk_mpt_lookup_by_key.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_lookup_by_key_${name}.emu.log" 2>&1 || true

  local expected_line expected_status expected_value_hex
  expected_line="$(cat "$in_file.expected.txt")"
  expected_status="$(echo "$expected_line" | awk '{print $1}')"
  expected_value_hex="$(echo "$expected_line" | awk '{print $2}')"
  local exp_value_byte_count=$(( ${#expected_value_hex} / 2 ))

  local actual_status actual_value_len actual_value
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_value_len="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  if (( exp_value_byte_count > 0 )); then
    actual_value="$(dd if="$out_file" bs=1 skip=16 count="$exp_value_byte_count" 2>/dev/null | xxd -p | tr -d '\n')"
  else
    actual_value=""
  fi
  local exp_status_le exp_len_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_len_le="$(python3 -c "print(int('$exp_value_byte_count').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_value_len" == "$exp_len_le" && \
        "$actual_value" == "$expected_value_hex" ]]; then
    printf "  %-26s OK   status=%d len=%d value=%s\n" \
      "$name" "$expected_status" "$exp_value_byte_count" "${expected_value_hex:0:32}"
    return 0
  else
    printf "  %-26s FAIL\n    expected: status=%d len=%d value=%s\n    actual:   status=0x%s len=0x%s value=%s\n" \
      "$name" "$expected_status" "$exp_value_byte_count" "$expected_value_hex" \
      "$actual_status" "$actual_value_len" "$actual_value"
    return 1
  fi
}

FAILED=0
# 20-byte address (state-trie shape)
ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
# Pretend account = 9-byte short string (just test bytes)
ACCT_ALICE="$(printf '0102030405060708090a' | head -c20)"

run_case "address_match"  "single_leaf $ALICE $ACCT_ALICE"               || FAILED=1
run_case "address_miss"   "miss $BOB $ALICE $ACCT_ALICE"                 || FAILED=1

# 32-byte slot key (storage-trie shape)
SLOT0="$(printf '00%.0s' $(seq 1 32))"
SLOT1="$(printf '00%.0s' $(seq 1 31); printf '01')"
# Value: a u256 stored as RLP short string
SLOTVAL="$(printf '00%.0s' $(seq 1 24); printf 'deadbeef00000000')"

run_case "slot_match"     "single_leaf $SLOT1 $SLOTVAL"                  || FAILED=1
run_case "slot_miss"      "miss $SLOT0 $SLOT1 $SLOTVAL"                  || FAILED=1

# Empty witness
run_case "empty_witness"  "empty_witness $ALICE"                         || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_lookup_by_key (state + storage shape) end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
