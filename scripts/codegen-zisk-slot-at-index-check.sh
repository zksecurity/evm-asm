#!/usr/bin/env bash
# codegen-zisk-slot-at-index-check.sh -- PR-K29.
#
# Storage-trie lookup: keccak(slot_idx_be32) → MPT walk →
# RLP-decode u256. Mirrors `state.get_storage` from
# execution-specs amsterdam.
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

echo "==> emit zisk_slot_at_index ELF"
lake exe codegen --program zisk_slot_at_index --halt linux93 \
  -o gen-out/zisk_slot_at_index

REPO_ROOT="$(pwd)"

# run_case: builds a 1-slot storage trie with the given (slot, value)
# and looks up the requested slot. mode forms:
#   "hit slot_dec value_dec"
#   "miss lookup_slot_dec stored_slot_dec stored_value_dec"
#   "empty lookup_slot_dec"
run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_slot_at_index_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_slot_at_index_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_slot_at_index_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

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

if parts[0] == 'hit':
    slot_dec = int(parts[1])
    value_dec = int(parts[2])
    slot_idx_be32 = slot_dec.to_bytes(32, 'big')
    encoded_value = rlp.encode(value_dec)
    path = bytes_to_nibbles(k256(slot_idx_be32))
    leaf = leaf_node(path, encoded_value)
    root = k256(leaf)
    witness = build_ssz_section([leaf])
    lookup_be32 = slot_idx_be32
    expected_status = 0
    expected_u256 = value_dec.to_bytes(32, 'big')
elif parts[0] == 'miss':
    lookup_dec = int(parts[1])
    stored_dec = int(parts[2])
    value_dec = int(parts[3])
    stored_be32 = stored_dec.to_bytes(32, 'big')
    encoded_value = rlp.encode(value_dec)
    path = bytes_to_nibbles(k256(stored_be32))
    leaf = leaf_node(path, encoded_value)
    root = k256(leaf)
    witness = build_ssz_section([leaf])
    lookup_be32 = lookup_dec.to_bytes(32, 'big')
    expected_status = 1
    expected_u256 = b'\x00' * 32
elif parts[0] == 'empty':
    lookup_dec = int(parts[1])
    root = b'\x00' * 32
    witness = b''
    lookup_be32 = lookup_dec.to_bytes(32, 'big')
    expected_status = 1
    expected_u256 = b'\x00' * 32

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(witness)))      # witness_len
    f.write(struct.pack('<Q', 32))                # slot_len (always 32)
    f.write(root)                                 # 32 bytes
    f.write(lookup_be32)
    f.write(witness)
    total = 8 + 8 + 32 + 32 + len(witness)
    pad = (-total) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', expected_status))
    f.write(expected_u256)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_slot_at_index.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_slot_at_index_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 40 "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 40 "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   %s\n" "$name" "${expected:16:32}..."
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "slot0_value0"          "hit 0 0"                                                      || FAILED=1
run_case "slot0_value1"          "hit 0 1"                                                      || FAILED=1
run_case "slot1_value_127"       "hit 1 127"                                                    || FAILED=1
run_case "slot1_value_128"       "hit 1 128"                                                    || FAILED=1
run_case "slot1_value_256"       "hit 1 256"                                                    || FAILED=1
run_case "slot42_value_big"      "hit 42 1000000000000000000"                                   || FAILED=1
run_case "slot1_value_max_u256"  "hit 1 115792089237316195423570985008687907853269984665640564039457584007913129639935" || FAILED=1
run_case "miss_other_slot"       "miss 99 7 42"                                                 || FAILED=1
run_case "empty_witness"         "empty 1"                                                      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: slot_at_index covers slot_value 0 / 1 / 127 / 128 / 256 / 10^18 / 2^256-1 + miss/empty"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
