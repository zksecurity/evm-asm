#!/usr/bin/env bash
# codegen-zisk-account-at-address-check.sh -- PR-K28.
#
# End-to-end: (address, state_root, witness) → account fields.
# Builds a synthetic state trie with one account, looks up the
# matching and a non-matching address, verifies the decoded
# fields against Python's RLP encoder.
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

echo "==> emit zisk_account_at_address ELF"
lake exe codegen --program zisk_account_at_address --halt linux93 \
  -o gen-out/zisk_account_at_address

REPO_ROOT="$(pwd)"

# Run a fixture. mode forms:
#   "match addr_hex nonce balance storage_root_hex code_hash_hex"
#   "miss lookup_hex trie_key_hex nonce balance storage_root_hex code_hash_hex"
#   "empty_witness lookup_hex"
run_case() {
  local name="$1" mode="$2"
  local in_file="$REPO_ROOT/gen-out/zisk_account_at_address_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_at_address_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_account_at_address_${name}.expected"

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

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

mode = '$mode'
parts = mode.split()

if parts[0] == 'match':
    addr = bytes.fromhex(parts[1])
    nonce = int(parts[2])
    balance = int(parts[3])
    storage_root = bytes.fromhex(parts[4])
    code_hash = bytes.fromhex(parts[5])
    account = encode_account(nonce, balance, storage_root, code_hash)
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account)
    root = k256(leaf)
    witness = build_ssz_section([leaf])
    lookup_addr = addr
    expected = struct.pack('<Q', 0)   # status
    expected += struct.pack('<Q', nonce)
    expected += balance.to_bytes(32, 'big')
    expected += storage_root
    expected += code_hash
elif parts[0] == 'miss':
    lookup_addr = bytes.fromhex(parts[1])
    trie_key = bytes.fromhex(parts[2])
    nonce = int(parts[3])
    balance = int(parts[4])
    storage_root = bytes.fromhex(parts[5])
    code_hash = bytes.fromhex(parts[6])
    account = encode_account(nonce, balance, storage_root, code_hash)
    path = bytes_to_nibbles(k256(trie_key))
    leaf = leaf_node(path, account)
    root = k256(leaf)
    witness = build_ssz_section([leaf])
    expected = struct.pack('<Q', 1)   # status = not found
    expected += b'\x00' * 104
elif parts[0] == 'empty_witness':
    lookup_addr = bytes.fromhex(parts[1])
    root = b'\x00' * 32
    witness = b''
    expected = struct.pack('<Q', 1)
    expected += b'\x00' * 104

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(witness)))       # witness_len
    f.write(struct.pack('<Q', len(lookup_addr)))   # addr_len
    f.write(root)                                  # 32 bytes
    f.write(lookup_addr)
    f.write(witness)
    total = 8 + 8 + 32 + len(lookup_addr) + len(witness)
    pad = (-total) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_account_at_address.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_account_at_address_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
EMPTY_TRIE="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_CODE="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

FAILED=0
run_case "alice_match"     "match $ALICE 0 0 $EMPTY_TRIE $EMPTY_CODE"            || FAILED=1
run_case "alice_nonzero"   "match $ALICE 42 1000000000000000000 $EMPTY_TRIE $EMPTY_CODE" || FAILED=1
run_case "alice_big"       "match $ALICE 1 115792089237316195423570985008687907853269984665640564039457584007913129639935 $EMPTY_TRIE $EMPTY_CODE" || FAILED=1
run_case "bob_miss"        "miss $BOB $ALICE 7 99 $EMPTY_TRIE $EMPTY_CODE"       || FAILED=1
run_case "empty_witness"   "empty_witness $ALICE"                                || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_at_address (lookup + decode) end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
