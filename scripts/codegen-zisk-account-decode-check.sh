#!/usr/bin/env bash
# codegen-zisk-account-decode-check.sh -- PR-K27.
#
# Decode an RLP-encoded Ethereum Account into
# (nonce, balance, storage_root, code_hash).
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

echo "==> emit zisk_account_decode ELF"
lake exe codegen --program zisk_account_decode --halt linux93 \
  -o gen-out/zisk_account_decode

REPO_ROOT="$(pwd)"

# Encode an Ethereum account as RLP and write to an input file.
# Compute the expected fixed-layout output.
run_case() {
  local name="$1" nonce="$2" balance_dec="$3" storage_root_hex="$4" code_hash_hex="$5" expected_status="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_account_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_account_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

nonce = $nonce
balance = $balance_dec
storage_root = bytes.fromhex('$storage_root_hex')
code_hash = bytes.fromhex('$code_hash_hex')
account_rlp = rlp.encode([nonce, balance, storage_root, code_hash])

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected output bytes (after status):
#   bytes  0.. 8 : status
#   bytes  8..16 : nonce (u64 LE)
#   bytes 16..48 : balance (u256 BE, left-zero-padded)
#   bytes 48..80 : storage_root
#   bytes 80..112: code_hash
import struct as _s
expected = b''
expected += _s.pack('<Q', $expected_status)
expected += _s.pack('<Q', nonce)
expected += balance.to_bytes(32, 'big')
expected += storage_root
expected += code_hash
with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_account_decode.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_account_decode_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 112 "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 112 "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   status=%d nonce=%d balance=%s...\n" \
      "$name" "$expected_status" "$nonce" "${expected:32:16}"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

# Standard empty constants.
EMPTY_TRIE="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_CODE="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

FAILED=0
run_case "empty"          0       0                  "$EMPTY_TRIE" "$EMPTY_CODE" 0  || FAILED=1
run_case "nonce_42"       42      1000000000000000000 "$EMPTY_TRIE" "$EMPTY_CODE" 0  || FAILED=1
# Max u64 nonce
run_case "max_u64_nonce"  18446744073709551615  100  "$EMPTY_TRIE" "$EMPTY_CODE" 0  || FAILED=1
# Big balance
run_case "big_balance"    1   115792089237316195423570985008687907853269984665640564039457584007913129639935  "$EMPTY_TRIE" "$EMPTY_CODE" 0  || FAILED=1
# Custom storage_root + code_hash
CUSTOM_HASH_A="$(printf 'aa%.0s' $(seq 1 32))"
CUSTOM_HASH_B="$(printf 'bb%.0s' $(seq 1 32))"
run_case "custom_hashes"  7  42  "$CUSTOM_HASH_A" "$CUSTOM_HASH_B" 0  || FAILED=1

# Malformed: not a list. Bypass Python's RLP encoder.
malformed_in="$REPO_ROOT/gen-out/zisk_account_decode_malformed.input"
malformed_out="$REPO_ROOT/gen-out/zisk_account_decode_malformed.output"
python3 -c "
import struct, sys
not_rlp_list = bytes([0x80])   # empty RLP string, not a list
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(not_rlp_list)))
    f.write(not_rlp_list)
    f.write(b'\x00' * 7)
" "$malformed_in"
"$ZISKEMU" -e gen-out/zisk_account_decode.elf -i "$malformed_in" -o "$malformed_out" -n 50000 \
  >"$REPO_ROOT/gen-out/zisk_account_decode_malformed.emu.log" 2>&1 || true
malformed_status="$(xxd -p -l 8 "$malformed_out" | tr -d '\n')"
exp_le="$(python3 -c "print((1).to_bytes(8, 'little').hex())")"
if [[ "$malformed_status" == "$exp_le" ]]; then
  printf "  %-26s OK   status=1 (parse fail)\n" "malformed_not_list"
else
  printf "  %-26s FAIL  expected status=1, got 0x%s\n" "malformed_not_list" "$malformed_status"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_decode splits account RLP into (nonce, balance, storage_root, code_hash)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
