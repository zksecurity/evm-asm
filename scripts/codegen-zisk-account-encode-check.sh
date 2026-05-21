#!/usr/bin/env bash
# codegen-zisk-account-encode-check.sh -- PR-K31.
#
# Encode (nonce, balance, storage_root, code_hash) into the
# canonical Ethereum account RLP. Cross-checks against Python's
# ethereum_rlp.rlp.encode.
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

echo "==> emit zisk_account_encode ELF"
lake exe codegen --program zisk_account_encode --halt linux93 \
  -o gen-out/zisk_account_encode

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" nonce="$2" balance="$3" storage_root_hex="$4" code_hash_hex="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_account_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_encode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_account_encode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

nonce = $nonce
balance = $balance
storage_root = bytes.fromhex('$storage_root_hex')
code_hash = bytes.fromhex('$code_hash_hex')

# Build input: 8-byte nonce BE + 32-byte balance BE + storage_root + code_hash
nonce_be = nonce.to_bytes(8, 'big')
balance_be = balance.to_bytes(32, 'big')

with open(sys.argv[1], 'wb') as f:
    f.write(nonce_be)
    f.write(balance_be)
    f.write(storage_root)
    f.write(code_hash)
    # 8 + 32 + 32 + 32 = 104 bytes; pad to multiple of 8
    pad = (-104) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected output: bytes_written (u64 LE) + RLP encoded account
expected_rlp = rlp.encode([nonce, balance, storage_root, code_hash])
with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', len(expected_rlp)))
    f.write(expected_rlp)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_account_encode.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_account_encode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   nonce=%d balance=%s%s len=%d\n" \
      "$name" "$nonce" \
      "${balance:0:8}" "$([ ${#balance} -gt 8 ] && echo '...')" \
      "$((exp_size - 8))"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

EMPTY_TRIE="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_CODE="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

FAILED=0
run_case "empty"           0     0                                                              "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "nonce_42"        42    1000000000000000000                                            "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "max_u64_nonce"   18446744073709551615   100                                           "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "big_balance"     1     115792089237316195423570985008687907853269984665640564039457584007913129639935 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "custom_hashes"   7     42                                                             "$(printf 'aa%.0s' $(seq 1 32))" "$(printf 'bb%.0s' $(seq 1 32))" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_encode produces canonical RLP for all account shapes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
