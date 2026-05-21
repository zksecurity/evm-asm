#!/usr/bin/env bash
# codegen-zisk-headers-parent-hash-check.sh -- PR-K17.
#
# Walks past the outer RLP list prefix + Bytes32 string prefix
# to extract the first 32 bytes (parent_hash) of an RLP-encoded
# Ethereum header. Tests all outer-prefix lengths plus an
# RLP-encoded amsterdam Header.
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

echo "==> emit zisk_headers_parent_hash ELF"
lake exe codegen --program zisk_headers_parent_hash --halt linux93 \
  -o gen-out/zisk_headers_parent_hash

run_case() {
  local name="$1" status="$2" expected_hash="$3" header_hex="$4"

  local in_file="gen-out/zisk_headers_parent_hash_${name}.input"
  local out_file="gen-out/zisk_headers_parent_hash_${name}.output"

  python3 -c "
import struct, sys
header = bytes.fromhex('$header_hex') if '$header_hex' else b''
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header)))
    f.write(header)
    pad = (-(8 + len(header))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_headers_parent_hash.elf \
    -i "$in_file" -o "$out_file" -n 50000 \
    >"gen-out/zisk_headers_parent_hash_${name}.emu.log" 2>&1 || true

  local actual_status actual_hash expected_status_le
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  expected_status_le="$(python3 -c "print(int('$status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$expected_status_le" && "$actual_hash" == "$expected_hash" ]]; then
    printf "  %-20s OK   status=%d hash=%s\n" "$name" "$status" "$expected_hash"
    return 0
  else
    printf "  %-20s FAIL\n    expected: status=%d hash=%s\n    actual:   status=%s hash=%s\n" \
      "$name" "$status" "$expected_hash" "$actual_status" "$actual_hash"
    return 1
  fi
}

# --- Short list: 0xc0+ prefix (payload ≤ 55 bytes) ---
# RLP of [Bytes32(0xaa*32)]:
#   inner: 0xa0 + 32 bytes  → 33 bytes
#   outer prefix: 0xc0 + 33 = 0xe1  → 1 byte
# Total: 34 bytes
SHORT_HEADER_HEX="e1a0$(printf 'aa%.0s' $(seq 1 32))"

# --- 0xf8 (1-byte length) form ---
# RLP of [Bytes32, 23-byte filler]: outer length = 33 + (1 + 23) = 57 ≥ 56
#   inner_0: 0xa0 + bb*32   = 33 bytes
#   inner_1: 0x97 + cc*23   = 24 bytes (0x80+23 = 0x97 string prefix for 23 bytes)
#   payload = 57 bytes; outer = 0xf8 0x39 (57)
F8_HEADER_HEX="f839a0$(printf 'bb%.0s' $(seq 1 32))97$(printf 'cc%.0s' $(seq 1 23))"

# --- 0xf9 (2-byte length) form: real amsterdam header (~658 bytes) ---
REAL_HEADER_HEX="$(uv run --directory execution-specs --quiet python3 -c "
from ethereum.crypto.hash import Hash32
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes8, Bytes32
from ethereum_types.numeric import U64, U256, Uint
from ethereum.forks.amsterdam.blocks import Header
from ethereum.forks.amsterdam.fork_types import Bloom
h = Header(
    parent_hash=Hash32(b'\x11' * 32),
    ommers_hash=Hash32(b'\x22' * 32),
    coinbase=Bytes(b'\x33' * 20),
    state_root=Hash32(b'\x44' * 32),
    transactions_root=Hash32(b'\x55' * 32),
    receipt_root=Hash32(b'\x66' * 32),
    bloom=Bloom(b'\x00' * 256),
    difficulty=Uint(0),
    number=Uint(0x1234),
    gas_limit=Uint(0x1c9c380),
    gas_used=Uint(0x100),
    timestamp=U256(0x6566778899),
    extra_data=Bytes(b'evm-asm2 PR-K17'),
    prev_randao=Bytes32(b'\x77' * 32),
    nonce=Bytes8(b'\x00' * 8),
    base_fee_per_gas=Uint(0x07),
    withdrawals_root=Hash32(b'\x88' * 32),
    blob_gas_used=U64(0),
    excess_blob_gas=U64(0),
    parent_beacon_block_root=Hash32(b'\x99' * 32),
    requests_hash=Hash32(b'\xaa' * 32),
    block_access_list_hash=Hash32(b'\xbb' * 32),
)
print(rlp.encode(h).hex())
")"

# --- Parse-fail fixtures ---
# Not an RLP list (first byte < 0xc0):
NOT_LIST_HEX="80"
# Wrong inner prefix (0x80 instead of 0xa0 for a 0-byte string):
WRONG_INNER_HEX="c180"  # short list [empty bytes]

FAILED=0
run_case "short_list_aa"  0  "$(printf 'aa%.0s' $(seq 1 32))" "$SHORT_HEADER_HEX"  || FAILED=1
run_case "f8_list_bb"     0  "$(printf 'bb%.0s' $(seq 1 32))" "$F8_HEADER_HEX"     || FAILED=1
run_case "real_header"    0  "$(printf '11%.0s' $(seq 1 32))" "$REAL_HEADER_HEX"   || FAILED=1
run_case "not_list"       1  "0000000000000000000000000000000000000000000000000000000000000000" "$NOT_LIST_HEX" || FAILED=1
run_case "wrong_inner"    1  "0000000000000000000000000000000000000000000000000000000000000000" "$WRONG_INNER_HEX" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: headers_parent_hash extracts parent_hash from all RLP list shapes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
