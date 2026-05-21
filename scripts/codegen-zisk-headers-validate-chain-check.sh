#!/usr/bin/env bash
# codegen-zisk-headers-validate-chain-check.sh -- PR-K18.
#
# Composes PR-K16 (keccak_array) + PR-K17 (parent_hash) to
# implement the SSZ-list version of `validate_headers`:
#
#   for i in 1..N:
#     assert header[i].parent_hash == keccak256(header[i-1])
#
# Build SSZ-encoded lists of minimal "headers" (RLP[Bytes32(x)])
# where x is each header's parent_hash field. The function
# should return status 0 iff every i>=1 has parent_hash equal
# to keccak256 of header[i-1]; status 1 otherwise.
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

echo "==> emit zisk_headers_validate_chain ELF"
lake exe codegen --program zisk_headers_validate_chain --halt linux93 \
  -o gen-out/zisk_headers_validate_chain

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" expected_status="$2" expected_n="$3" mode="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_headers_validate_chain_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_headers_validate_chain_${name}.output"

  # mode: "chain N" -> build a valid keccak parent_hash chain of N headers.
  #       "break N idx" -> chain of N headers where header[idx].parent_hash
  #                        is replaced with a junk value, breaking the chain.
  #       "empty"       -> N=0.
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak

def make_header(parent_hash: bytes) -> bytes:
    # RLP-encode [Bytes32(parent_hash)]: 0xc0+33 outer, 0xa0 + 32 inner
    return bytes([0xc0 + 33, 0xa0]) + parent_hash

def keccak256(b: bytes) -> bytes:
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

mode = '$mode'
parts = mode.split()
if parts[0] == 'empty':
    headers = []
elif parts[0] == 'chain':
    N = int(parts[1])
    headers = []
    prev_hash = b'\x00' * 32
    for i in range(N):
        h = make_header(prev_hash)
        headers.append(h)
        prev_hash = keccak256(h)
elif parts[0] == 'break':
    N = int(parts[1])
    idx = int(parts[2])
    headers = []
    prev_hash = b'\x00' * 32
    for i in range(N):
        if i == idx:
            ph = b'\xde\xad\xbe\xef' * 8  # junk
        else:
            ph = prev_hash
        h = make_header(ph)
        headers.append(h)
        prev_hash = keccak256(h)

n = len(headers)
section = b''
if n > 0:
    offset = 4 * n
    for h in headers:
        section += struct.pack('<I', offset)
        offset += len(h)
    for h in headers:
        section += h

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(section)))
    f.write(section)
    pad = (-(8 + len(section))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_headers_validate_chain.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_headers_validate_chain_${name}.emu.log" 2>&1 || true

  local actual_status actual_n
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_n="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_status_le expected_n_le
  expected_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  expected_n_le="$(python3 -c "print(int('$expected_n').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$expected_status_le" && "$actual_n" == "$expected_n_le" ]]; then
    printf "  %-20s OK   status=%d N=%d\n" "$name" "$expected_status" "$expected_n"
    return 0
  else
    printf "  %-20s FAIL\n    expected: status=%d N=%d\n    actual:   status=0x%s N=0x%s\n" \
      "$name" "$expected_status" "$expected_n" "$actual_status" "$actual_n"
    return 1
  fi
}

FAILED=0
run_case "empty"           0 0 "empty"      || FAILED=1
run_case "chain_1"         0 1 "chain 1"    || FAILED=1
run_case "chain_2"         0 2 "chain 2"    || FAILED=1
run_case "chain_5"         0 5 "chain 5"    || FAILED=1
run_case "broken_2"        1 2 "break 2 1"  || FAILED=1
run_case "broken_3_at_1"   1 3 "break 3 1"  || FAILED=1
run_case "broken_3_at_2"   1 3 "break 3 2"  || FAILED=1
run_case "broken_5_at_3"   1 5 "break 5 3"  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: headers_validate_chain matches Python over all 8 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
