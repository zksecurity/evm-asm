#!/usr/bin/env bash
# codegen-zisk-headers-keccak-chain-check.sh -- PR-K15.
#
# Exercises the `headers_keccak_chain` function: walk an SSZ-
# encoded list section, keccak256 each element, return the
# count and the last-element digest. Foundation for future
# header chain validation (validate_headers walks the same
# section and checks that header[i].parent_hash equals
# keccak256(header[i-1])).
#
# Input layout to the probe:
#   bytes  0.. 8 : section_len   (u64, at INPUT_ADDR + 8)
#   bytes  8..   : SSZ list section bytes
#
# Output layout:
#   bytes  0.. 8 : element count N (u64 LE, at OUTPUT_ADDR)
#   bytes  8..40 : keccak256(element[N-1]) (32 bytes)
#                  or zeros if N = 0.
#
# Fixtures cover:
#   - empty list (N = 0)
#   - one empty element (N = 1, last hash = keccak256(b""))
#   - two empty elements (N = 2, same hash)
#   - one element with bytes 0xff×32
#   - three elements (varied byte patterns)
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

echo "==> emit zisk_headers_keccak_chain ELF"
lake exe codegen --program zisk_headers_keccak_chain --halt linux93 \
  -o gen-out/zisk_headers_keccak_chain

# build_ssz_section <hex of element_0> <hex of element_1> ...
# Output: hex of the SSZ-encoded list section.
build_ssz_section() {
  python3 -c "
import struct, sys
elements = [bytes.fromhex(a) for a in sys.argv[1:]]
n = len(elements)
if n == 0:
    sys.stdout.write('')
    sys.exit(0)
# Inner offset table: n × u32 LE, where offset_i = 4*n + sum(len(e_j) for j<i)
section = b''
offset = 4 * n
for e in elements:
    section += struct.pack('<I', offset)
    offset += len(e)
for e in elements:
    section += e
sys.stdout.write(section.hex())
" "$@"
}

run_case() {
  local name="$1"
  local expected_n="$2"
  local expected_last_hash="$3"
  shift 3
  local elements=("$@")

  local section_hex
  section_hex="$(build_ssz_section "${elements[@]}")"

  local in_file="gen-out/zisk_headers_keccak_chain_${name}.input"
  local out_file="gen-out/zisk_headers_keccak_chain_${name}.output"

  python3 -c "
import struct, sys
section = bytes.fromhex('$section_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(section)))   # section_len at INPUT+8
    f.write(section)
    pad = (-(8 + len(section))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_headers_keccak_chain.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"gen-out/zisk_headers_keccak_chain_${name}.emu.log" 2>&1 || true

  local actual_n actual_hash expected_n_le
  actual_n="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  expected_n_le="$(python3 -c "print(int('$expected_n').to_bytes(8, 'little').hex())")"

  if [[ "$actual_n" == "$expected_n_le" && "$actual_hash" == "$expected_last_hash" ]]; then
    printf "  %-20s OK   N=%d hash=%s\n" "$name" "$expected_n" "$expected_last_hash"
    return 0
  else
    printf "  %-20s FAIL\n    expected: N=%d hash=%s\n    actual:   N=%s hash=%s\n" \
      "$name" "$expected_n" "$expected_last_hash" "$actual_n" "$actual_hash"
    return 1
  fi
}

# Run keccak computations via the execution-specs uv env (which
# has pycryptodome installed). Outputs a script that prints all
# 4 keccak hashes + the long-element hex on stdout, one per line.
KECCAK_RESULTS="$(uv run --directory execution-specs --quiet python3 -c "
from Crypto.Hash import keccak
def k(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.hexdigest()
print(k(b''))
print(k(b'\xff' * 32))
print(k(b'abc'))
long_b = bytes((i*7+3) & 0xff for i in range(100))
print(long_b.hex())
print(k(long_b))
")"
KECCAK_EMPTY="$(echo "$KECCAK_RESULTS" | sed -n 1p)"
KECCAK_FF32="$(echo "$KECCAK_RESULTS" | sed -n 2p)"
KECCAK_ABC="$(echo "$KECCAK_RESULTS" | sed -n 3p)"
LONG_ELEMENT_HEX="$(echo "$KECCAK_RESULTS" | sed -n 4p)"
KECCAK_LONG="$(echo "$KECCAK_RESULTS" | sed -n 5p)"

FAILED=0
run_case "empty_list"  0  "0000000000000000000000000000000000000000000000000000000000000000" || FAILED=1
run_case "n1_empty"    1  "$KECCAK_EMPTY" "" || FAILED=1
run_case "n2_empty"    2  "$KECCAK_EMPTY" "" "" || FAILED=1
run_case "n1_ff32"     1  "$KECCAK_FF32" "$(printf 'ff%.0s' $(seq 1 32))" || FAILED=1
run_case "n3_mixed"    3  "$KECCAK_LONG" "ab" "$(printf '%02x' 65)6263" "$LONG_ELEMENT_HEX" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: headers_keccak_chain matches Python over all 5 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
