#!/usr/bin/env bash
# codegen-zisk-headers-keccak-array-check.sh -- PR-K16.
#
# Walks the same SSZ list section as PR-K15 but writes EVERY
# element's keccak256 digest into a caller table -- the
# foundation for `build_node_db` / `build_code_db`.
#
# Output is (N, table[0..N]) all dumped to OUTPUT, so it fits
# in ziskemu's 256-byte output cap as long as N ≤ 7.
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

echo "==> emit zisk_headers_keccak_array ELF"
lake exe codegen --program zisk_headers_keccak_array --halt linux93 \
  -o gen-out/zisk_headers_keccak_array

build_ssz_section() {
  python3 -c "
import struct, sys
elements = [bytes.fromhex(a) for a in sys.argv[1:]]
n = len(elements)
if n == 0:
    sys.stdout.write('')
    sys.exit(0)
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
  local name="$1" expected_n="$2"
  shift 2
  local elements=("$@")

  local section_hex
  section_hex="$(build_ssz_section "${elements[@]}")"

  local in_file="gen-out/zisk_headers_keccak_array_${name}.input"
  local out_file="gen-out/zisk_headers_keccak_array_${name}.output"

  python3 -c "
import struct, sys
section = bytes.fromhex('$section_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(section)))
    f.write(section)
    pad = (-(8 + len(section))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  # Expected: N (u64 LE) + N × keccak256(element)
  local elements_hex_args=""
  for e in "${elements[@]}"; do
    elements_hex_args="$elements_hex_args '$e'"
  done

  local expected_full
  expected_full="$(uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak
elements = [bytes.fromhex(a) for a in sys.argv[1:]]
out = struct.pack('<Q', len(elements))
for e in elements:
    h = keccak.new(digest_bits=256); h.update(e); out += h.digest()
print(out.hex())
" "${elements[@]}")"

  "$ZISKEMU" -e gen-out/zisk_headers_keccak_array.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"gen-out/zisk_headers_keccak_array_${name}.emu.log" 2>&1 || true

  local total_bytes=$((8 + expected_n * 32))
  local actual
  actual="$(xxd -p -l "$total_bytes" "$out_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected_full" ]]; then
    printf "  %-16s OK   N=%d (%d bytes)\n" "$name" "$expected_n" "$total_bytes"
    return 0
  else
    printf "  %-16s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected_full" "$actual"
    return 1
  fi
}

FAILED=0
run_case "empty_list"  0                                                      || FAILED=1
run_case "n1_empty"    1 ""                                                   || FAILED=1
run_case "n2_empty"    2 "" ""                                                || FAILED=1
run_case "n3_mixed"    3 "ab" "616263" "deadbeef"                             || FAILED=1
run_case "n5_varied"   5 "00" "ff" "$(printf '%02x' $(seq 0 9 | head -10 | xargs -I{} echo {}))" \
         "abcdef0123456789" "$(printf '7f%.0s' $(seq 1 64))"                  || FAILED=1
run_case "n7_full"     7 "01" "02" "03" "04" "05" "06" "07"                   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: headers_keccak_array fills the table correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
