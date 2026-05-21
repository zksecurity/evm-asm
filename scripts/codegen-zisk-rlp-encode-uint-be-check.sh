#!/usr/bin/env bash
# codegen-zisk-rlp-encode-uint-be-check.sh -- PR-K30.
#
# Strip leading zeros from a BE byte array and emit canonical
# RLP encoding. Cross-checks against Python's ethereum_rlp.rlp.
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

echo "==> emit zisk_rlp_encode_uint_be ELF"
lake exe codegen --program zisk_rlp_encode_uint_be --halt linux93 \
  -o gen-out/zisk_rlp_encode_uint_be

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" src_hex="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_encode_uint_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_encode_uint_be_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

src_hex = '$src_hex'
src = bytes.fromhex(src_hex)
# Build the canonical RLP-encoded integer using execution-specs' rlp.
# The integer value is the BE interpretation of src (with leading zeros).
value = int.from_bytes(src, 'big')
expected_rlp = rlp.encode(value)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(src)))
    f.write(src)
    pad = (-(8 + len(src))) % 8
    if pad:
        f.write(b'\x00' * pad)

# expected output: u64 bytes_written + RLP bytes
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', len(expected_rlp)))
    f.write(expected_rlp)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_encode_uint_be.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_encode_uint_be_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$in_file.expected")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$in_file.expected" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   src='%s' rlp='%s'\n" "$name" "${src_hex:0:32}" "${expected:16:32}"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "zero_8b"        "0000000000000000"                                                        || FAILED=1
run_case "one_u8"         "01"                                                                       || FAILED=1
run_case "127_u8"         "7f"                                                                       || FAILED=1
run_case "128_u8"         "80"                                                                       || FAILED=1
run_case "one_u64"        "0000000000000001"                                                        || FAILED=1
run_case "max_u8_u64"     "00000000000000ff"                                                        || FAILED=1
run_case "256_u64"        "0000000000000100"                                                        || FAILED=1
run_case "10_to_18_u64"   "0000000de0b6b3a7640000"                                                  || FAILED=1
run_case "max_u64"        "ffffffffffffffff"                                                        || FAILED=1
run_case "zero_u256"      "$(printf '00%.0s' $(seq 1 32))"                                          || FAILED=1
run_case "max_u256"       "$(printf 'ff%.0s' $(seq 1 32))"                                          || FAILED=1
run_case "mixed_u256"     "0000000000000123456789abcdef000000000000000000000000000000000000"      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_encode_uint_be emits canonical RLP for all u64 / u256 forms"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
