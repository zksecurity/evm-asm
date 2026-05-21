#!/usr/bin/env bash
# codegen-zisk-bytes-to-nibbles-check.sh -- PR-K25.
#
# Convert N bytes to 2N nibbles (hi nibble first, then lo).
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

echo "==> emit zisk_bytes_to_nibbles ELF"
lake exe codegen --program zisk_bytes_to_nibbles --halt linux93 \
  -o gen-out/zisk_bytes_to_nibbles

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" src_hex="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_bytes_to_nibbles_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bytes_to_nibbles_${name}.output"

  python3 -c "
import struct, sys
src = bytes.fromhex('$src_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(src)))
    f.write(src)
    pad = (-(8 + len(src))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bytes_to_nibbles.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_bytes_to_nibbles_${name}.emu.log" 2>&1 || true

  local src_len=$(( ${#src_hex} / 2 ))
  local expected_count=$(( src_len * 2 ))
  # Expected nibbles: each byte's hi nibble then lo nibble, each as one byte.
  local expected_nibbles_hex
  expected_nibbles_hex="$(python3 -c "
src_hex = '$src_hex'
out = ''
for i in range(0, len(src_hex), 2):
    out += '0' + src_hex[i]
    out += '0' + src_hex[i+1]
print(out)
")"
  local actual_count actual_nibbles exp_count_le
  actual_count="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  exp_count_le="$(python3 -c "print(int('$expected_count').to_bytes(8, 'little').hex())")"
  if (( expected_count > 0 )); then
    actual_nibbles="$(dd if="$out_file" bs=1 skip=8 count="$expected_count" 2>/dev/null | xxd -p | tr -d '\n')"
  else
    actual_nibbles=""
  fi

  if [[ "$actual_count" == "$exp_count_le" && "$actual_nibbles" == "$expected_nibbles_hex" ]]; then
    printf "  %-26s OK   count=%d nibbles=%s\n" "$name" "$expected_count" "${expected_nibbles_hex:0:32}"
    return 0
  else
    printf "  %-26s FAIL\n    expected: count=%d nibbles=%s\n    actual:   count=0x%s nibbles=%s\n" \
      "$name" "$expected_count" "$expected_nibbles_hex" "$actual_count" "$actual_nibbles"
    return 1
  fi
}

FAILED=0
run_case "empty"        ""                                              || FAILED=1
run_case "one_byte"     "ab"                                            || FAILED=1
run_case "two_bytes"    "1234"                                          || FAILED=1
run_case "address20"    "$(printf 'cc%.0s' $(seq 1 20))"                || FAILED=1
run_case "hash32"       "0123456789abcdef$(printf 'ff%.0s' $(seq 1 24))" || FAILED=1
run_case "all_zeros"    "$(printf '00%.0s' $(seq 1 16))"                || FAILED=1
run_case "all_f"        "$(printf 'ff%.0s' $(seq 1 8))"                 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bytes_to_nibbles correctly expands all fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
