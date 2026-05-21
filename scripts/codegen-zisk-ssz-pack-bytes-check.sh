#!/usr/bin/env bash
# codegen-zisk-ssz-pack-bytes-check.sh -- PR-S8 verification.
#
# Exercises `ssz_pack_bytes`: copy L source bytes to a 32-byte
# chunk array, zero-pad the final chunk if needed.
#
# Output layout in OUTPUT (the probe writes both chunk_count and
# chunks so the test can diff the whole shape):
#   bytes 0..8  : chunk count (u64 LE) = ceil(L / 32)
#   bytes 8..   : ceil(L/32) * 32 chunk bytes
#
# Test fixtures cover all interesting alignment classes:
#   L = 0      → 0 chunks
#   L = 1      → 1 chunk = [src[0]] + 31 zeros
#   L = 32     → 1 chunk
#   L = 33     → 2 chunks (one full, one 1+31 padded)
#   L = 64     → 2 chunks
#   L = 100    → 4 chunks (last has 4 data + 28 padding)
#   L = 200    → 7 chunks (last has 8 data + 24 padding)
#
# ziskemu's `-o` output channel caps at 256 bytes regardless of
# how much OUTPUT_ADDR memory the guest wrote. The function's
# contract supports L up to 1024 bytes (32 chunks); larger L
# values are exercised end-to-end in PR-S9+ where the test diffs
# a single 32-byte digest of the chunks rather than the raw
# chunk array.
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

echo "==> emit zisk_ssz_pack_bytes ELF"
lake exe codegen --program zisk_ssz_pack_bytes --halt linux93 \
  -o gen-out/zisk_ssz_pack_bytes

run_case() {
  local name="$1" L="$2"
  local in_file="gen-out/zisk_ssz_pack_bytes_${name}.input"
  local out_file="gen-out/zisk_ssz_pack_bytes_${name}.output"

  python3 -c "
import struct, sys
L = $L
# Deterministic pseudo-random source bytes
src = bytes((i * 31 + 17) & 0xff for i in range(L))
chunks = (L + 31) // 32
padded = src + b'\x00' * (chunks * 32 - L)
exp_bytes = struct.pack('<Q', chunks) + padded
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', L))   # file byte 0..8 -> INPUT_ADDR + 8
    f.write(src)
    pad = (-(8 + L)) % 8
    if pad:
        f.write(b'\x00' * pad)
with open(sys.argv[2], 'wb') as f:
    f.write(exp_bytes)
" "$in_file" "$in_file.expected"

  "$ZISKEMU" -e gen-out/zisk_ssz_pack_bytes.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"gen-out/zisk_ssz_pack_bytes_${name}.emu.log" 2>&1 || true

  local out_len="$(stat -c%s "$in_file.expected")"
  local actual="$(xxd -p -l "$out_len" "$out_file" 2>/dev/null | tr -d '\n')"
  local expected="$(xxd -p "$in_file.expected" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-12s OK   (L=%d, chunks=%d)\n" "$name" "$L" "$(((L + 31) / 32))"
    return 0
  else
    printf "  %-12s FAIL (L=%d)\n    expected: %s\n    actual:   %s\n" \
      "$name" "$L" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
for L in 0 1 32 33 64 100 200; do
  run_case "L${L}" "$L" || FAILED=1
done

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ssz_pack_bytes packs all alignment classes correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
