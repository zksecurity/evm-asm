#!/usr/bin/env bash
# codegen-zisk-mpt-branch-child-check.sh -- PR-K22.
#
# Extract the i-th child of an MPT branch node:
#   * 32-byte hash slot      → status=0, 32 bytes copied to out
#   * empty slot (0x80)      → status=1, output zeroed
#   * inlined RLP node       → status=2, bytes copied (zero-padded)
#   * out-of-range / fail    → status=3, output zeroed
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

echo "==> emit zisk_mpt_branch_child ELF"
lake exe codegen --program zisk_mpt_branch_child --halt linux93 \
  -o gen-out/zisk_mpt_branch_child

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" node_hex="$2" nibble="$3" \
        expected_status="$4" expected_content_hex="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_child_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_child_${name}.output"

  python3 -c "
import struct, sys
node = bytes.fromhex('$node_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node)))
    f.write(struct.pack('<Q', $nibble))
    f.write(node)
    pad = (-(16 + len(node))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_child.elf \
    -i "$in_file" -o "$out_file" -n 50000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_child_${name}.emu.log" 2>&1 || true

  local actual_status actual_content
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_content="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_content" == "$expected_content_hex" ]]; then
    printf "  %-26s OK   status=%d content=%s\n" "$name" "$expected_status" "${expected_content_hex:0:32}..."
    return 0
  else
    printf "  %-26s FAIL\n    expected: status=%d content=%s\n    actual:   status=0x%s content=%s\n" \
      "$name" "$expected_status" "$expected_content_hex" "$actual_status" "$actual_content"
    return 1
  fi
}

# Branch with one Bytes32 child at slot 5, rest empty (same as PR-K21 fixture).
# Items 0..4 = 0x80 (5 bytes), item 5 = 0xa0 + 32 0xaa (33 bytes), items 6..16 = 0x80 (11 bytes).
# Total items 17. Payload = 5 + 33 + 11 = 49. Outer = 0xc0+49 = 0xf1. Total 50.
BRANCH_5_AA="f1$(printf '80%.0s' $(seq 1 5))a0$(printf 'aa%.0s' $(seq 1 32))$(printf '80%.0s' $(seq 1 11))"

# Branch with hash at slot 0 and another at slot 15, rest empty.
# Items: 0xa0 + 32 0xaa, then 0x80 × 14, then 0xa0 + 32 0xbb, then 0x80 (slot 16).
# Total: 33 + 14 + 33 + 1 = 81. Outer = 0xf8 0x51. Total 83 bytes.
BRANCH_0_15="f851a0$(printf 'aa%.0s' $(seq 1 32))$(printf '80%.0s' $(seq 1 14))a0$(printf 'bb%.0s' $(seq 1 32))80"

# Branch with inlined RLP at slot 3 (a 31-byte inline). Slot 3 = 0x9e + 30 bytes
# (short string for 30 bytes payload = 31 bytes total).
# Slots 0..2 empty (3 bytes), slot 3 inline (31 bytes), slots 4..16 empty (13 bytes).
# Payload = 3 + 31 + 13 = 47. Outer = 0xc0+47 = 0xef. Total 48.
INLINE_BYTES="$(printf 'cd%.0s' $(seq 1 30))"
BRANCH_3_INLINE="ef$(printf '80%.0s' $(seq 1 3))9e${INLINE_BYTES}$(printf '80%.0s' $(seq 1 13))"

ZERO32="$(printf '00%.0s' $(seq 1 32))"
HASH_AA="$(printf 'aa%.0s' $(seq 1 32))"
HASH_BB="$(printf 'bb%.0s' $(seq 1 32))"
# Inline padded to 32 bytes (30 cd's + 2 zero bytes)
INLINE_PADDED="${INLINE_BYTES}0000"

FAILED=0
run_case "slot5_hash"        "$BRANCH_5_AA"     5  0 "$HASH_AA"        || FAILED=1
run_case "slot4_empty"       "$BRANCH_5_AA"     4  1 "$ZERO32"         || FAILED=1
run_case "slot0_hash"        "$BRANCH_0_15"     0  0 "$HASH_AA"        || FAILED=1
run_case "slot15_hash"       "$BRANCH_0_15"     15 0 "$HASH_BB"        || FAILED=1
run_case "slot8_empty"       "$BRANCH_0_15"     8  1 "$ZERO32"         || FAILED=1
run_case "slot3_inlined"     "$BRANCH_3_INLINE" 3  2 "$INLINE_PADDED"  || FAILED=1
run_case "slot7_empty"       "$BRANCH_3_INLINE" 7  1 "$ZERO32"         || FAILED=1
run_case "oob_nibble16"      "$BRANCH_0_15"     16 3 "$ZERO32"         || FAILED=1
run_case "oob_nibble100"     "$BRANCH_0_15"    100 3 "$ZERO32"         || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_child handles hash / empty / inlined / OOB slots"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
