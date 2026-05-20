#!/usr/bin/env bash
# codegen-zisk-sha256-probe-le-check.sh -- PR-S1 (retry) probe.
#
# Pins the SHA-256 compression intrinsic at CSR 0x805. ziskemu
# 0.18.0 uses LE-u32-within-u64 packing for state (NOT the
# 0.15.0 source's BE-per-u64 documented in
# `ziskos/entrypoint/src/syscalls/sha256f.rs`).
#
# Empirical state layout (verified by this probe):
#   state_u64[i] in memory = bytes(LE(s_2i)) || bytes(LE(s_2i+1))
#   For SHA-256 IV: state[0] = 0xbb67ae856a09e667 (as u64) =
#     bytes 67 e6 09 6a 85 ae 67 bb in memory.
#
# Input layout (same LE-u32 packing):
#   For padded empty message: input[0] = 0x80 (only byte 0 set)
#   bytes 80 00 00 00 00 00 00 00.
#
# Post-compression state holds the 8 u32s of SHA-256("") packed
# in LE-u32 byte order. Reading the 32 bytes byte-for-byte yields
# (per 4-byte LE u32 of the canonical SHA-256(empty) = e3b0c442...):
#   42 c4 b0 e3 14 1c fc 98 c8 f4 fb 9a 24 b9 6f 99
#   e4 41 ae 27 4c 93 9b 64 1b 99 95 a4 55 b8 52 78
#
# = canonical SHA-256(b"") with each u32 group byte-swapped.
#
# PR-S2 (eventual) will add the Merkle-Damgaard wrapper that
# byte-swaps each u32 to produce canonical hash bytes for
# callers expecting the standard wire format.
set -euo pipefail

cd "$(dirname "$0")/.."

# 32 bytes = SHA-256("") packed LE-u32-within-u64.
EXPECTED_HEX="42c4b0e3141cfc98c8f4fb9a24b96f99e441ae274c939b641b9995a455b85278"

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

echo "==> emit zisk_sha256_probe_le ELF"
lake exe codegen --program zisk_sha256_probe_le --halt linux93 \
  -o gen-out/zisk_sha256_probe_le

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_sha256_probe_le.elf \
  -o gen-out/zisk_sha256_probe_le.output -n 200000 \
  >gen-out/zisk_sha256_probe_le.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 32 gen-out/zisk_sha256_probe_le.output | tr -d '\n')"

echo
echo "expected (LE-u32-packed SHA-256(b\"\")):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: ziskemu SHA-256 intrinsic pinned at CSR 0x805,"
  echo "         LE-u32-within-u64 packing."
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
