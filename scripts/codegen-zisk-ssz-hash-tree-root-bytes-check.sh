#!/usr/bin/env bash
# codegen-zisk-ssz-hash-tree-root-bytes-check.sh -- PR-S9.
#
# Exercises the full SSZ `hash_tree_root(Bytes)` composition:
#   chunks  = pack_bytes(value)               (PR-S8)
#   partial = merkleize(chunks, limit_log2)   (PR-S7)
#   length  = u256_le(len(value))             (32-byte chunk)
#   root    = sha256(partial || length)       (PR-S2)
#
# Compares against Python's recomputation, which itself can be
# audited against the consensus-specs SSZ implementation.
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

echo "==> emit zisk_ssz_hash_tree_root_bytes ELF"
lake exe codegen --program zisk_ssz_hash_tree_root_bytes --halt linux93 \
  -o gen-out/zisk_ssz_hash_tree_root_bytes

run_case() {
  local name="$1" L="$2" limit_log2="$3" data_hex="$4"
  local in_file="gen-out/zisk_ssz_hash_tree_root_bytes_${name}.input"
  local out_file="gen-out/zisk_ssz_hash_tree_root_bytes_${name}.output"

  python3 -c "
import struct, hashlib, sys
L = $L
limit_log2 = $limit_log2
data_hex = '$data_hex'
value = bytes.fromhex(data_hex) if data_hex else b''
assert len(value) == L

# Pack
chunks = []
pad = (-L) % 32
padded = value + b'\x00' * pad
for i in range(0, len(padded), 32):
    chunks.append(padded[i:i+32])

# Zero hashes
z = [b'\x00' * 32]
for _ in range(max(limit_log2, 1) + 1):
    z.append(hashlib.sha256(z[-1]+z[-1]).digest())

# Merkleize
n = len(chunks)
if n == 0:
    partial = z[limit_log2]
else:
    M = 1
    d = 0
    while M < n:
        M *= 2
        d += 1
    cs = list(chunks) + [z[0]] * (M - n)
    while len(cs) > 1:
        cs = [hashlib.sha256(cs[2*i] + cs[2*i+1]).digest() for i in range(len(cs)//2)]
    partial = cs[0]
    while d < limit_log2:
        partial = hashlib.sha256(partial + z[d]).digest()
        d += 1

# Mix in length
length_chunk = L.to_bytes(32, 'little')
root = hashlib.sha256(partial + length_chunk).digest()

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', L))           # INPUT_ADDR + 8
    f.write(struct.pack('<Q', limit_log2))  # INPUT_ADDR + 16
    f.write(value)
    pad8 = (-(16 + L)) % 8
    if pad8:
        f.write(b'\x00' * pad8)
with open(sys.argv[2], 'w') as f:
    f.write(root.hex())
" "$in_file" "${in_file}.expected"

  "$ZISKEMU" -e gen-out/zisk_ssz_hash_tree_root_bytes.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"gen-out/zisk_ssz_hash_tree_root_bytes_${name}.emu.log" 2>&1 || true

  local actual="$(xxd -p -l 32 "$out_file" 2>/dev/null | tr -d '\n')"
  local expected="$(cat "${in_file}.expected")"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-22s OK   %s\n" "$name" "$expected"
    return 0
  else
    printf "  %-22s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
# Empty Bytes -- single u256(0) length leaf merged with Z_0:
#   partial = Z_0
#   root = sha256(Z_0 || 0_u256) = sha256(0*64) = Z_1
run_case "L0_log0"      0 0   ""                                            || FAILED=1
run_case "L0_log3"      0 3   ""                                            || FAILED=1

# Single 0x42 byte at limit_log2=0 (capacity = 32 bytes = 1 chunk)
run_case "L1_log0_42"   1 0   "42"                                          || FAILED=1

# 32 0xff bytes at limit_log2=0 (capacity = 32 bytes)
run_case "L32_log0_ff"  32 0  "$(printf 'ff%.0s' $(seq 1 32))"              || FAILED=1

# 64 0xab bytes at limit_log2=1 (capacity = 64 bytes = 2 chunks)
run_case "L64_log1_ab"  64 1  "$(printf 'ab%.0s' $(seq 1 64))"              || FAILED=1

# 100 alternating bytes at limit_log2=2 (capacity = 128 bytes = 4 chunks)
ALT_HEX="$(python3 -c "print(bytes(range(100)).hex())")"
run_case "L100_log2_alt" 100 2 "$ALT_HEX"                                   || FAILED=1

# 200 bytes at limit_log2=3 (capacity = 256 bytes = 8 chunks)
LONG_HEX="$(python3 -c "print(bytes((i*7 + 3) & 0xff for i in range(200)).hex())")"
run_case "L200_log3_seq" 200 3 "$LONG_HEX"                                  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ssz_hash_tree_root_bytes matches SSZ spec across all fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
