#!/usr/bin/env bash
# codegen-zisk-ssz-merkleize-check.sh -- PR-S7 verification.
#
# Exercises the general SSZ merkleize() over a matrix of
# (n, limit_log2) combinations with all-zero chunks. Per the
# SSZ spec, merkleize([zero]*n, capacity = 2^L) = Z_L for ANY n
# in [0, 2^L]: every leaf is zero, so the root of the depth-L
# tree is the zero-tree root Z_L.
#
# Also tests a non-zero chunk case (n=1, chunks=[0xff*32], L=2)
# against Python's recomputation, to ensure the Z_d mix-in phase
# works on non-trivial inputs.
#
# Input layout to ziskemu:
#   bytes  0..  8 : ziskemu length prefix (ignored by guest)
#   bytes  8.. 16 : limit_log2 (u64 LE)
#   bytes 16.. 24 : n (u64 LE)
#   bytes 24..    : n * 32 chunk bytes
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

echo "==> emit zisk_ssz_merkleize ELF"
lake exe codegen --program zisk_ssz_merkleize --halt linux93 \
  -o gen-out/zisk_ssz_merkleize

run_case() {
  local name="$1" n="$2" L="$3" chunks_hex="$4" expected_hex="$5"
  local in_file="gen-out/zisk_ssz_merkleize_${name}.input"
  local out_file="gen-out/zisk_ssz_merkleize_${name}.output"

  python3 -c "
import struct, sys
n = $n
L = $L
hex_in = '$chunks_hex'
chunks = bytes.fromhex(hex_in) if hex_in else b''
assert len(chunks) == n * 32, f'expected {n*32} bytes, got {len(chunks)}'
# ziskemu maps file byte 0 -> INPUT_ADDR + 8, so the file contents ARE
# the guest's view of INPUT_ADDR[8..]. Layout the guest expects:
#   INPUT_ADDR +  8..16 : L
#   INPUT_ADDR + 16..24 : n
#   INPUT_ADDR + 24..   : chunks
# which corresponds to file bytes 0..8 = L, 8..16 = n, 16.. = chunks.
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', L))
    f.write(struct.pack('<Q', n))
    f.write(chunks)
    pad = (-(16 + n * 32)) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_ssz_merkleize.elf \
    -i "$in_file" -o "$out_file" -n 800000 \
    >"gen-out/zisk_ssz_merkleize_${name}.emu.log" 2>&1 || true

  local actual="$(xxd -p -l 32 "$out_file" 2>/dev/null | tr -d '\n')"
  if [[ "$actual" == "$expected_hex" ]]; then
    printf "  %-30s OK   %s\n" "$name" "$expected_hex"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected_hex" "$actual"
    return 1
  fi
}

# Precompute Z_d table.
read -r -a ZS <<<"$(python3 -c "
import hashlib
z = [b'\x00' * 32]
for _ in range(6):
    z.append(hashlib.sha256(z[-1]+z[-1]).digest())
print(' '.join(v.hex() for v in z))
")"

FAILED=0
# All-zero cases: result is always Z_L regardless of n (when n <= 2^L)
for L in 0 1 2 3 4 5; do
  cap=$((1 << L))
  for n in 0 1 2 3 $cap; do
    if (( n > cap )); then continue; fi
    chunks_hex=""
    if (( n > 0 )); then
      chunks_hex="$(printf '00%.0s' $(seq 1 $((n*32))))"
    fi
    run_case "n${n}_L${L}_zero" "$n" "$L" "$chunks_hex" "${ZS[$L]}" || FAILED=1
  done
done

# Non-zero case: n=1, chunks=[0xff*32], L=2.
# Python reference:
#   step1 (M=1, depth_M=0): partial = chunks[0] = 0xff*32
#   step2 (mix Z_d for d=0,1):
#     partial = sha256(0xff*32 || Z_0)
#     partial = sha256(partial || Z_1)
NONZERO_HEX="$(python3 -c "
import hashlib
z = [b'\x00' * 32]
for _ in range(3):
    z.append(hashlib.sha256(z[-1]+z[-1]).digest())
r = b'\xff' * 32
r = hashlib.sha256(r + z[0]).digest()
r = hashlib.sha256(r + z[1]).digest()
print(r.hex())
")"
run_case "n1_L2_ff" 1 2 "$(printf 'ff%.0s' $(seq 1 32))" "$NONZERO_HEX" || FAILED=1

# Another non-zero: n=3, chunks=[0xaa*32, 0xbb*32, 0xcc*32], L=3.
THREE_HEX="$(python3 -c "
import hashlib
z = [b'\x00' * 32]
for _ in range(4):
    z.append(hashlib.sha256(z[-1]+z[-1]).digest())
a = b'\xaa' * 32
b = b'\xbb' * 32
c = b'\xcc' * 32
# Phase 1: M=4 (next pow2 of 3); padded = [a,b,c,Z_0]
# merkleize_pow2 level 1: [sha256(a||b), sha256(c||z0)]
# merkleize_pow2 level 2: sha256(level1_left || level1_right)
l1l = hashlib.sha256(a + b).digest()
l1r = hashlib.sha256(c + z[0]).digest()
partial = hashlib.sha256(l1l + l1r).digest()
# Phase 2: mix Z_d for d in [2, 3): just d=2
partial = hashlib.sha256(partial + z[2]).digest()
print(partial.hex())
")"
CHUNKS_3="$(printf 'aa%.0s' $(seq 1 32))$(printf 'bb%.0s' $(seq 1 32))$(printf 'cc%.0s' $(seq 1 32))"
run_case "n3_L3_abc" 3 3 "$CHUNKS_3" "$THREE_HEX" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ssz_merkleize matches SSZ spec for the entire matrix"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
