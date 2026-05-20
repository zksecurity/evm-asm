#!/usr/bin/env bash
# codegen-zisk-keccak-probe.sh -- PR-K1 ziskemu keccak intrinsic probe.
#
# Builds the `zisk_keccak_probe` program, runs it on ziskemu, and
# verifies the 200-byte post-permutation state matches the Keccak
# team's reference vector for keccak-f[1600] applied to a zero state.
#
# Pins the assertion that ziskemu's `_opcode_keccak` is triggered by
# a CSRS at CSR address 0x800 (state pointer in rs1), encoded as the
# 32-bit RISC-V word 0x80052073 when rs1 = a0 (x10). See:
#   - zisk-627550f4f7ac9ffb/.../ziskos/entrypoint/src/syscalls/keccakf.rs
#     (the `ziskos_syscall!(0x800, state)` macro)
#   - zisk-627550f4f7ac9ffb/.../ziskos/entrypoint/src/syscalls/syscall.rs
#     (`SYSCALL_KECCAKF_ID = 0x800`)
#   - ~/.zisk/zisk/emulator-asm/src/emu.c:507 (`_opcode_keccak`)
#
# Reference vector: 200 bytes of the keccak-f[1600] permutation
# applied to a state of 25 zero u64 limbs, as published by the
# Keccak team's IntermediateValues.txt
# (https://keccak.team/files/Keccak-reference-3.0.pdf). Limb 0 is
# the well-known 0xF1258F7940E1DDE7.
#
# Exit:
#   0 -- ziskemu output matches the reference vector
#   1 -- emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

# 400 hex chars = 200 bytes = 25 u64 LE limbs.
EXPECTED_HEX="e7dde140798f25f18a47c033f9ccd584eea95aa61e2698d54d49806f304715bd57d05362054e288bd46f8e7f2da497ffc44746a4a0e5fe90762e19d60cda5b8c9c05191bf7a630ad64fc8fd0b75a933035d617233fa95aeb0321710d26e6a6a95f55cfdb167ca58126c84703cd31b8439f56a5111a2ff20161aed9215a63e505f270c98cf2febe641166c47b95703661cb0ed04f555a7cb8c832cf1c8ae83e8c14263aae22790c94e409c5a224f94118c26504e72635f5163ba1307fe944f67549a2ec5c7bfff1ea"

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

echo "==> emit zisk_keccak_probe ELF"
lake exe codegen --program zisk_keccak_probe --halt linux93 \
  -o gen-out/zisk_keccak_probe

echo "==> ziskemu run"
"$ZISKEMU" -e gen-out/zisk_keccak_probe.elf \
  -o gen-out/zisk_keccak_probe.output -n 200000 \
  >gen-out/zisk_keccak_probe.emu.log 2>&1

ACTUAL_HEX="$(xxd -p -l 200 gen-out/zisk_keccak_probe.output | tr -d '\n')"

echo
echo "expected (200 bytes, Keccak-f[1600](0^200) reference):"
echo "  ${EXPECTED_HEX:0:80}..."
echo "actual:"
echo "  ${ACTUAL_HEX:0:80}..."
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: ziskemu keccak intrinsic round-trips correctly"
  echo "         -- CSRS 0x800, a0 (.4byte 0x80052073) triggers"
  echo "            _opcode_keccak with state pointer in a0."
  exit 0
else
  echo "==> FAIL: zisk_keccak_probe output mismatch"
  echo "expected: $EXPECTED_HEX"
  echo "actual:   $ACTUAL_HEX"
  exit 1
fi
