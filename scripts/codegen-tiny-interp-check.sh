#!/usr/bin/env bash
# codegen-tiny-interp-check.sh — M5a verification.
#
# Builds two tiny EVM bytecode programs through codegen → as → ld,
# runs each resulting ELF on ziskemu, and diffs the first 32 bytes
# of ziskemu's public output against the expected 256-bit sum.
#
# Test cases (hardcoded in EvmAsm.Codegen.Programs):
#
#   tiny_interp_add  : PUSH1 0xFF; PUSH1 0x01; ADD; STOP
#                      → 0x100, LE limbs [0x100, 0, 0, 0]
#                      → first 8 bytes  00 01 00 00 00 00 00 00
#
#   tiny_interp_add2 : PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP
#                      → 0x60,  LE limbs [0x60, 0, 0, 0]
#                      → first 8 bytes  60 00 00 00 00 00 00 00
#
# Exit:
#   0 — both outputs match expected
#   1 — emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found — install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

check_program() {
  local prog="$1"
  local expected_hex="$2"

  echo
  echo "==> emit $prog ELF"
  lake exe codegen --program "$prog" --halt linux93 -o "gen-out/$prog"

  echo "==> ziskemu -e gen-out/$prog.elf -o gen-out/$prog.output"
  "$ZISKEMU" -e "gen-out/$prog.elf" -o "gen-out/$prog.output" -n 100000 \
    >"gen-out/$prog.emu.log" 2>&1

  local actual_hex
  actual_hex="$(xxd -p -c 64 -l 32 "gen-out/$prog.output" | tr -d '\n')"

  echo "expected:"
  echo "  $expected_hex"
  echo "actual:"
  echo "  $actual_hex"

  if [[ "$actual_hex" == "$expected_hex" ]]; then
    echo "==> PASS: $prog"
    return 0
  else
    echo "==> FAIL: $prog output mismatch"
    return 1
  fi
}

check_program tiny_interp_add  "0001000000000000000000000000000000000000000000000000000000000000"
check_program tiny_interp_add2 "6000000000000000000000000000000000000000000000000000000000000000"

echo
echo "==> ALL PASS"
