#!/usr/bin/env bash
# codegen-evm_mod-cases-check.sh — M4 corner-case verification for MOD.
#
# Builds the `evm_mod_from_input` ELF once, then loops over a list of
# (dividend, divisor) pairs: packs each into a ziskemu `-i` input file,
# runs the ELF, and diffs the first 32 bytes of the output against the
# expected remainder (computed by Python's `%` operator).
#
# Mirrors codegen-evm_div-cases-check.sh but checks remainders. The
# loop body / div128 subroutine is identical to DIV; only the epilogue
# differs (it copies u[0..3] instead of q[0..3]), so the same set of
# corner cases is useful coverage for MOD too. The two v1 div128
# counterexamples from memory/project_sdiv_div128_bug.md are included.
#
# Exit:
#   0 — every case matched its expected remainder
#   1 — emission / build / emulation failed, or any case mismatched
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

echo "==> emit evm_mod_from_input ELF"
lake exe codegen --program evm_mod_from_input --halt linux93 \
  -o gen-out/evm_mod_from_input

ELF=gen-out/evm_mod_from_input.elf
INPUT=gen-out/evm_mod_from_input.input.bin
OUTPUT=gen-out/evm_mod_from_input.output

export ZISKEMU ELF INPUT OUTPUT

python3 <<'PY'
import os, struct, subprocess, sys, pathlib

ZISKEMU = os.environ["ZISKEMU"]
ELF     = os.environ["ELF"]
INPUT   = os.environ["INPUT"]
OUTPUT  = os.environ["OUTPUT"]

# (label, dividend, divisor). Same vectors as the DIV cases script so
# DIV and MOD outputs can be cross-checked against the same operand
# layouts. Expected remainder = a % b (EVM convention: a % 0 = 0).
cases = [
    ("n1_smoke",            7,                                 2),
    ("n2_carry",            1 << 64,                           2),
    ("mod_by_zero",         42,                                0),
    ("a_lt_b_hi",           1,                                 1 << 200),
    ("a_eq_b",              0xdeadbeefcafebabe_1122334455667788_99aabbccddeeff00_0102030405060708,
                            0xdeadbeefcafebabe_1122334455667788_99aabbccddeeff00_0102030405060708),
    ("max_mod_one",         (1 << 256) - 1,                    1),
    ("max_mod_two",         (1 << 256) - 1,                    2),
    ("shift_zero_path",     1 << 255,                          1 << 255),
    ("v1_counter1",         ((1 << 63) + (1 << 33)) << 192,
                            (1 << 192) + ((1 << 33) - 1) * (1 << 128)),
    ("v1_counter2",         ((1 << 64) - 2) << 192,
                            (1 << 192) + ((1 << 64) - 2) * (1 << 128)),
    ("n4_dense",            0xfedcba9876543210_0f1e2d3c4b5a6978_8090a0b0c0d0e0f0_0011223344556677,
                            0x0000000000000003_0000000000000005_0000000000000007_000000000000000b),
    ("n3_b3_zero",          (1 << 256) - 1,                    1 << 130),
    ("max_mod_three",       (1 << 256) - 1,                    3),
    ("denorm_path",         (1 << 256) - 1,                    (1 << 250) | (1 << 130)),
]

MASK256 = (1 << 256) - 1

def pack_input(a: int, b: int) -> bytes:
    assert 0 <= a <= MASK256 and 0 <= b <= MASK256, "operands must fit in 256 bits"
    blob = a.to_bytes(32, "little") + b.to_bytes(32, "little")
    return struct.pack("<Q", len(blob)) + blob

def expected_remainder_hex(a: int, b: int) -> str:
    r = 0 if b == 0 else a % b
    return r.to_bytes(32, "little").hex()

failures = []
for label, a, b in cases:
    pathlib.Path(INPUT).write_bytes(pack_input(a, b))
    expected = expected_remainder_hex(a, b)
    log = pathlib.Path(f"gen-out/evm_mod_from_input.{label}.emu.log")
    try:
        subprocess.run(
            [ZISKEMU, "-e", ELF, "-i", INPUT, "-o", OUTPUT, "-n", "1000000"],
            check=True, stdout=log.open("wb"), stderr=subprocess.STDOUT,
        )
    except subprocess.CalledProcessError as e:
        print(f"  [FAIL] {label}: ziskemu exited {e.returncode} (see {log})")
        failures.append(label)
        continue
    actual = pathlib.Path(OUTPUT).read_bytes()[:32].hex()
    status = "PASS" if actual == expected else "FAIL"
    print(f"  [{status}] {label}")
    if actual != expected:
        print(f"         a = 0x{a:064x}")
        print(f"         b = 0x{b:064x}")
        print(f"    expected = {expected}")
        print(f"      actual = {actual}")
        failures.append(label)

print()
if failures:
    print(f"==> FAIL: {len(failures)} / {len(cases)} cases mismatched: {failures}")
    sys.exit(1)
print(f"==> PASS: all {len(cases)} cases matched expected remainders")
PY
