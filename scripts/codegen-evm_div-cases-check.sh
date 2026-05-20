#!/usr/bin/env bash
# codegen-evm_div-cases-check.sh — M4 corner-case verification for DIV.
#
# Builds the `evm_div_from_input` ELF once, then loops over a list of
# (dividend, divisor) pairs: packs each into a ziskemu `-i` input file,
# runs the ELF, and diffs the first 32 bytes of the output against the
# expected quotient (computed by Python's true integer division).
#
# `evm_div` calls `divK_div128_v4` (see EvmAsm/Evm64/DivMod/Program.lean:717),
# so the v1 one-correction overshoot bug should NOT trip — including the
# two counterexamples that proved v1 wrong (see
# `memory/project_sdiv_div128_bug.md`).
#
# Exit:
#   0 — every case matched its expected quotient
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

echo "==> emit evm_div_from_input ELF"
lake exe codegen --program evm_div_from_input --halt linux93 \
  -o gen-out/evm_div_from_input

ELF=gen-out/evm_div_from_input.elf
INPUT=gen-out/evm_div_from_input.input.bin
OUTPUT=gen-out/evm_div_from_input.output

export ZISKEMU ELF INPUT OUTPUT

python3 <<'PY'
import os, struct, subprocess, sys, pathlib

ZISKEMU = os.environ["ZISKEMU"]
ELF     = os.environ["ELF"]
INPUT   = os.environ["INPUT"]
OUTPUT  = os.environ["OUTPUT"]

# (label, dividend, divisor). All values are arbitrary-precision Python
# ints; they're packed as 32-byte LE blobs into the ziskemu input file.
# Quotients are computed by Python's `//` (EVM convention: x // 0 = 0).
cases = [
    # n=1 single-limb fast path.
    ("n1_smoke",            6,                                 2),
    # n=2 cascade + carry across limbs (the original M2 vector).
    ("n2_carry",            1 << 64,                           2),
    # Phase A early-exit: divisor = 0 → quotient = 0 (EVM convention).
    ("divide_by_zero",      42,                                0),
    # a < b → quotient = 0; b has a high limb set so phase B picks n=4.
    ("a_lt_b_hi",           1,                                 1 << 200),
    # a == b → quotient = 1; non-trivial pattern across all four limbs.
    ("a_eq_b",              0xdeadbeefcafebabe_1122334455667788_99aabbccddeeff00_0102030405060708,
                            0xdeadbeefcafebabe_1122334455667788_99aabbccddeeff00_0102030405060708),
    # Max dividend / 1 → quotient = max 256-bit.
    ("max_div_one",         (1 << 256) - 1,                    1),
    # Max dividend / 2 → quotient = 2^255 - 1 (limb-3 high bit clear).
    ("max_div_two",         (1 << 256) - 1,                    2),
    # CLZ = 0 path (Phase C2 shift = 0): top bit of divisor's high limb set.
    ("shift_zero_path",     1 << 255,                          1 << 255),
    # v1 buggy counterexample #1 (memory: project-sdiv-div128-bug).
    # a3 = 2^63 + 2^33; b3 = 1, b2 = 2^33 - 1; rest zero.
    ("v1_counter1",         ((1 << 63) + (1 << 33)) << 192,
                            (1 << 192) + ((1 << 33) - 1) * (1 << 128)),
    # v1 buggy counterexample #2.
    # a3 = 2^64 - 2; b3 = 1, b2 = 2^64 - 2; rest zero.
    ("v1_counter2",         ((1 << 64) - 2) << 192,
                            (1 << 192) + ((1 << 64) - 2) * (1 << 128)),
    # n=4 dense vector exercising the Knuth D6 correction multiple times.
    ("n4_dense",            0xfedcba9876543210_0f1e2d3c4b5a6978_8090a0b0c0d0e0f0_0011223344556677,
                            0x0000000000000003_0000000000000005_0000000000000007_000000000000000b),
    # Phase B n=3 path: b3 = 0, b2 nonzero. Multi-iteration loop with
    # a 3-limb divisor.
    ("n3_b3_zero",          (1 << 256) - 1,                    1 << 130),
    # Large dividend / tiny divisor — multiple loop-body iterations.
    ("max_div_three",       (1 << 256) - 1,                    3),
    # Denormalize path with nonzero shift: divisor's high limb has CLZ
    # > 0 (top bit clear), forcing Phase C2 down the shift > 0 branch
    # and exercising the denorm phase at the end. Quotient ~ 2^6 = 64.
    ("denorm_path",         (1 << 256) - 1,                    (1 << 250) | (1 << 130)),
]

MASK256 = (1 << 256) - 1

def pack_input(a: int, b: int) -> bytes:
    assert 0 <= a <= MASK256 and 0 <= b <= MASK256, "operands must fit in 256 bits"
    blob = a.to_bytes(32, "little") + b.to_bytes(32, "little")
    return struct.pack("<Q", len(blob)) + blob

def expected_quotient_hex(a: int, b: int) -> str:
    q = 0 if b == 0 else a // b
    return q.to_bytes(32, "little").hex()

failures = []
for label, a, b in cases:
    pathlib.Path(INPUT).write_bytes(pack_input(a, b))
    expected = expected_quotient_hex(a, b)
    log = pathlib.Path(f"gen-out/evm_div_from_input.{label}.emu.log")
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
print(f"==> PASS: all {len(cases)} cases matched expected quotients")
PY
