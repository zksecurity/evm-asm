#!/usr/bin/env bash
# codegen-evm_sdiv_v4-cases-check.sh - M4 corner-case verification for SDIV v4.
#
# Builds the `evm_sdiv_v4_from_input` ELF once, then loops over signed
# (dividend, divisor) pairs: packs each into a ziskemu `-i` input file as
# 256-bit two's-complement little-endian words, runs the ELF, and diffs the
# first 32 bytes of output against the expected signed quotient.
#
# EVM SDIV truncates toward zero. Do not use Python's `//` directly for
# negative values because it rounds toward minus infinity.
#
# Exit:
#   0 - every case matched its expected signed quotient
#   1 - emission / build / emulation failed, or any case mismatched
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found - install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

SDIV_PROGRAM="${SDIV_PROGRAM:-evm_sdiv_v4_from_input}"
SDIV_ARTIFACT="${SDIV_ARTIFACT:-${SDIV_PROGRAM}}"

echo "==> lake build codegen"
lake build codegen

echo "==> emit ${SDIV_PROGRAM} ELF"
lake exe codegen --program "${SDIV_PROGRAM}" --halt linux93 \
  -o "gen-out/${SDIV_ARTIFACT}"

ELF="gen-out/${SDIV_ARTIFACT}.elf"
INPUT="gen-out/${SDIV_ARTIFACT}.input.bin"
OUTPUT="gen-out/${SDIV_ARTIFACT}.output"

export ZISKEMU ELF INPUT OUTPUT SDIV_ARTIFACT

python3 <<'PY'
import os, struct, subprocess, sys, pathlib

ZISKEMU = os.environ["ZISKEMU"]
ELF     = os.environ["ELF"]
INPUT   = os.environ["INPUT"]
OUTPUT  = os.environ["OUTPUT"]
ARTIFACT = os.environ["SDIV_ARTIFACT"]

MIN_INT = -(1 << 255)
MAX_INT = (1 << 255) - 1
MASK256 = (1 << 256) - 1

# (label, signed dividend, signed divisor). Values are packed as EVM
# 256-bit two's-complement words. Expected quotient follows EVM SDIV:
# zero on divisor 0, otherwise sign(abs(a) // abs(b)), modulo 2^256.
cases = [
    ("pos_pos_smoke",        100,                               7),
    ("neg_pos",             -100,                              7),
    ("pos_neg",             100,                              -7),
    ("neg_neg",             -100,                             -7),
    ("sdiv_by_zero",        -42,                                0),
    ("zero_dividend",       0,                                 -7),
    ("evm_overflow",        MIN_INT,                           -1),
    ("min_div_one",         MIN_INT,                            1),
    ("min_div_two",         MIN_INT,                            2),
    # High-limb signed values near the SDIV absolute-value boundary.
    ("hi_neg_pos",          -((1 << 254) + (1 << 130)),        (1 << 129) + 3),
    ("hi_pos_neg",          (1 << 254) - 12345,               -((1 << 128) + 5)),
    ("max_pos_div_three",   MAX_INT,                            3),
    ("min_plus_one_neg",    MIN_INT + 1,                       -3),
]

def to_word(x: int) -> int:
    return x & MASK256

def pack_input(a: int, b: int) -> bytes:
    blob = to_word(a).to_bytes(32, "little") + to_word(b).to_bytes(32, "little")
    return struct.pack("<Q", len(blob)) + blob

def expected_sdiv_word(a: int, b: int) -> int:
    if b == 0:
        return 0
    sign = -1 if (a < 0) ^ (b < 0) else 1
    q = sign * (abs(a) // abs(b))
    return to_word(q)

def expected_sdiv_hex(a: int, b: int) -> str:
    return expected_sdiv_word(a, b).to_bytes(32, "little").hex()

failures = []
for label, a, b in cases:
    pathlib.Path(INPUT).write_bytes(pack_input(a, b))
    expected = expected_sdiv_hex(a, b)
    log = pathlib.Path(f"gen-out/{ARTIFACT}.{label}.emu.log")
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
        print(f"         a = {a}")
        print(f"         b = {b}")
        print(f"    expected = {expected}")
        print(f"      actual = {actual}")
        failures.append(label)

print()
if failures:
    print(f"==> FAIL: {len(failures)} / {len(cases)} cases mismatched: {failures}")
    sys.exit(1)
print(f"==> PASS: all {len(cases)} cases matched expected signed quotients")
PY
