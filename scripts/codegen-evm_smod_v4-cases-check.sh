#!/usr/bin/env bash
# codegen-evm_smod_v4-cases-check.sh - ziskemu corner-case verification for SMOD v4.
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

echo "==> lake build codegen"
lake build codegen

echo "==> emit evm_smod_v4_from_input ELF"
lake exe codegen --program evm_smod_v4_from_input --halt linux93 \
  -o gen-out/evm_smod_v4_from_input

ELF=gen-out/evm_smod_v4_from_input.elf
INPUT=gen-out/evm_smod_v4_from_input.input.bin
OUTPUT=gen-out/evm_smod_v4_from_input.output

export ZISKEMU ELF INPUT OUTPUT

python3 <<'PY'
import os, struct, subprocess, sys, pathlib

ZISKEMU = os.environ["ZISKEMU"]
ELF     = os.environ["ELF"]
INPUT   = os.environ["INPUT"]
OUTPUT  = os.environ["OUTPUT"]

MASK256 = (1 << 256) - 1
SIGNBIT = 1 << 255
MIN_INT = -(1 << 255)

def word(x: int) -> int:
    return x & MASK256

def signed(u: int) -> int:
    assert 0 <= u <= MASK256, "operands must fit in 256 bits"
    return u - (1 << 256) if u >= SIGNBIT else u

v1_counter1_a = ((1 << 63) + (1 << 33)) << 192
v1_counter1_b = (1 << 192) + ((1 << 33) - 1) * (1 << 128)
v1_counter2_a = ((1 << 64) - 2) << 192
v1_counter2_b = (1 << 192) + ((1 << 64) - 2) * (1 << 128)

cases = [
    ("pos_pos_smoke",         word(100),                         word(7)),
    ("neg_pos",               word(-100),                        word(7)),
    ("pos_neg",               word(100),                         word(-7)),
    ("neg_neg",               word(-100),                        word(-7)),
    ("smod_by_zero",          word(-42),                         word(0)),
    ("zero_dividend",         word(0),                           word(-7)),
    ("min_mod_neg_one",       word(MIN_INT),                     word(-1)),
    ("min_mod_two",           word(MIN_INT),                     word(2)),
    ("a_lt_b_signed",         word(7),                           word(-100)),
    ("dense_neg_neg",         word(-0xfedcba9876543210_0f1e2d3c4b5a6978),
                              word(-0x0000000000000003_0000000000000005)),
    ("v1_counter1_raw",       v1_counter1_a,                     v1_counter1_b),
    ("v1_counter1_flip_b",    v1_counter1_a,                     word(-signed(v1_counter1_b))),
    ("v1_counter2_raw",       v1_counter2_a,                     v1_counter2_b),
    ("v1_counter2_flip_a",    word(-signed(v1_counter2_a)),      v1_counter2_b),
]

def pack_input(a_word: int, b_word: int) -> bytes:
    assert 0 <= a_word <= MASK256 and 0 <= b_word <= MASK256, "operands must fit in 256 bits"
    blob = a_word.to_bytes(32, "little") + b_word.to_bytes(32, "little")
    return struct.pack("<Q", len(blob)) + blob

def evm_smod_word(a_word: int, b_word: int) -> int:
    a = signed(a_word)
    b = signed(b_word)
    if b == 0:
        return 0
    sign = -1 if a < 0 else 1
    return word(sign * (abs(a) % abs(b)))

failures = []
for label, a_word, b_word in cases:
    pathlib.Path(INPUT).write_bytes(pack_input(a_word, b_word))
    expected = evm_smod_word(a_word, b_word).to_bytes(32, "little").hex()
    log = pathlib.Path(f"gen-out/evm_smod_v4_from_input.{label}.emu.log")
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
        print(f"         a = 0x{a_word:064x} ({signed(a_word)})")
        print(f"         b = 0x{b_word:064x} ({signed(b_word)})")
        print(f"    expected = {expected}")
        print(f"      actual = {actual}")
        failures.append(label)

print()
if failures:
    print(f"==> FAIL: {len(failures)} / {len(cases)} cases mismatched: {failures}")
    sys.exit(1)
print(f"==> PASS: all {len(cases)} cases matched expected signed remainders")
PY
