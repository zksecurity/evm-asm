#!/usr/bin/env bash
# codegen-opcodes-runtime-check.sh — M8.5 runtime-bytecode test runner.
#
# Builds the M8.5 `runtime_dispatcher` ELF **once**, then iterates
# Lean-declared test cases (`EvmAsm/Codegen/Tests/Cases.lean`) packing
# each per-case bytecode into a ziskemu `-i <file>` payload and reusing
# the same dispatcher ELF.
#
# Replaces the per-case-ELF assemble + link work that
# `scripts/codegen-opcodes-check.sh` does for every case. Same expected
# outputs; ~6× faster on the macOS dev box.
#
# Adding a new opcode regression = appending one record to
# `opcodeTestCases` in `Tests/Cases.lean` — no edits to this script.
#
# Exit:
#   0 — all cases match expected
#   1 — emission / build / emulation failed, or any output mismatch
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

PYTHON="${PYTHON:-python3}"
if ! command -v "$PYTHON" >/dev/null 2>&1; then
  echo "$PYTHON not found — set PYTHON=... or install python3" >&2
  exit 1
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit + link runtime_dispatcher.elf (once)"
lake exe codegen --program runtime_dispatcher --halt linux93 -o gen-out/runtime_dispatcher

# `--list-test-cases` is a 3-column TSV: <name> <expected_hex> <bytecode_csv>.
# Single source of truth lives in `EvmAsm/Codegen/Tests/Cases.lean`.
LIST_FILE="gen-out/.opcodes-list"
lake exe codegen --list-test-cases >"$LIST_FILE"

TOTAL=0
while IFS= read -r _; do TOTAL=$((TOTAL + 1)); done <"$LIST_FILE"

if [[ "$TOTAL" -eq 0 ]]; then
  echo "==> no test cases declared in opcodeTestCases" >&2
  exit 1
fi

echo "==> running $TOTAL test case(s) through runtime_dispatcher.elf"

FAILED=()
while IFS=$'\t' read -r name expected bytecode_csv; do
  if [[ -z "$name" || -z "$expected" || -z "$bytecode_csv" ]]; then
    echo
    echo "==> SKIP: malformed --list-test-cases line (missing 1+ columns)"
    FAILED+=("${name:-<unknown>} (malformed-tsv)")
    continue
  fi

  echo
  echo "==> pack $name"
  "$PYTHON" scripts/pack-bytecode.py "$bytecode_csv" "gen-out/$name.input"

  echo "==> ziskemu -e runtime_dispatcher.elf -i gen-out/$name.input"
  "$ZISKEMU" -e gen-out/runtime_dispatcher.elf -i "gen-out/$name.input" \
    -o "gen-out/$name.output" -n 200000 \
    >"gen-out/$name.emu.log" 2>&1

  actual="$(xxd -p -c 64 -l 32 "gen-out/$name.output" | tr -d '\n')"

  echo "expected:"
  echo "  $expected"
  echo "actual:"
  echo "  $actual"

  if [[ "$actual" == "$expected" ]]; then
    echo "==> PASS: $name"
  else
    echo "==> FAIL: $name output mismatch"
    FAILED+=("$name")
  fi
done <"$LIST_FILE"

echo
if [[ ${#FAILED[@]} -eq 0 ]]; then
  echo "==> ALL PASS ($TOTAL case(s))"
  exit 0
else
  echo "==> FAIL: ${#FAILED[@]} of $TOTAL case(s) failed:"
  for f in "${FAILED[@]}"; do
    echo "    - $f"
  done
  exit 1
fi
