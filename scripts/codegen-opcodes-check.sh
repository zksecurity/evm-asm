#!/usr/bin/env bash
# codegen-opcodes-check.sh — generic per-opcode regression runner.
#
# Enumerates Lean-declared test cases (`EvmAsm/Codegen/Tests/Cases.lean`)
# via `lake exe codegen --list-test-cases`, then for each case:
#   1. emits an ELF via `lake exe codegen --test-case <name>` (wraps the
#      bytecode through the M5b dispatcher's `tinyInterpRegistry`)
#   2. runs it on ziskemu
#   3. diffs the first 32 bytes of ziskemu's `-o` output against the
#      case's `expectedOutHex`.
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

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

# `lake exe codegen --list-test-cases` emits `<name>\t<expectedOutHex>`
# per line; we read both columns. Single source of truth lives in
# `EvmAsm/Codegen/Tests/Cases.lean`. Uses portable `while read` so the
# script works on the macOS bash 3.2 default (no `mapfile`).

LIST_FILE="gen-out/.opcodes-list"
lake exe codegen --list-test-cases >"$LIST_FILE"

TOTAL=0
while IFS= read -r _; do TOTAL=$((TOTAL + 1)); done <"$LIST_FILE"

if [[ "$TOTAL" -eq 0 ]]; then
  echo "==> no test cases declared in opcodeTestCases" >&2
  exit 1
fi

echo "==> running $TOTAL test case(s)"

FAILED=()
# `--list-test-cases` emits TSV with `<name>\t<expected>\t<bytecode>`
# since M8.5; this legacy runner only needs name+expected, so we drop
# the 3rd column into `_bytecode_unused` to keep `read` honest.
while IFS=$'\t' read -r name expected _bytecode_unused; do
  if [[ -z "$name" || -z "$expected" ]]; then
    echo
    echo "==> SKIP: malformed --list-test-cases line"
    FAILED+=("${name:-<unknown>} (malformed-tsv)")
    continue
  fi

  echo
  echo "==> emit $name"
  lake exe codegen --test-case "$name" --halt linux93 -o "gen-out/$name"

  echo "==> ziskemu -e gen-out/$name.elf -o gen-out/$name.output"
  "$ZISKEMU" -e "gen-out/$name.elf" -o "gen-out/$name.output" -n 200000 \
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
