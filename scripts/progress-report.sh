#!/usr/bin/env bash
#
# progress-report.sh — regenerate PROGRESS.md from the kernel-checked
# registry in EvmAsm/Progress.lean plus grep-derived numeric facts.
#
# Modes:
#   scripts/progress-report.sh --write   # regenerate PROGRESS.md
#   scripts/progress-report.sh --check   # exit non-zero if PROGRESS.md
#                                        # differs from what would be
#                                        # written. Used by CI.
#
# Design notes:
#   * Sections A.2 (opcode coverage) and B.5 (conformance count) are
#     emitted by `lake exe progress-report` — Lean-side, kernel-checked.
#   * Sections C.1 (cycle bounds), D.1 (codegen registry), and the
#     git/standards/toolchain pins are grepped here.
#   * The hand-written prose sections (L1-stack diagram, 9-item
#     guest-program checklist, narrative for axes D–H) live in
#     `scripts/progress-template.md` and are interpolated near the
#     top. Edit that template to refresh the prose without touching
#     this script.
#
# Why a bash wrapper: grepping cycle bounds across ~100 Spec.lean
# files from Lean would either spawn `IO.Process` (defeats the
# determinism argument) or require encoding the bounds as Lean defs
# (heavy). Bash + grep is cheaper and the surface is tiny.
#
# CI invariants (sorry count, axiom count, no-warnings, etc.) are
# *not* re-checked here — they are enforced by their dedicated
# CI steps. We only render a status banner.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

MODE="${1:-}"
case "$MODE" in
  --write|--check) ;;
  *) echo "usage: $0 --write | --check" >&2; exit 2 ;;
esac

# --------------------------------------------------------------------
# Pins — git commit, submodule SHAs, toolchain
# --------------------------------------------------------------------

GIT_SHA="$(git rev-parse HEAD)"
GIT_SHORT="$(git rev-parse --short HEAD)"
TODAY="$(date -u +%Y-%m-%d)"

# Submodule pins from .gitmodules + the gitlink tree entry. We don't
# require the submodule to be initialized locally.
STANDARDS_SHA="$(git ls-tree HEAD EvmAsm/Evm64/zkvm-standards | awk '{print $3}')"
EXEC_SPECS_SHA="$(git ls-tree HEAD execution-specs | awk '{print $3}')"
LEAN_TOOLCHAIN="$(cat lean-toolchain)"

# --------------------------------------------------------------------
# Lean-emitted sections (A.2 coverage, B.5 conformance)
# --------------------------------------------------------------------

LEAN_OUT="$(lake exe progress-report 2>/dev/null)"

# Conformance vector count — pull directly from the kernel-checked
# theorem. The theorem `allConformanceVectorCount_eq` has the literal
# count on its statement line (indented continuation of the theorem).
CONF_COUNT="$(grep -oE 'allConformanceVectorCount = [0-9]+' \
  EvmAsm/EL/Conformance/All.lean | head -1 | grep -oE '[0-9]+')"

# --------------------------------------------------------------------
# Section C.1 cycle bounds are carried in the registry's `notes` field
# (e.g. "N=30") so they appear inline in the per-opcode coverage table.
# A separate grep-based extraction was tried and removed: many proof
# files emit per-branch / per-limb `cpsTripleWithin N` lemmas BEFORE the
# top-level stack-spec theorem, so "first bound found" picked up
# misleading sub-spec values (e.g. BYTE=11 instead of 29, DUP=2 instead
# of 9). The right place to anchor the bound is the registry itself; a
# kernel-checked `cycleBound : Option Nat` field on `OpcodeEntry` would
# be the next step if drift becomes a concern.
# --------------------------------------------------------------------
# Section D.1/D.2 — codegen registry size and milestone status
# --------------------------------------------------------------------

codegen_registry_count() {
  grep -c '=> some' EvmAsm/Codegen/Programs.lean || echo 0
}

codegen_milestones() {
  # Source of truth: the "### Sequencing" line in CODEGEN.md uses
  # `M0 ✅ → M1 ✅ → ... → M5 (next)` to mark milestone status.
  # We pull each milestone's mark from there. Falls back to "⏳"
  # for any milestone not listed (e.g. deferred M3).
  local seq
  seq="$(grep -A2 '^### Sequencing' CODEGEN.md | tr -d '\n' || true)"
  for m in M0 M1 M2 M3 M4 M5; do
    if echo "$seq" | grep -qE "${m} ✅"; then
      printf "| %s | ✅ |\n" "$m"
    elif echo "$seq" | grep -qE "${m} \\("; then
      # Marked as (next), (deferred), etc.
      tag="$(echo "$seq" | grep -oE "${m} \\([a-z]+\\)" | head -1 | sed -E "s/${m} //")"
      printf "| %s | ⏳ %s |\n" "$m" "$tag"
    else
      printf "| %s | ⏳ |\n" "$m"
    fi
  done
}

codegen_scripts() {
  ls scripts/codegen-*.sh 2>/dev/null | wc -l | tr -d ' '
}

# --------------------------------------------------------------------
# Section A.1 — sorry / axiom invariants
# --------------------------------------------------------------------

sorry_count() { grep -rE '^\s*sorry\b' EvmAsm/ 2>/dev/null | wc -l | tr -d ' '; }
axiom_count() { grep -rE '^\s*axiom\b' EvmAsm/ 2>/dev/null | wc -l | tr -d ' '; }

# --------------------------------------------------------------------
# Compose the report
# --------------------------------------------------------------------

TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

{
cat <<EOF
# evm-asm progress

> Snapshot: \`${TODAY}\` @ [\`${GIT_SHORT}\`](https://github.com/Verified-zkEVM/evm-asm/commit/${GIT_SHA})
> Lean toolchain: \`${LEAN_TOOLCHAIN}\`
> Pinned submodules: \`eth-act/zkvm-standards@${STANDARDS_SHA:0:7}\`, \`ethereum/execution-specs@${EXEC_SPECS_SHA:0:7}\`
> Regenerated by [\`scripts/progress-report.sh\`](scripts/progress-report.sh) from the kernel-checked
> registry in [\`EvmAsm/Progress.lean\`](EvmAsm/Progress.lean). \`scripts/check-progress.sh\` runs
> in CI and fails the build if this file drifts from the regenerated output.

EOF

if [[ -f scripts/progress-template.md ]]; then
  cat scripts/progress-template.md
  echo
fi

cat <<EOF
## A.1 / H — kernel invariants

| Invariant | Status |
|---|---|
| \`sorry\` count in \`EvmAsm/\` | $(sorry_count) |
| \`axiom\` count in \`EvmAsm/\` | $(axiom_count) |
| Conformance vectors (kernel-checked, \`allConformanceVectors_length\`) | ${CONF_COUNT} |
| Build CI guardrails | \`check-no-warnings.sh\`, \`check-unbounded-cps.sh\`, \`check-unimported.sh\`, \`check-file-size.sh\` |

EOF

echo "$LEAN_OUT"
echo

cat <<EOF
## C.1 — Per-opcode cycle bounds

Worst-case \`cpsTripleWithin N\` step bounds are listed inline in the
per-opcode coverage table above (in the \`Notes\` column as \`N=…\`).
This is the verified gas-cost surrogate.

## D — Codegen reach

- Programs in \`EvmAsm/Codegen/Programs.lean\` registry: **$(codegen_registry_count)**
- ziskemu round-trip scripts: **$(codegen_scripts)** under \`scripts/codegen-*.sh\`
- Milestones (CODEGEN.md):

| Milestone | Status |
|---|---|
$(codegen_milestones)

EOF
} > "$TMP"

# --------------------------------------------------------------------
# Dispatch on mode
# --------------------------------------------------------------------

case "$MODE" in
  --write)
    mv "$TMP" PROGRESS.md
    trap - EXIT
    echo "Wrote PROGRESS.md"
    ;;
  --check)
    if [[ ! -f PROGRESS.md ]]; then
      echo "PROGRESS.md missing; run scripts/progress-report.sh --write" >&2
      exit 1
    fi
    # Ignore the `> Snapshot:` header line in the drift comparison. The
    # snapshot SHA/date is sourced from `git rev-parse HEAD` at regen
    # time and therefore changes with every commit. The intent of that
    # line is to give human readers an anchor point for the most recent
    # regeneration — it is NOT meant to lock PROGRESS.md to a specific
    # commit. Without -I, the drift gate would fire on every PR by
    # construction, even when no registry content has changed.
    if ! diff -u -I '^> Snapshot:' PROGRESS.md "$TMP"; then
      cat >&2 <<'EOF2'

PROGRESS.md is out of date relative to the kernel-checked registry in
EvmAsm/Progress.lean. To regenerate:

    scripts/progress-report.sh --write

then commit the result. If the drift is in a deterministic field
(sorry count, conformance count, …) that does not depend on the
registry, you may also need to fix the underlying source.
EOF2
      exit 1
    fi
    ;;
esac
