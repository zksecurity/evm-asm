#!/usr/bin/env bash
#
# progress-delta.sh — deterministic PR-level progress delta.
#
# Reads PROGRESS.md at two commits (base + head), parses the
# kernel-checked count tables and per-opcode tier table, emits a
# structured Markdown block to stdout suitable for splicing into the
# augmented-instructions file consumed by the AI PR-summary workflow.
#
# No LLM. No mutation. Pure git + awk.
#
# Usage:
#   scripts/progress-delta.sh <base-sha> <head-sha>
#
# Typical CI invocation (see .github/workflows/summary.yml):
#   scripts/progress-delta.sh \
#       "${{ github.event.pull_request.base.sha }}" \
#       "${{ github.event.pull_request.head.sha }}"
#
# Exit codes:
#   0 — emitted a delta block (possibly "metric-neutral").
#   1 — git access error or PROGRESS.md missing on one side.
#
# Idempotent: re-running on the same pair of SHAs produces identical
# output. PROGRESS.md drift is enforced separately by
# scripts/check-progress.sh, so the inputs here are trustworthy.

set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <base-sha> <head-sha>" >&2
  exit 2
fi

BASE="$1"
HEAD="$2"

cd "$(dirname "$0")/.."

# --------------------------------------------------------------------
# Fetch both versions of PROGRESS.md. If either side is missing the
# file (e.g. this PR is the one introducing PROGRESS.md), fall back
# gracefully — emit a block that flags the introduction event.
# --------------------------------------------------------------------

TMP_BASE="$(mktemp)"
TMP_HEAD="$(mktemp)"
trap 'rm -f "$TMP_BASE" "$TMP_HEAD"' EXIT

if ! git show "${BASE}:PROGRESS.md" > "$TMP_BASE" 2>/dev/null; then
  : > "$TMP_BASE"
  BASE_MISSING=1
else
  BASE_MISSING=0
fi

if ! git show "${HEAD}:PROGRESS.md" > "$TMP_HEAD" 2>/dev/null; then
  : > "$TMP_HEAD"
  HEAD_MISSING=1
else
  HEAD_MISSING=0
fi

# --------------------------------------------------------------------
# Helpers — extract a single named count from a PROGRESS.md.
# The exe (`lake exe progress-report`) renders count lines like:
#     | ✅ proven      | 43 |
# We grep the icon + label and pull the trailing integer.
# --------------------------------------------------------------------

count_field() {
  local file="$1"
  local label="$2"   # e.g. "proven", "partial", "execSpec", "notStarted"
  awk -v lbl="$label" '
    $0 ~ ("\\| (✅|🟡|⏳|✗) " lbl " *\\|") {
      # The integer is the last pipe-separated cell on this line.
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

bytes_field() {
  # Distinguish entry-count tables from byte-count tables by looking at
  # the nearest preceding section header. We rely on the rendered order:
  # the entry-count table comes first, the byte-count table second.
  # We pick the second occurrence by `awk` counting.
  local file="$1"
  local label="$2"
  awk -v lbl="$label" '
    /^By \*\*opcode byte\*\*/ { in_bytes = 1 }
    in_bytes && $0 ~ ("\\| (✅|🟡|⏳|✗) " lbl " *\\|") {
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

conformance_count() {
  local file="$1"
  awk '
    /Conformance vectors .* allConformanceVectors_length/ {
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

sorry_field() {
  local file="$1"
  awk '
    /sorry. count in/ {
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

axiom_field() {
  local file="$1"
  awk '
    /axiom. count in/ {
      n = split($0, cells, "|")
      gsub(/ /, "", cells[n-1])
      print cells[n-1]
      exit
    }
  ' "$file"
}

# --------------------------------------------------------------------
# Per-opcode tier table — extract rows of the form:
#   | <icon> <NAME> | <tier> | `<witness>` | <notes> |
# Output as: NAME<TAB>TIER per line.
# --------------------------------------------------------------------

opcode_tiers() {
  local file="$1"
  awk '
    BEGIN { in_table = 0 }
    /^### Per-opcode registry/ { in_table = 1; next }
    in_table && /^\| (✅|🟡|⏳|✗) / {
      # Strip the leading icon, then split.
      sub(/^\| (✅|🟡|⏳|✗) /, "| ", $0)
      n = split($0, cells, "|")
      # cells[2] = name, cells[3] = tier
      name = cells[2]; gsub(/^ +| +$/, "", name)
      tier = cells[3]; gsub(/^ +| +$/, "", tier)
      print name "\t" tier
    }
    in_table && /^## / { in_table = 0 }
  ' "$file"
}

# --------------------------------------------------------------------
# Compose the delta
# --------------------------------------------------------------------

# Pulls — base then head — for each tracked scalar.
B_PROVEN="$(count_field "$TMP_BASE" "proven" 2>/dev/null || echo "")"
B_PARTIAL="$(count_field "$TMP_BASE" "partial" 2>/dev/null || echo "")"
B_EXECSPEC="$(count_field "$TMP_BASE" "execSpec" 2>/dev/null || echo "")"
B_NOTSTARTED="$(count_field "$TMP_BASE" "notStarted" 2>/dev/null || echo "")"

H_PROVEN="$(count_field "$TMP_HEAD" "proven" 2>/dev/null || echo "")"
H_PARTIAL="$(count_field "$TMP_HEAD" "partial" 2>/dev/null || echo "")"
H_EXECSPEC="$(count_field "$TMP_HEAD" "execSpec" 2>/dev/null || echo "")"
H_NOTSTARTED="$(count_field "$TMP_HEAD" "notStarted" 2>/dev/null || echo "")"

B_BYTES_PROVEN="$(bytes_field "$TMP_BASE" "proven" 2>/dev/null || echo "")"
H_BYTES_PROVEN="$(bytes_field "$TMP_HEAD" "proven" 2>/dev/null || echo "")"

B_CONF="$(conformance_count "$TMP_BASE" 2>/dev/null || echo "")"
H_CONF="$(conformance_count "$TMP_HEAD" 2>/dev/null || echo "")"

B_SORRY="$(sorry_field "$TMP_BASE" 2>/dev/null || echo "")"
H_SORRY="$(sorry_field "$TMP_HEAD" 2>/dev/null || echo "")"

B_AXIOM="$(axiom_field "$TMP_BASE" 2>/dev/null || echo "")"
H_AXIOM="$(axiom_field "$TMP_HEAD" 2>/dev/null || echo "")"

# Per-opcode transitions: compare BASE→HEAD tier per opcode name.
TIER_DIFF="$(mktemp)"
trap 'rm -f "$TMP_BASE" "$TMP_HEAD" "$TIER_DIFF"' EXIT

opcode_tiers "$TMP_BASE" > "${TIER_DIFF}.base" 2>/dev/null || : > "${TIER_DIFF}.base"
opcode_tiers "$TMP_HEAD" > "${TIER_DIFF}.head" 2>/dev/null || : > "${TIER_DIFF}.head"

# Join on opcode name, emit transitions where tier differs or entry is new/removed.
TRANSITIONS="$(awk -F'\t' '
  NR == FNR { base[$1] = $2; next }
  {
    if (!($1 in base)) {
      print "+ " $1 " (new entry, tier: " $2 ")"
    } else if (base[$1] != $2) {
      print "* " $1 ": " base[$1] " → " $2
    }
    seen[$1] = 1
  }
  END {
    for (op in base) {
      if (!(op in seen)) {
        print "- " op " (removed, was: " base[op] ")"
      }
    }
  }
' "${TIER_DIFF}.base" "${TIER_DIFF}.head" 2>/dev/null || true)"

rm -f "${TIER_DIFF}.base" "${TIER_DIFF}.head"

# --------------------------------------------------------------------
# Format a count delta as "old → new (±n)" or omit if unchanged.
# --------------------------------------------------------------------

count_delta_line() {
  local label="$1" old="$2" new="$3"
  if [[ -z "$old" && -z "$new" ]]; then return; fi
  if [[ "$old" == "$new" ]]; then
    printf -- "- %s: %s (unchanged)\n" "$label" "${new:-unknown}"
  else
    local sign
    if [[ -z "$old" || -z "$new" ]]; then
      sign="?"
    else
      local delta=$((new - old))
      if (( delta >= 0 )); then sign="+${delta}"; else sign="${delta}"; fi
    fi
    printf -- "- %s: %s → %s (%s)\n" "$label" "${old:-?}" "${new:-?}" "$sign"
  fi
}

# --------------------------------------------------------------------
# Emit
# --------------------------------------------------------------------

cat <<EOF
## Computed progress delta for this PR

Inputs: \`PROGRESS.md\` at base \`${BASE:0:7}\` vs head \`${HEAD:0:7}\`.
Source is the kernel-checked registry in \`EvmAsm/Progress.lean\`;
drift between the registry and \`PROGRESS.md\` is gated separately by
\`scripts/check-progress.sh\` in CI.

EOF

if (( BASE_MISSING )); then
  echo "_Note: PROGRESS.md did not exist at base; this PR appears to introduce it._"
  echo
fi
if (( HEAD_MISSING )); then
  echo "_Note: PROGRESS.md is absent at head; downstream sections may be empty._"
  echo
fi

echo "### Count deltas"
echo
count_delta_line "proven (entries)"      "$B_PROVEN"        "$H_PROVEN"
count_delta_line "partial (entries)"     "$B_PARTIAL"       "$H_PARTIAL"
count_delta_line "execSpec (entries)"    "$B_EXECSPEC"      "$H_EXECSPEC"
count_delta_line "notStarted (entries)"  "$B_NOTSTARTED"    "$H_NOTSTARTED"
count_delta_line "proven (opcode bytes)" "$B_BYTES_PROVEN"  "$H_BYTES_PROVEN"
count_delta_line "conformance vectors"   "$B_CONF"          "$H_CONF"
count_delta_line "sorry count"           "$B_SORRY"         "$H_SORRY"
count_delta_line "axiom count"           "$B_AXIOM"         "$H_AXIOM"
echo

echo "### Per-opcode tier transitions"
echo
if [[ -z "$TRANSITIONS" ]]; then
  echo "_No tier transitions._"
else
  echo "$TRANSITIONS" | sed 's/^/    /'
fi
echo
