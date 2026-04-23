#!/usr/bin/env bash
#
# check-imported.sh — fail if any EvmAsm/**/*.lean file is not
# transitively reachable from the EvmAsm.lean root via `import`.
#
# Tracks issue #1209: orphaned files compile only by accident (e.g.
# direct `lake build EvmAsm.X.Y`) and silently rot when the default
# `lake build` doesn't touch them.
#
# Usage:
#   scripts/check-imported.sh           # exit 1 on any orphan
#   scripts/check-imported.sh --report  # always exit 0; print summary
#
# POSIX bash, no external deps. Roots are the `EvmAsm.lean` umbrella
# (whatever it imports is "reachable") plus the umbrella sub-roots
# `EvmAsm/Rv64.lean` and `EvmAsm/Evm64.lean` so that things like
# `EvmAsm.Rv64.SailEquiv.*` count as reachable through the standard
# build entry point.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

# Convert "EvmAsm.X.Y" to "EvmAsm/X/Y.lean".
modname_to_path() {
  local m="$1"
  echo "${m//.//}.lean"
}

# Convert "EvmAsm/X/Y.lean" to "EvmAsm.X.Y".
path_to_modname() {
  local p="$1"
  p="${p%.lean}"
  echo "${p//\//.}"
}

# Reachable set: associative array of module names (paths).
declare -A reachable=()
queue=("EvmAsm.lean")

while ((${#queue[@]} > 0)); do
  cur="${queue[0]}"
  queue=("${queue[@]:1}")
  if [[ -n "${reachable[$cur]:-}" ]]; then continue; fi
  if [[ ! -f "$cur" ]]; then continue; fi
  reachable[$cur]=1
  # Parse `import EvmAsm.X.Y` lines (only EvmAsm.* imports — Mathlib /
  # Std / Lean / LeanRV64D files are not under our tree).
  while IFS= read -r mod; do
    [[ -z "$mod" ]] && continue
    p=$(modname_to_path "$mod")
    if [[ -f "$p" && -z "${reachable[$p]:-}" ]]; then
      queue+=("$p")
    fi
  done < <(grep -E '^import EvmAsm(\.[A-Za-z0-9_]+)+$' "$cur" | awk '{print $2}')
done

# Compare against every .lean under EvmAsm/.
orphans=()
while IFS= read -r f; do
  # Skip Spec.lean files: handled by their own path
  if [[ -z "${reachable[$f]:-}" ]]; then
    orphans+=("$f")
  fi
done < <(find EvmAsm -type f -name '*.lean' | sort)

if ((${#orphans[@]} == 0)); then
  echo "All $(echo "${!reachable[@]}" | wc -w) Lean files under EvmAsm/ are reachable from EvmAsm.lean."
  exit 0
fi

echo "Orphaned (never-imported) Lean files under EvmAsm/:"
for f in "${orphans[@]}"; do
  echo "  $f"
done
echo
echo "Each file above is not transitively imported from EvmAsm.lean."
echo "It will silently break when the default 'lake build' is run."
echo "Either import it from a parent module, delete it, or — if it's"
echo "intentionally standalone scaffolding — add a comment explaining"
echo "why and update this script's allow-list (see issue #1209)."

if [[ "$mode" == "report" ]]; then
  exit 0
fi
exit 1
