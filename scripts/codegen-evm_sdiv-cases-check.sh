#!/usr/bin/env bash
set -euo pipefail

# Canonical SDIV check entrypoint. The implementation delegates to the v4
# vector suite because the codegen `evm_sdiv` target is intentionally aliased
# to the corrected v4 implementation.
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec env \
  SDIV_PROGRAM="${SDIV_PROGRAM:-evm_sdiv_from_input}" \
  SDIV_ARTIFACT="${SDIV_ARTIFACT:-evm_sdiv_from_input}" \
  "${SCRIPT_DIR}/codegen-evm_sdiv_v4-cases-check.sh" "$@"
