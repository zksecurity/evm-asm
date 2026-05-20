#!/usr/bin/env bash
# Compatibility entry point for the SDIV v4 ziskemu cases.
set -euo pipefail

cd "$(dirname "$0")/.."
exec scripts/codegen-evm_sdiv_v4-cases-check.sh "$@"
