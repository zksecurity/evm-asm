#!/usr/bin/env bash
# Compatibility entry point for the SMOD v4 ziskemu cases.
set -euo pipefail

cd "$(dirname "$0")/.."
exec scripts/codegen-evm_smod_v4-cases-check.sh "$@"
