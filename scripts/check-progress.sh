#!/usr/bin/env bash
#
# check-progress.sh — CI entry point.
#
# Asserts that PROGRESS.md matches what `scripts/progress-report.sh
# --write` would emit. Fails the build on drift. Same shape as
# `scripts/check-no-warnings.sh` and friends.
#
# Why: the registry in EvmAsm/Progress.lean is the source of truth for
# the coverage tables. If a contributor adds a proven opcode but
# forgets to update PROGRESS.md, this catches it.

set -euo pipefail
cd "$(dirname "$0")/.."
exec scripts/progress-report.sh --check
