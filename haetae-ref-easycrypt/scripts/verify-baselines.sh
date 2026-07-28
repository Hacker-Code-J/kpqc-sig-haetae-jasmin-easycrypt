#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)

printf '\n[1/5] Checking pinned source files\n'
(cd "$PROJECT_DIR" && ./scripts/check-sources.sh)

printf '\n[2/5] Running HAETAE Jasmin tests and KAT comparisons\n'
(cd "$PROJECT_DIR" && ./scripts/verify-jasmin-baseline.sh)

printf '\n[3/5] Running the existing HAETAE security proof gate\n'
(cd "$ROOT_DIR/haetae-security" && \
  sh provable-security/verify-provable-security.sh)

printf '\n[4/5] Recompiling the HAETAE security proof without caches\n'
(cd "$PROJECT_DIR" && ./scripts/verify-security-fresh.sh)

printf '\n[5/5] Compiling the existing HAETAE NTT functional proof\n'
(cd "$ROOT_DIR/haetae-ntt-verify/easycrypt-ct" && \
  ./scripts/check-full-functional-correctness.sh)

printf '\nAll existing baseline checks passed.\n'
