#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
JASMIN_DIR="$ROOT_DIR/haetae-ref-jasmin"
LOG="$PROJECT_DIR/logs/jasmin-baseline.log"
SUMMARY="$PROJECT_DIR/logs/jasmin-baseline-summary.txt"

mkdir -p "$PROJECT_DIR/logs"

{
  printf 'HAETAE Jasmin forced-build and test summary\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Command: make -B -C %s test\n' "$JASMIN_DIR"
  printf 'Source manifest: %s\n' "$PROJECT_DIR/manifests/sources.sha256"
  printf 'Toolchain record: %s\n\n' "$PROJECT_DIR/manifests/toolchain.md"
} > "$SUMMARY"

set +e
make -B -C "$JASMIN_DIR" test > "$LOG" 2>&1
status=$?
set -e

cat "$LOG"

if [ "$status" -ne 0 ]; then
  printf 'RESULT: FAIL make-exit=%s log=%s\n' "$status" "$LOG" | tee -a "$SUMMARY"
  exit "$status"
fi

if grep -q 'Invalid on' "$LOG"; then
  printf 'RESULT: FAIL smoke-harness-reported-invalid log=%s\n' "$LOG" \
    | tee -a "$SUMMARY"
  exit 1
fi

completed_modes=$(grep -c '100%' "$LOG" || true)
if [ "$completed_modes" -lt 3 ]; then
  printf 'RESULT: FAIL completed-mode-markers=%s expected-at-least=3 log=%s\n' \
    "$completed_modes" "$LOG" | tee -a "$SUMMARY"
  exit 1
fi

printf 'Smoke completion markers: %s\n' "$completed_modes" >> "$SUMMARY"
printf 'Failure marker scan: PASS (no "Invalid on" output)\n' >> "$SUMMARY"
printf 'KAT comparison: PASS (make target and all diff commands exited 0)\n' >> "$SUMMARY"
printf 'RESULT: PASS make-exit=0 modes=3\n' | tee -a "$SUMMARY"
