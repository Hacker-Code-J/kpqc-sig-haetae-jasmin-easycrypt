#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
EC_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$EC_DIR/.." && pwd)
JASMIN_FILE="$ROOT_DIR/jasmin/hpoly.jazz"
LOG_DIR="$EC_DIR/logs"
LOG_FILE="$LOG_DIR/regenerate-extract.log"
RUN_LOG="$LOG_DIR/regenerate-extract.run.log"

. "$SCRIPT_DIR/ui.sh"

mkdir -p "$LOG_DIR"
: > "$RUN_LOG"
UI_RUN_LOG="$RUN_LOG"
RUN_START=$(date +%s)

ui_title \
  "HAETAE NTT EasyCrypt Extraction" \
  "Regenerate EasyCrypt from the full-safe constant-time Jasmin source"
ui_kv "Source" "$JASMIN_FILE"
ui_kv "Output" "$EC_DIR/Hpoly_extract.ec"
ui_kv "Log" "logs/regenerate-extract.log"
ui_kv "Run log" "logs/regenerate-extract.run.log"
ui_step "1" "1" "jasmin2ec extraction"
ui_kv "Command" "jasmin2ec --array-model=barray --output-array=$EC_DIR -o $EC_DIR/Hpoly_extract.ec $JASMIN_FILE"

set +e
jasmin2ec --array-model=barray \
  --output-array="$EC_DIR" \
  -o "$EC_DIR/Hpoly_extract.ec" \
  "$JASMIN_FILE" > "$LOG_FILE" 2>&1
extract_status="$?"
set -e

RUN_END=$(date +%s)
RUN_ELAPSED=$(ui_elapsed $((RUN_END - RUN_START)))

if [ "$extract_status" -ne 0 ]; then
  ui_fail "extraction failed after $RUN_ELAPSED"
  ui_kv "Log excerpt" "logs/regenerate-extract.log"
  ui_tail 80 "$LOG_FILE"
  exit "$extract_status"
fi

ui_pass "regenerated Hpoly_extract.ec in $RUN_ELAPSED"
ui_summary_header
ui_summary_row "Hpoly_extract.ec" "PASS" "$RUN_ELAPSED" "logs/regenerate-extract.log"
