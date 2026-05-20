#!/usr/bin/env zsh
set -eu
set -o pipefail

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
EC_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
LOG_DIR="$EC_DIR/logs"
INVOCATION_DIR=$(pwd -P)
RUN_LOG="$LOG_DIR/functional-support.run.log"

. "$SCRIPT_DIR/ui.sh"

mkdir -p "$LOG_DIR"
: > "$RUN_LOG"
UI_RUN_LOG="$RUN_LOG"
RUN_START=$(date +%s)

ui_title \
  "HAETAE NTT EasyCrypt Support Check" \
  "Extraction and reusable functional theories"
ui_kv "Workspace" "$EC_DIR"
ui_kv "Logs" "$LOG_DIR"
ui_kv "Run log" "logs/functional-support.run.log"
ui_kv "Mode" "fresh EasyCrypt compile (-no-eco)"
if [ "$INVOCATION_DIR" != "$EC_DIR" ]; then
  ui_kv "Started from" "$INVOCATION_DIR"
fi

cd "$EC_DIR"

if [ ! -f "$EC_DIR/Hpoly_extract.ec" ]; then
  ui_fail "missing generated extraction"
  ui_kv "Missing" "$EC_DIR/Hpoly_extract.ec"
  ui_kv "Fix" "./scripts/regenerate-extract.sh"
  exit 2
fi

compile_target() {
  target="$1"
  log="$LOG_DIR/${target%.ec}.compile.log"
  log_display="logs/${target%.ec}.compile.log"
  step_start=$(date +%s)

  ui_step "1" "1" "$target"
  ui_kv "Command" "easycrypt compile -no-eco $target -I ."
  ui_kv "Log" "$log_display"

  set +e
  easycrypt compile -no-eco "$target" -I . > "$log" 2>&1
  ec_status="$?"
  set -e

  step_end=$(date +%s)
  step_elapsed=$(ui_elapsed $((step_end - step_start)))

  if [ "$ec_status" -eq 0 ]; then
    ui_pass "compiled in $step_elapsed"
    return 0
  fi

  ui_fail "compile failed after $step_elapsed"
  ui_kv "Log excerpt" "$log_display"
  ui_tail 80 "$log"
  return "$ec_status"
}

for target in FunctionalSupport.ec
do
  compile_target "$target"
done

RUN_END=$(date +%s)
RUN_ELAPSED=$(ui_elapsed $((RUN_END - RUN_START)))

ui_summary_header
ui_summary_row "FunctionalSupport.ec" "PASS" "$RUN_ELAPSED" "logs/FunctionalSupport.compile.log"
echo
ui_pass "functional support theories compiled successfully in $RUN_ELAPSED"
