#!/usr/bin/env zsh
set -eu
set -o pipefail

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
EC_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
LOG_DIR="$EC_DIR/logs"
INVOCATION_DIR=$(pwd -P)
SUMMARY_FILE="$LOG_DIR/full-functional-correctness.summary"
RUN_LOG="$LOG_DIR/full-functional-correctness.run.log"
MAX_EASYCRYPT_ATTEMPTS=6

. "$SCRIPT_DIR/ui.sh"

mkdir -p "$LOG_DIR"
: > "$RUN_LOG"
UI_RUN_LOG="$RUN_LOG"
RUN_START=$(date +%s)

if command -v rg >/dev/null 2>&1; then
  SEARCH_TOOL="rg"
else
  SEARCH_TOOL="grep"
fi

log_contains() {
  pattern="$1"
  file="$2"

  if [ "$SEARCH_TOOL" = "rg" ]; then
    rg -q "$pattern" "$file"
  else
    grep -q "$pattern" "$file"
  fi
}

proof_hole_scan() {
  pattern='(^|[^[:alnum:]_])(admit|abort|axiom)([^[:alnum:]_]|$)'

  if [ "$SEARCH_TOOL" = "rg" ]; then
    rg -n "$pattern" "$@"
  else
    grep -nE "$pattern" "$@"
  fi
}

ui_title \
  "HAETAE NTT EasyCrypt Verification" \
  "Full-safe constant-time functional correctness"
ui_kv "Workspace" "$EC_DIR"
ui_kv "Logs" "$LOG_DIR"
ui_kv "Run log" "logs/full-functional-correctness.run.log"
ui_kv "Mode" "fresh EasyCrypt compile (-no-eco)"
ui_kv "Proof holes" "scan for admit, abort, axiom"
ui_kv "Search" "$SEARCH_TOOL"
ui_kv "Retries" "$MAX_EASYCRYPT_ATTEMPTS EasyCrypt attempts on why3server startup failures"
if [ "$INVOCATION_DIR" != "$EC_DIR" ]; then
  ui_kv "Started from" "$INVOCATION_DIR"
fi

cd "$EC_DIR"
: > "$SUMMARY_FILE"

if [ ! -f "$EC_DIR/Hpoly_extract.ec" ]; then
  ui_fail "missing generated extraction"
  ui_kv "Missing" "$EC_DIR/Hpoly_extract.ec"
  ui_kv "Fix" "./scripts/regenerate-extract.sh"
  exit 2
fi

compile_target() {
  target="$1"
  step="$2"
  total="$3"
  log="$LOG_DIR/${target%.ec}.compile.log"
  log_display="logs/${target%.ec}.compile.log"
  attempts=0
  step_start=$(date +%s)

  ui_step "$step" "$total" "$target"
  ui_kv "Command" "easycrypt compile -no-eco $target -I ."
  ui_kv "Log" "$log_display"

  while true
  do
    attempts=$((attempts + 1))
    if [ "$attempts" -gt 1 ]; then
      ui_info "retry attempt $attempts"
    fi

    set +e
    easycrypt compile -no-eco "$target" -I . > "$log" 2>&1
    ec_status="$?"
    set -e
    step_end=$(date +%s)
    step_elapsed=$(ui_elapsed $((step_end - step_start)))

    if [ "$ec_status" -eq 0 ]; then
      ui_pass "compiled in $step_elapsed"
      printf '%s|PASS|%s|%s\n' "$target" "$step_elapsed" "$log_display" >> "$SUMMARY_FILE"
      return 0
    fi

    if [ "$attempts" -lt "$MAX_EASYCRYPT_ATTEMPTS" ] && log_contains 'cannot start & connect to why3server' "$log"; then
      retry_sleep=$attempts
      ui_warn "EasyCrypt could not start why3server; retrying after ${retry_sleep}s"
      sleep "$retry_sleep"
      continue
    fi

    ui_fail "compile failed after $step_elapsed"
    printf '%s|FAIL|%s|%s\n' "$target" "$step_elapsed" "$log_display" >> "$SUMMARY_FILE"
    ui_kv "Log excerpt" "$log_display"
    ui_tail 80 "$log"
    print_summary
    echo
    ui_fail "functional correctness proof failed while compiling $target"
    return "$ec_status"
  done
}

print_summary() {
  ui_summary_header
  while IFS='|' read -r summary_target summary_result summary_elapsed summary_log
  do
    if [ "$summary_target" != "" ]; then
      ui_summary_row "$summary_target" "$summary_result" "$summary_elapsed" "$summary_log"
    fi
  done < "$SUMMARY_FILE"
}

TOTAL_STEPS=5
STEP=1
for target in Hpoly_loop.ec RefJasminNTTLoop.ec CTLoopEquiv.ec NTTEndToEnd.ec
do
  compile_target "$target" "$STEP" "$TOTAL_STEPS"
  STEP=$((STEP + 1))
done

scan_log="$LOG_DIR/proof-hole-scan.log"
scan_display="logs/proof-hole-scan.log"
scan_start=$(date +%s)

ui_step "$STEP" "$TOTAL_STEPS" "Proof-hole scan"
ui_kv "Pattern" "admit | abort | axiom"
ui_kv "Log" "$scan_display"

set +e
proof_hole_scan \
  Hpoly_loop.ec RefJasminNTTLoop.ec CTLoopEquiv.ec \
  NTTEndToEnd.ec NTTFullAlgebra.ec NTTFullSpec.ec > "$scan_log" 2>&1
scan_status="$?"
set -e
scan_end=$(date +%s)
scan_elapsed=$(ui_elapsed $((scan_end - scan_start)))

if [ "$scan_status" -eq 0 ]; then
  ui_fail "proof-hole markers found in $scan_elapsed"
  printf '%s|FAIL|%s|%s\n' "proof-hole scan" "$scan_elapsed" "$scan_display" >> "$SUMMARY_FILE"
  ui_cat < "$scan_log"
  print_summary
  echo
  ui_fail "proof-hole scan found admit/abort/axiom markers"
  exit 1
fi

if [ "$scan_status" -ne 1 ]; then
  ui_fail "proof-hole scan command failed in $scan_elapsed"
  printf '%s|FAIL|%s|%s\n' "proof-hole scan" "$scan_elapsed" "$scan_display" >> "$SUMMARY_FILE"
  ui_cat < "$scan_log"
  print_summary
  exit "$scan_status"
fi

printf 'No admit/abort/axiom markers found in checked proof targets.\n' > "$scan_log"
ui_pass "no proof-hole markers found in $scan_elapsed"
printf '%s|PASS|%s|%s\n' "proof-hole scan" "$scan_elapsed" "$scan_display" >> "$SUMMARY_FILE"

RUN_END=$(date +%s)
RUN_ELAPSED=$(ui_elapsed $((RUN_END - RUN_START)))

print_summary
echo
ui_pass "full functional correctness proof compiled successfully in $RUN_ELAPSED"
