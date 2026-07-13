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
  pattern="$1"
  shift

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
ui_kv "Coverage" "all current .ec sources except preserved legacy RefJasminNTT.ec"
ui_kv "Proof holes" "scan for admit and abort"
ui_kv "Axioms" "allowed only in GFq.ec and Montgomery.ec"
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

VERIFY_TARGETS=(
  Array256.ec
  BArray1024.ec
  WArray1024.ec
  Hpoly_extract.ec
  Fastexp.ec
  Montgomery.ec
  GFq.ec
  Rq.ec
  Fq.ec
  NTT_Fq.ec
  NTTFullSpec.ec
  NTTFullAlgebra.ec
  FunctionalSupport.ec
  Hpoly_loop.ec
  RefJasminNTTLoop.ec
  CTLoopEquiv.ec
  NTTEndToEnd.ec
)

TOTAL_STEPS=$((${#VERIFY_TARGETS[@]} + 2))
STEP=1
for target in "${VERIFY_TARGETS[@]}"
do
  compile_target "$target" "$STEP" "$TOTAL_STEPS"
  STEP=$((STEP + 1))
done

scan_log="$LOG_DIR/proof-hole-scan.log"
scan_display="logs/proof-hole-scan.log"
scan_start=$(date +%s)

ui_step "$STEP" "$TOTAL_STEPS" "Proof-hole scan"
ui_kv "Pattern" "admit | abort"
ui_kv "Log" "$scan_display"

set +e
proof_hole_scan '(^|[^[:alnum:]_])(admit|abort)([^[:alnum:]_]|$)' \
  "${VERIFY_TARGETS[@]}" > "$scan_log" 2>&1
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
  ui_fail "proof-hole scan found admit/abort markers"
  exit 1
fi

if [ "$scan_status" -ne 1 ]; then
  ui_fail "proof-hole scan command failed in $scan_elapsed"
  printf '%s|FAIL|%s|%s\n' "proof-hole scan" "$scan_elapsed" "$scan_display" >> "$SUMMARY_FILE"
  ui_cat < "$scan_log"
  print_summary
  exit "$scan_status"
fi

printf 'No admit/abort markers found in current checked proof targets.\n' > "$scan_log"
ui_pass "no proof-hole markers found in $scan_elapsed"
printf '%s|PASS|%s|%s\n' "proof-hole scan" "$scan_elapsed" "$scan_display" >> "$SUMMARY_FILE"

STEP=$((STEP + 1))
axiom_log="$LOG_DIR/axiom-boundary-scan.log"
axiom_display="logs/axiom-boundary-scan.log"
axiom_start=$(date +%s)

ui_step "$STEP" "$TOTAL_STEPS" "Axiom boundary scan"
ui_kv "Pattern" "axiom declarations"
ui_kv "Allowed" "GFq.ec, Montgomery.ec"
ui_kv "Log" "$axiom_display"

set +e
proof_hole_scan '^[[:space:]]*axiom[[:space:]]' \
  "${VERIFY_TARGETS[@]}" > "$axiom_log" 2>&1
axiom_status="$?"
set -e
axiom_end=$(date +%s)
axiom_elapsed=$(ui_elapsed $((axiom_end - axiom_start)))

if [ "$axiom_status" -eq 0 ]; then
  unexpected_axioms=$(awk -F: '$1 != "GFq.ec" && $1 != "Montgomery.ec" { print }' "$axiom_log")
  if [ "$unexpected_axioms" != "" ]; then
    ui_fail "unexpected axiom declarations found in $axiom_elapsed"
    printf '%s|FAIL|%s|%s\n' "axiom boundary scan" "$axiom_elapsed" "$axiom_display" >> "$SUMMARY_FILE"
    printf '%s\n' "$unexpected_axioms" | ui_cat
    print_summary
    echo
    ui_fail "axiom declarations escaped the expected foundational boundary"
    exit 1
  fi

  printf '\nAxiom declarations are confined to the expected foundational boundary: GFq.ec and Montgomery.ec.\n' >> "$axiom_log"
  ui_pass "axiom declarations confined to expected foundational files in $axiom_elapsed"
  printf '%s|PASS|%s|%s\n' "axiom boundary scan" "$axiom_elapsed" "$axiom_display" >> "$SUMMARY_FILE"
elif [ "$axiom_status" -eq 1 ]; then
  printf 'No axiom declarations found in current checked proof targets.\n' > "$axiom_log"
  ui_pass "no axiom declarations found in $axiom_elapsed"
  printf '%s|PASS|%s|%s\n' "axiom boundary scan" "$axiom_elapsed" "$axiom_display" >> "$SUMMARY_FILE"
else
  ui_fail "axiom boundary scan command failed in $axiom_elapsed"
  printf '%s|FAIL|%s|%s\n' "axiom boundary scan" "$axiom_elapsed" "$axiom_display" >> "$SUMMARY_FILE"
  ui_cat < "$axiom_log"
  print_summary
  exit "$axiom_status"
fi

RUN_END=$(date +%s)
RUN_ELAPSED=$(ui_elapsed $((RUN_END - RUN_START)))

print_summary
echo
ui_pass "full functional correctness proof compiled successfully in $RUN_ELAPSED"
