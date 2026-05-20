# Shared terminal UI helpers for the HAETAE verification scripts.

if [ "${HAETAE_VERIFY_UI_LOADED:-0}" = "1" ]; then
  return 0 2>/dev/null || exit 0
fi
HAETAE_VERIFY_UI_LOADED=1

if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
  UI_RESET=$(printf '\033[0m')
  UI_BOLD=$(printf '\033[1m')
  UI_DIM=$(printf '\033[2m')
  UI_RED=$(printf '\033[31m')
  UI_GREEN=$(printf '\033[32m')
  UI_YELLOW=$(printf '\033[33m')
  UI_BLUE=$(printf '\033[34m')
else
  UI_RESET=
  UI_BOLD=
  UI_DIM=
  UI_RED=
  UI_GREEN=
  UI_YELLOW=
  UI_BLUE=
fi

UI_RUN_LOG=${UI_RUN_LOG:-}

ui_record() {
  printf "$@"
  if [ "${UI_RUN_LOG:-}" != "" ]; then
    printf "$@" >> "$UI_RUN_LOG"
  fi
}

ui_hr() {
  ui_record '%s\n' '----------------------------------------------------------------------'
}

ui_title() {
  ui_hr
  ui_record '%b%s%b\n' "$UI_BOLD" "$1" "$UI_RESET"
  if [ "${2:-}" != "" ]; then
    ui_record '%b%s%b\n' "$UI_DIM" "$2" "$UI_RESET"
  fi
  ui_hr
}

ui_kv() {
  ui_record '  %-12s %s\n' "$1:" "$2"
}

ui_step() {
  ui_record '\n%b[%s/%s] %s%b\n' "$UI_BLUE" "$1" "$2" "$3" "$UI_RESET"
}

ui_pass() {
  ui_record '  %b[PASS]%b %s\n' "$UI_GREEN" "$UI_RESET" "$1"
}

ui_fail() {
  ui_record '  %b[FAIL]%b %s\n' "$UI_RED" "$UI_RESET" "$1"
}

ui_warn() {
  ui_record '  %b[WARN]%b %s\n' "$UI_YELLOW" "$UI_RESET" "$1"
}

ui_info() {
  ui_record '  %b[INFO]%b %s\n' "$UI_BLUE" "$UI_RESET" "$1"
}

ui_cat() {
  if [ "${UI_RUN_LOG:-}" != "" ]; then
    tee -a "$UI_RUN_LOG"
  else
    cat
  fi
}

ui_tail() {
  lines="$1"
  file="$2"

  if [ "${UI_RUN_LOG:-}" != "" ]; then
    tail -n "$lines" "$file" | tee -a "$UI_RUN_LOG"
  else
    tail -n "$lines" "$file"
  fi
}

ui_elapsed() {
  ui_elapsed_seconds="$1"
  ui_elapsed_minutes=$((ui_elapsed_seconds / 60))
  ui_elapsed_rest=$((ui_elapsed_seconds % 60))

  if [ "$ui_elapsed_minutes" -eq 0 ]; then
    printf '%ss' "$ui_elapsed_rest"
  else
    printf '%sm %02ss' "$ui_elapsed_minutes" "$ui_elapsed_rest"
  fi
}

ui_summary_header() {
  ui_record '\n%bSummary%b\n' "$UI_BOLD" "$UI_RESET"
  ui_record '  %-34s %-8s %-10s %s\n' 'Target' 'Result' 'Elapsed' 'Log'
  ui_record '  %-34s %-8s %-10s %s\n' '------' '------' '-------' '---'
}

ui_summary_row() {
  ui_record '  %-34s %-8s %-10s %s\n' "$1" "$2" "$3" "$4"
}
