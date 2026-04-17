#!/usr/bin/env bash
# common.sh — shared variables and helpers for all profiling scripts

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BIN_DIR="$PROJECT_ROOT/build/bin"
LIB_DIR="$PROJECT_ROOT/build/lib"
RESULTS_DIR="$PROJECT_ROOT/profiling_results"

PERF="${PERF:-$(command -v perf || true)}"
[ -n "$PERF" ] || die "perf not found in PATH. Install it first."
CPU_CORE=3

MODES=(2 3 5)
VARIANTS=(ref jazz)

# Map mode+variant → binary names
bench_bin() { local m=$1 v=$2
    case "$v" in
        ref)     echo "haetae-mode${m}-benchmark"         ;;
        jazz) echo "haetae-mode${m}-benchmark-jazz" ;;
    esac
}
main_bin() { local m=$1 v=$2
    case "$v" in
        ref)     echo "haetae-mode${m}-main"         ;;
        jazz) echo "haetae-mode${m}-main-jazz" ;;
    esac
}

# Re-enable PMCCNTR_EL0 on all CPUs immediately before a run.
# Required because PMUSERENR_EL0 is reset when CPUs enter deep idle.
# /proc/reenable_ccr is provided by reenable_ccr.ko (built in /tmp/reenable_ccr/).
ccr_enable() {
    # Block deep idle on CPU_CORE so PMUSERENR_EL0 is not reset between
    # the trigger and binary startup. pm_qos_resume_latency_us=0 keeps
    # the CPU in a shallow (WFI-only) idle that preserves register state.
    local pm_qos="/sys/devices/system/cpu/cpu${CPU_CORE}/power/pm_qos_resume_latency_us"
    if [ -w "$pm_qos" ]; then
        echo 0 | sudo tee "$pm_qos" > /dev/null
    fi
    if [ -w /proc/reenable_ccr ]; then
        echo 1 | sudo tee /proc/reenable_ccr > /dev/null
    else
        log "  [WARN] /proc/reenable_ccr not writable — PMCCNTR_EL0 may be unavailable"
        log "         Load: sudo insmod /tmp/reenable_ccr/reenable_ccr.ko"
    fi
}

# Run a binary with CPU pinning and library path set
run_bin() {
    local bin="$1"; shift
    ccr_enable
    LD_LIBRARY_PATH="$LIB_DIR" taskset -c "$CPU_CORE" "$BIN_DIR/$bin" "$@"
}

# Logging helpers
log()  { printf '[%s] %s\n' "$(date '+%H:%M:%S')" "$*"; }
logn() { printf '[%s] %s' "$(date '+%H:%M:%S')" "$*"; }
die()  { printf 'ERROR: %s\n' "$*" >&2; exit 1; }

# Section banner
banner() {
    local title="$*"
    local len=${#title}
    local line
    printf -v line '%*s' $((len + 4)) ''; line="${line// /=}"
    printf '\n%s\n  %s  \n%s\n' "$line" "$title" "$line"
}

# Create result subdirectory
mkresdir() {
    local subdir="$1"
    mkdir -p "$RESULTS_DIR/$subdir"
    echo "$RESULTS_DIR/$subdir"
}
