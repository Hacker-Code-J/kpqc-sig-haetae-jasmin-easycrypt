#!/usr/bin/env bash
# 00_setup.sh — validate profiling environment and capture system info
set -euo pipefail
source "$(dirname "$0")/common.sh"

banner "HAETAE Profiling Environment Setup"

OUT_DIR="$(mkresdir env)"
SYSINFO="$OUT_DIR/sysinfo.txt"

# ── Tool checks ────────────────────────────────────────────────────────────────
log "Checking required tools..."
MISSING=0
for tool in taskset "$PERF" valgrind callgrind_annotate; do
    if command -v "$tool" &>/dev/null || [ -x "$tool" ]; then
        log "  [OK]  $tool"
    else
        log "  [MISS] $tool — NOT FOUND"
        MISSING=1
    fi
done
[ "$MISSING" -eq 0 ] || die "Missing required tools. Install them before profiling."

# ── PMU / kernel checks ────────────────────────────────────────────────────────
log "Checking kernel PMU configuration..."

PARANOID=$(cat /proc/sys/kernel/perf_event_paranoid)
GOV=$(cat /sys/devices/system/cpu/cpu${CPU_CORE}/cpufreq/scaling_governor 2>/dev/null || echo "unknown")
CCR_LOADED=$(lsmod | grep -c enable_ccr || true)

[ "$PARANOID" -le 0 ] || {
    log "  [WARN] perf_event_paranoid=$PARANOID — full PMU requires -1"
    log "         Run: sudo sh -c 'echo -1 > /proc/sys/kernel/perf_event_paranoid'"
}
[ "$GOV" = "performance" ] || {
    log "  [WARN] CPU${CPU_CORE} governor='$GOV' — use 'performance' to prevent throttling"
    log "         Run: sudo sh -c 'echo performance > /sys/devices/system/cpu/cpu${CPU_CORE}/cpufreq/scaling_governor'"
}
[ "$CCR_LOADED" -ge 1 ] || {
    log "  [WARN] enable_ccr kernel module not loaded — PMCCNTR_EL0 access may fail"
    log "         Run: sudo insmod benchmark/enable_ccr/enable_ccr.ko"
}
RCCRLOADED=$(lsmod | grep -c reenable_ccr || true)
[ "$RCCRLOADED" -ge 1 ] || {
    log "  [WARN] reenable_ccr module not loaded — PMCCNTR_EL0 will reset on CPU idle"
    log "         Build: make -C /tmp/reenable_ccr"
    log "         Load:  sudo insmod /tmp/reenable_ccr/reenable_ccr.ko"
}
[ -w /proc/reenable_ccr ] && log "  [OK]  /proc/reenable_ccr trigger available" || true
log "  paranoid=$PARANOID  governor=$GOV  enable_ccr_loaded=$CCR_LOADED"

# ── Binary checks ─────────────────────────────────────────────────────────────
log "Checking binaries..."
for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        bin="$BIN_DIR/$(bench_bin "$mode" "$variant")"
        mbin="$BIN_DIR/$(main_bin "$mode" "$variant")"
        [ -x "$bin" ]  || die "Missing: $bin"
        [ -x "$mbin" ] || die "Missing: $mbin"
    done
done
log "  All 12 binaries present."

# ── System snapshot ────────────────────────────────────────────────────────────
log "Capturing system snapshot → $SYSINFO"
{
    echo "=== HAETAE Jazz Profiling System Info ==="
    echo "Date:      $(date)"
    echo "Hostname:  $(hostname)"
    echo ""
    echo "--- Kernel ---"
    uname -a
    echo ""
    echo "--- CPU ---"
    grep -E "^(Hardware|Processor|model name|CPU part|CPU implementer|CPU architecture|CPU variant|CPU revision|Features)" /proc/cpuinfo | sort -u
    echo ""
    echo "--- CPU Frequency (all cores) ---"
    for cpu in /sys/devices/system/cpu/cpu[0-9]*/cpufreq; do
        core=$(echo "$cpu" | grep -oP 'cpu\d+')
        freq=$(cat "$cpu/scaling_cur_freq" 2>/dev/null || echo "?")
        gov=$(cat "$cpu/scaling_governor" 2>/dev/null || echo "?")
        max=$(cat "$cpu/scaling_max_freq" 2>/dev/null || echo "?")
        printf "  %-6s  cur=%s Hz  max=%s Hz  governor=%s\n" "$core" "$freq" "$max" "$gov"
    done
    echo ""
    echo "--- Memory ---"
    grep -E "^(MemTotal|MemFree|MemAvailable|SwapTotal)" /proc/meminfo
    echo ""
    echo "--- Kernel PMU config ---"
    printf "  perf_event_paranoid: %s\n" "$(cat /proc/sys/kernel/perf_event_paranoid)"
    printf "  enable_ccr loaded:   %s\n" "$(lsmod | grep -c enable_ccr || echo 0)"
    echo ""
    echo "--- perf version ---"
    "$PERF" --version 2>&1 || true
    echo ""
    echo "--- valgrind version ---"
    valgrind --version 2>&1 || true
    echo ""
    echo "--- Binaries ---"
    for mode in "${MODES[@]}"; do
        for variant in "${VARIANTS[@]}"; do
            b="$BIN_DIR/$(bench_bin "$mode" "$variant")"
            printf "  %s\n" "$(file "$b")"
            printf "    BuildID: %s\n" "$(readelf -n "$b" 2>/dev/null | grep -oP '(?<=Build ID: )\w+')"
        done
    done
    echo ""
    echo "--- Shared libraries ---"
    ls -lh "$LIB_DIR"
} > "$SYSINFO"

cat "$SYSINFO"
log "Setup complete. System info saved to $SYSINFO"
