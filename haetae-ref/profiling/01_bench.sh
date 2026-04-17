#!/usr/bin/env bash
# 01_bench.sh — PMCCNTR_EL0 cycle benchmarks (10000 iterations each function)
#
# Uses the built-in WRAP_FUNC harness which reads the hardware cycle counter
# directly (enable_ccr.ko grants userspace PMCCNTR_EL0 access).
# CPU pinned to core 3 to eliminate scheduler noise.
set -euo pipefail
source "$(dirname "$0")/common.sh"

banner "Phase 1: PMCCNTR_EL0 Cycle Benchmarks"

OUT_DIR="$(mkresdir benchmarks)"

for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        bin="$(bench_bin "$mode" "$variant")"
        out="$OUT_DIR/mode${mode}_${variant}.txt"

        logn "  mode${mode}-${variant}: running $bin ... "
        {
            echo "=== HAETAE Mode${mode} ${variant^^} — Cycle Benchmark ==="
            echo "Date:   $(date)"
            echo "Binary: $BIN_DIR/$bin"
            echo "CPU:    core ${CPU_CORE}, governor=$(cat /sys/devices/system/cpu/cpu${CPU_CORE}/cpufreq/scaling_governor)"
            echo "NTESTS: 10000 (average over all iterations)"
            echo ""
        } > "$out"

        run_bin "$bin" >> "$out" 2>&1
        printf 'done\n'
        log "  → $out"
    done
done

log "Phase 1 complete."
