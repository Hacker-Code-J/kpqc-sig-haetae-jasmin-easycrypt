#!/usr/bin/env bash
# 02_perf_stat.sh — perf stat with Cortex-A76 PMU event groups
#
# Four event groups to stay within hardware counter limits (6 PMCs on A76):
#   core    — IPC, stall cycles (front/back end)
#   cache   — L1D, LLC miss rates
#   tlb     — dTLB / iTLB miss rates
#   branch  — branch misprediction rate
#
# Each group is measured separately (5 repetitions) to avoid multiplexing
# error on cycle counts. The benchmark binary is used (10000 iterations/fn)
# so event counts are large enough for reliable measurement.
set -euo pipefail
source "$(dirname "$0")/common.sh"

banner "Phase 2: perf stat — Cortex-A76 PMU Events"

OUT_DIR="$(mkresdir perf_stat)"

# Event groups — keep each group ≤ 6 events (A76 has 6 programmable PMCs)
declare -A EVENT_GROUPS
EVENT_GROUPS[core]="cycles,instructions,stalled-cycles-frontend,stalled-cycles-backend,bus-cycles"
EVENT_GROUPS[cache]="L1-dcache-loads,L1-dcache-load-misses,L1-icache-loads,L1-icache-load-misses,LLC-loads,LLC-load-misses"
EVENT_GROUPS[tlb]="dTLB-loads,dTLB-load-misses,iTLB-loads,iTLB-load-misses"
EVENT_GROUPS[branch]="branch-instructions,branch-misses"

GROUP_ORDER=(core cache tlb branch)

STAT_REPEAT=5

# Use the *main* binary (100 × keypair+sign+verify): does not use
# PMCCNTR_EL0, so PMU measurement is not affected by the CCR issue.
# 100 iterations × ~3 ms each = ~300 ms per run — plenty for accurate PMU counts.
for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        bin="$(main_bin "$mode" "$variant")"
        log "mode${mode}-${variant}: $bin (100 × keypair+sign+verify)"

        for group in "${GROUP_ORDER[@]}"; do
            events="${EVENT_GROUPS[$group]}"
            out="$OUT_DIR/mode${mode}_${variant}_${group}.txt"

            logn "  [${group}] perf stat (${STAT_REPEAT}x) ... "
            {
                echo "=== HAETAE Mode${mode} ${variant^^} — perf stat [${group}] ==="
                echo "Date:    $(date)"
                echo "Binary:  $BIN_DIR/$bin  (100 iter × keypair+sign+verify)"
                echo "Events:  $events"
                echo "Repeats: ${STAT_REPEAT}"
                echo "CPU:     core ${CPU_CORE}"
                echo ""
            } > "$out"

            LD_LIBRARY_PATH="$LIB_DIR" \
            taskset -c "$CPU_CORE" \
            "$PERF" stat \
                --repeat "$STAT_REPEAT" \
                --event "$events" \
                --detailed \
                -- "$BIN_DIR/$bin" \
                >> "$out" 2>&1

            printf 'done\n'
            log "  → $out"
        done
    done
done

log "Phase 2 complete."
