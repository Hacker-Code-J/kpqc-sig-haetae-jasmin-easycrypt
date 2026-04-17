#!/usr/bin/env bash
# 04_callgrind.sh — Valgrind Callgrind instruction-level analysis
#
# Callgrind simulates every instruction: counts are deterministic (not
# statistical) and independent of CPU frequency or scheduler noise.
# Enables cache simulation (LL/L1D/L1I) and branch prediction simulation.
#
# Uses the *main* binary (keypair + sign + verify, one iteration each) —
# NOT the benchmark binary (10000 iters × 12 fns would take hours).
#
# Output per binary:
#   *_callgrind.out  — raw callgrind output (re-analyze with kcachegrind)
#   *_annotate.txt   — callgrind_annotate full source annotation
#   *_summary.txt    — per-function instruction counts (sorted by Ir)
set -euo pipefail
source "$(dirname "$0")/common.sh"

banner "Phase 4: Valgrind Callgrind — Instruction-Level Analysis"

OUT_DIR="$(mkresdir callgrind)"

# A76 cache geometry (from ARM Cortex-A76 TRM)
# valgrind format: <size_bytes>,<assoc>,<line_bytes>
L1D_SPEC="65536,4,64"    # 64 KiB, 4-way, 64-byte lines
L1I_SPEC="65536,4,64"    # 64 KiB, 4-way, 64-byte lines
LL_SPEC="524288,8,64"    # 512 KiB, 8-way, 64-byte lines (unified L2 per core)

log "Cache geometry: L1D=${L1D_SPEC}, L1I=${L1I_SPEC}, LL=${LL_SPEC}"
log "NOTE: Callgrind is slow (~50-100x). Each binary may take 1-5 minutes."

for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        bin="$(main_bin "$mode" "$variant")"
        bin_path="$BIN_DIR/$bin"
        cg_out="$OUT_DIR/mode${mode}_${variant}_callgrind.out"
        ann_file="$OUT_DIR/mode${mode}_${variant}_annotate.txt"
        sum_file="$OUT_DIR/mode${mode}_${variant}_summary.txt"

        # ── Run callgrind ─────────────────────────────────────────────────────
        # Callgrind simulation is deterministic — no CPU pinning needed.
        # main binary does not use PMCCNTR_EL0 so no CCR trigger needed.
        log "  mode${mode}-${variant}: valgrind --tool=callgrind on $bin"
        LD_LIBRARY_PATH="$LIB_DIR" \
        valgrind \
            --tool=callgrind \
            --callgrind-out-file="$cg_out" \
            --cache-sim=yes \
            --branch-sim=yes \
            --I1="${L1I_SPEC}" \
            --D1="${L1D_SPEC}" \
            --LL="${LL_SPEC}" \
            --collect-jumps=yes \
            --collect-systime=nsec \
            --instr-atstart=yes \
            --separate-callers=4 \
            "$bin_path" \
            > /dev/null 2>&1
        log "  → $cg_out"

        # ── Full source annotation ────────────────────────────────────────────
        logn "  mode${mode}-${variant}: callgrind_annotate (full) ... "
        {
            echo "=== HAETAE Mode${mode} ${variant^^} — Callgrind Annotate ==="
            echo "Date:          $(date)"
            echo "Binary:        $bin_path"
            echo "Cache sim:     L1D=${L1D_SPEC}, L1I=${L1I_SPEC}, LL=${LL_SPEC}"
            echo "Branch sim:    yes"
            echo ""
            callgrind_annotate \
                --auto=yes \
                --context=10 \
                --inclusive=yes \
                --threshold=0.5 \
                "$cg_out" \
                2>/dev/null
        } > "$ann_file"
        printf 'done\n'
        log "  → $ann_file"

        # ── Per-function summary (sorted by instruction count) ─────────────────
        logn "  mode${mode}-${variant}: extracting function summary ... "
        {
            echo "=== HAETAE Mode${mode} ${variant^^} — Callgrind Per-Function Summary ==="
            echo "Date:   $(date)"
            echo "Binary: $bin_path"
            echo ""
            printf "%-12s %-12s %-12s %-12s %-50s\n" \
                "Ir(calls)" "D1mr" "LLmr" "Bcm" "Function"
            printf '%s\n' "$(printf '─%.0s' {1..110})"
            # Parse the annotate output: lines with leading count + function name
            callgrind_annotate \
                --auto=no \
                --inclusive=no \
                --threshold=0.0 \
                "$cg_out" \
                2>/dev/null \
            | awk '
                /^[[:space:]]*[0-9,]+[[:space:]]/ {
                    # Remove commas from numbers
                    gsub(/,/, "")
                    # Fields: Ir [D1mr LLdr D1mw LLdw ...] function
                    if (NF >= 2) {
                        ir = $1
                        fn = $NF
                        # skip internal/runtime symbols
                        if (fn !~ /^(0x|PROGRAM|below|---|\?)/) {
                            printf "%-12s %-50s\n", ir, fn
                        }
                    }
                }
            ' \
            | sort -rn \
            | head -40
        } > "$sum_file"
        printf 'done\n'
        log "  → $sum_file"
    done
done

log "Phase 4 complete."
log "TIP: Open *.callgrind.out files in KCachegrind for interactive visualization."
