#!/usr/bin/env bash
# 03_perf_record.sh — perf record + annotate + call graph
#
# Records at 999 Hz using DWARF call-graph unwinding (works with -g -O2, no
# need for -fno-omit-frame-pointer). Generates three outputs per binary:
#   *.perf.data      — raw sample data (kept for re-analysis)
#   *_flat.txt       — flat profile sorted by self cycles %
#   *_callgraph.txt  — annotated call-graph (children inclusive)
#
# The benchmark binary is used: 10000 iterations per function gives enough
# samples at 999 Hz for statistically meaningful hotspot attribution.
set -euo pipefail
source "$(dirname "$0")/common.sh"

banner "Phase 3: perf record — Hotspot + Call Graph"

OUT_DIR="$(mkresdir perf_record)"

SAMPLE_FREQ=999          # Hz — below 1kHz to avoid kernel throttling
DWARF_STACKSIZE=65528    # bytes — max DWARF stack capture size

# Use the *main* binary: full keypair+sign+verify call graph.
# The benchmark binary would also work but requires PMCCNTR_EL0;
# the main binary gives the complete cryptographic flow for hotspot analysis.
for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        bin="$(main_bin "$mode" "$variant")"
        bin_path="$BIN_DIR/$bin"
        data_file="$OUT_DIR/mode${mode}_${variant}.perf.data"
        flat_file="$OUT_DIR/mode${mode}_${variant}_flat.txt"
        cg_file="$OUT_DIR/mode${mode}_${variant}_callgraph.txt"

        # ── Record ────────────────────────────────────────────────────────────
        logn "  mode${mode}-${variant}: perf record (-F ${SAMPLE_FREQ} Hz, DWARF) ... "
        LD_LIBRARY_PATH="$LIB_DIR" \
        taskset -c "$CPU_CORE" \
        "$PERF" record \
            --freq "$SAMPLE_FREQ" \
            --call-graph "dwarf,${DWARF_STACKSIZE}" \
            --no-buildid-cache \
            --output "$data_file" \
            -- "$bin_path" \
            > /dev/null 2>&1
        printf 'done\n'
        log "  → $data_file ($(du -sh "$data_file" | cut -f1))"

        # ── Flat profile ───────────────────────────────────────────────────────
        logn "  mode${mode}-${variant}: perf report (flat) ... "
        {
            echo "=== HAETAE Mode${mode} ${variant^^} — perf report (flat) ==="
            echo "Date:   $(date)"
            echo "Binary: $bin_path"
            echo "Freq:   ${SAMPLE_FREQ} Hz, call-graph dwarf"
            echo ""
            "$PERF" report \
                --input "$data_file" \
                --stdio \
                --no-children \
                --sort symbol,dso \
                --percent-limit 0.1 \
                2>/dev/null
        } > "$flat_file"
        printf 'done\n'
        log "  → $flat_file"

        # ── Call graph ─────────────────────────────────────────────────────────
        logn "  mode${mode}-${variant}: perf report (call graph) ... "
        {
            echo "=== HAETAE Mode${mode} ${variant^^} — perf report (call graph) ==="
            echo "Date:   $(date)"
            echo "Binary: $bin_path"
            echo ""
            "$PERF" report \
                --input "$data_file" \
                --stdio \
                --call-graph "graph,0.5,caller" \
                --percent-limit 0.1 \
                2>/dev/null
        } > "$cg_file"
        printf 'done\n'
        log "  → $cg_file"

        # ── Per-function annotate (top 5 hottest symbols) ──────────────────────
        logn "  mode${mode}-${variant}: perf annotate (source+asm) ... "
        ann_file="$OUT_DIR/mode${mode}_${variant}_annotate.txt"
        {
            echo "=== HAETAE Mode${mode} ${variant^^} — perf annotate ==="
            echo "Date:   $(date)"
            echo "Binary: $bin_path"
            echo ""
            # Extract top symbols (by self%), then annotate each
            top_syms=$(
                "$PERF" report \
                    --input "$data_file" \
                    --stdio \
                    --no-children \
                    --sort symbol \
                    --percent-limit 1.0 \
                    2>/dev/null \
                | grep -oP '^\s+\d+\.\d+%\s+\K\S+' \
                | head -8 \
                || true
            )
            if [ -z "$top_syms" ]; then
                echo "(no symbols above 1% threshold)"
            else
                for sym in $top_syms; do
                    echo ""
                    echo "────────────────────── $sym ──────────────────────"
                    "$PERF" annotate \
                        --input "$data_file" \
                        --stdio \
                        --symbol "$sym" \
                        2>/dev/null || echo "(annotation unavailable for $sym)"
                done
            fi
        } > "$ann_file"
        printf 'done\n'
        log "  → $ann_file"
    done
done

log "Phase 3 complete."
