#!/usr/bin/env bash
# 05_report.sh — generate consolidated performance summary
#
# Reads all profiling_results/ outputs and produces:
#   summary.txt  — human-readable comparison table (cycles, IPC, cache miss rate)
set -euo pipefail
source "$(dirname "$0")/common.sh"

banner "Phase 5: Generating Performance Report"

mkdir -p "$RESULTS_DIR"
REPORT="$RESULTS_DIR/summary.txt"

# ── Helper: extract average cycle count from bench output ─────────────────────
# Format: "function_name:\naverage: NNNNN cycles/ticks\n"
extract_cycles() {
    local file="$1" func="$2"
    # grep the line after the function label
    awk -v fn="$func" '
        $0 ~ fn { found=1; next }
        found && /average:/ {
            match($0, /[0-9]+/)
            print substr($0, RSTART, RLENGTH)
            found=0
        }
    ' "$file" 2>/dev/null | head -1
}

# ── Helper: extract perf stat metric ─────────────────────────────────────────
# Handles: "        12,345,678      cycles"
extract_stat() {
    local file="$1" event="$2"
    grep -E "^\s+[0-9,]+\s+${event}" "$file" 2>/dev/null \
    | tail -1 \
    | awk '{gsub(/,/,""); print $1}' \
    | head -1
}

# ── Helper: extract perf stat ratio ──────────────────────────────────────────
# Handles lines like "  1837747873  instructions  #  2.65  insn per cycle"
# Returns the number after the '#' annotation marker.
extract_ratio() {
    local file="$1" pattern="$2"
    grep -iE "$pattern" "$file" 2>/dev/null \
    | grep -oP '#\s+\K[\d.]+' \
    | head -1
}

# ── Helper: compute speedup ───────────────────────────────────────────────────
speedup() {
    local ref="$1" opt="$2"
    if [[ -n "$ref" && -n "$opt" && "$opt" -gt 0 ]] 2>/dev/null; then
        awk "BEGIN { printf \"%.2fx\", $ref / $opt }"
    else
        echo "N/A"
    fi
}

# ── Helper: miss rate % ───────────────────────────────────────────────────────
miss_rate() {
    local misses="$1" total="$2"
    if [[ -n "$misses" && -n "$total" && "$total" -gt 0 ]] 2>/dev/null; then
        awk "BEGIN { printf \"%.2f%%\", $misses * 100 / $total }"
    else
        echo "N/A"
    fi
}

{
# ══════════════════════════════════════════════════════════════════════════════
echo "╔══════════════════════════════════════════════════════════════════════════╗"
echo "║       HAETAE Jaszz — Performance Profiling Report                    ║"
echo "╚══════════════════════════════════════════════════════════════════════════╝"
echo ""
echo "Generated : $(date)"
echo "Platform  : $(grep -m1 'Model' /proc/device-tree/model 2>/dev/null || grep -m1 'Hardware' /proc/cpuinfo 2>/dev/null | cut -d: -f2 | xargs || uname -m) ($(uname -m))"
echo "Kernel    : $(uname -r)"
echo "CPU core  : ${CPU_CORE} (taskset pinned)"
echo "Governor  : $(cat /sys/devices/system/cpu/cpu${CPU_CORE}/cpufreq/scaling_governor 2>/dev/null)"
echo "Freq(cur) : $(cat /sys/devices/system/cpu/cpu${CPU_CORE}/cpufreq/scaling_cur_freq 2>/dev/null || echo '?') Hz"
echo ""

# ──────────────────────────────────────────────────────────────────────────────
echo "═══════════════════════════════════════════════════════════════════════════"
echo " §1  CYCLE COUNTS  (PMCCNTR_EL0 · 10,000 iter average · taskset -c 3)"
echo "═══════════════════════════════════════════════════════════════════════════"
echo ""

# Column header
printf "%-40s" "Function"
for mode in "${MODES[@]}"; do
    printf "  %-12s %-12s %-8s" "M${mode}-REF" "M${mode}-A64" "Speedup"
done
echo ""
printf "%-40s" "$(printf '─%.0s' {1..40})"
for mode in "${MODES[@]}"; do
    printf "  %-12s %-12s %-8s" "$(printf '─%.0s' {1..12})" "$(printf '─%.0s' {1..12})" "$(printf '─%.0s' {1..8})"
done
echo ""

# Function labels as they appear in benchmark output (grep patterns)
declare -A FUNC_LABELS
# FUNC_LABELS[polymatkm_expand_matA]="ploymatkm_expand_matA:"
# FUNC_LABELS[sample_hyperball]="polyfixveclk_sample_hyperball:"
# FUNC_LABELS[expand_S]="polyvecmk_uniform_eta:"
# FUNC_LABELS[fft_bitrev+fft]="fft_bitrev"
FUNC_LABELS[ntt]="ntt:"
FUNC_LABELS[invntt_tomont]="invntt_tomont:"
FUNC_LABELS[pointwise_montgomery]="polymatkm_pointwise_montgomery:"
# FUNC_LABELS[round_y1_y2]="polyfixvecl_round"
# FUNC_LABELS[poly_fromcrt]="polyveck_poly_fromcrt:"
# FUNC_LABELS[highbits_hint]="polyveck_highbits_hint:"
FUNC_LABELS[crypto_sign_keypair]="crypto_sign_keypair:"
FUNC_LABELS[crypto_sign_signature]="crypto_sign_signature:"
FUNC_LABELS[crypto_sign_verify]="crypto_sign_verify:"

for func_key in \
    ntt invntt_tomont pointwise_montgomery \
    crypto_sign_keypair crypto_sign_signature crypto_sign_verify; do

    pattern="${FUNC_LABELS[$func_key]}"
    printf "%-40s" "$func_key"

    for mode in "${MODES[@]}"; do
        ref_file="$RESULTS_DIR/benchmarks/mode${mode}_ref.txt"
        a64_file="$RESULTS_DIR/benchmarks/mode${mode}_jazz.txt"
        ref_cyc=""
        a64_cyc=""

        [ -f "$ref_file" ] && ref_cyc="$(extract_cycles "$ref_file" "$pattern")"
        [ -f "$a64_file" ] && a64_cyc="$(extract_cycles "$a64_file" "$pattern")"

        sp="$(speedup "$ref_cyc" "$a64_cyc")"
        ref_fmt="${ref_cyc:-N/A}"
        a64_fmt="${a64_cyc:-N/A}"
        printf "  %-12s %-12s %-8s" "$ref_fmt" "$a64_fmt" "$sp"
    done
    echo ""
done

echo ""

# # ──────────────────────────────────────────────────────────────────────────────
# echo "═══════════════════════════════════════════════════════════════════════════"
# echo " §2  PMU EVENTS  (perf stat · 5 repetitions · Cortex-A76)"
# echo "═══════════════════════════════════════════════════════════════════════════"
# echo ""

# printf "%-20s %-8s %-8s %-12s %-12s %-10s %-10s %-12s\n" \
#     "Mode/Variant" "IPC" "Stall-F%" "L1D-miss%" "LLC-miss%" "dTLB-miss%" "Branch-mis%" "Instructions"
# printf '%s\n' "$(printf '─%.0s' {1..100})"

# for mode in "${MODES[@]}"; do
#     for variant in "${VARIANTS[@]}"; do
#         core_f="$RESULTS_DIR/perf_stat/mode${mode}_${variant}_core.txt"
#         cache_f="$RESULTS_DIR/perf_stat/mode${mode}_${variant}_cache.txt"
#         tlb_f="$RESULTS_DIR/perf_stat/mode${mode}_${variant}_tlb.txt"
#         branch_f="$RESULTS_DIR/perf_stat/mode${mode}_${variant}_branch.txt"

#         ipc="N/A"; stall_f="N/A"
#         l1d_miss="N/A"; llc_miss="N/A"
#         dtlb_miss="N/A"; br_miss="N/A"
#         total_insn="N/A"

#         if [ -f "$core_f" ]; then
#             ipc="$(extract_ratio "$core_f" 'insn per cycle' || echo N/A)"
#             cyc="$(extract_stat "$core_f" 'cycles')"
#             sfe="$(extract_stat "$core_f" 'stalled-cycles-frontend')"
#             insn="$(extract_stat "$core_f" 'instructions')"
#             # Format instruction count with K/M suffix for readability
#             if [[ -n "$insn" ]] 2>/dev/null; then
#                 total_insn="$(awk "BEGIN{printf \"%.1fM\", $insn/1000000}")"
#             else
#                 total_insn="N/A"
#             fi
#             [ -n "$sfe" ] && [ -n "$cyc" ] && [ "$cyc" -gt 0 ] 2>/dev/null && \
#                 stall_f="$(awk "BEGIN{printf \"%.1f%%\", $sfe*100/$cyc}")"
#         fi

#         if [ -f "$cache_f" ]; then
#             l1d_loads="$(extract_stat "$cache_f" 'L1-dcache-loads')"
#             l1d_misses="$(extract_stat "$cache_f" 'L1-dcache-load-misses')"
#             llc_loads="$(extract_stat "$cache_f" 'LLC-loads')"
#             llc_misses="$(extract_stat "$cache_f" 'LLC-load-misses')"
#             l1d_miss="$(miss_rate "$l1d_misses" "$l1d_loads")"
#             llc_miss="$(miss_rate "$llc_misses" "$llc_loads")"
#         fi

#         if [ -f "$tlb_f" ]; then
#             dtlb_loads="$(extract_stat "$tlb_f" 'dTLB-loads')"
#             dtlb_misses="$(extract_stat "$tlb_f" 'dTLB-load-misses')"
#             dtlb_miss="$(miss_rate "$dtlb_misses" "$dtlb_loads")"
#         fi

#         if [ -f "$branch_f" ]; then
#             br_total="$(extract_stat "$branch_f" 'branch-instructions')"
#             br_misses_cnt="$(extract_stat "$branch_f" 'branch-misses')"
#             br_miss="$(miss_rate "$br_misses_cnt" "$br_total")"
#         fi

#         printf "%-20s %-8s %-8s %-12s %-12s %-10s %-10s %-12s\n" \
#             "mode${mode}-${variant}" \
#             "$ipc" "$stall_f" \
#             "$l1d_miss" "$llc_miss" \
#             "$dtlb_miss" "$br_miss" \
#             "$total_insn"
#     done
# done

# echo ""

# ──────────────────────────────────────────────────────────────────────────────
echo "═══════════════════════════════════════════════════════════════════════════"
echo " §3  TOP HOTSPOTS  (perf record · self % · per mode)"
echo "═══════════════════════════════════════════════════════════════════════════"
echo ""

for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        flat_f="$RESULTS_DIR/perf_record/mode${mode}_${variant}_flat.txt"
        [ -f "$flat_f" ] || continue

        echo "── Mode${mode}-${variant^^} ──────────────────────────"
        # Format: "  24.77%  [.] SymbolName  SharedObj"
        grep -E '^\s+[0-9]+\.[0-9]+%\s+\[.\]' "$flat_f" \
        | head -10 \
        | awk '{printf "  %-10s %s\n", $1, $3}' \
        || echo "  (no data)"
        echo ""
    done
done

# ──────────────────────────────────────────────────────────────────────────────
echo "═══════════════════════════════════════════════════════════════════════════"
echo " §4  INSTRUCTION COUNTS  (callgrind · keypair+sign+verify · 1 iter)"
echo "═══════════════════════════════════════════════════════════════════════════"
echo ""

printf "%-20s %-18s %-18s %-18s %-18s\n" \
    "Mode/Variant" "Total-Ir" "D1-miss-rate" "LL-miss-rate" "Branch-mis%"
printf '%s\n' "$(printf '─%.0s' {1..90})"

for mode in "${MODES[@]}"; do
    for variant in "${VARIANTS[@]}"; do
        ann_f="$RESULTS_DIR/callgrind/mode${mode}_${variant}_annotate.txt"
        [ -f "$ann_f" ] || { printf "%-20s  (no data)\n" "mode${mode}-${variant}"; continue; }

        # PROGRAM TOTALS line: Ir Dr Dw I1mr D1mr D1mw ILmr DLmr DLmw Bc Bcm Bi Bim ...
        # Each field is immediately followed by (xx.x%), extract bare numbers in order.
        totals_line="$(grep "PROGRAM TOTALS" "$ann_f" 2>/dev/null || true)"
        mapfile -t _f < <(echo "$totals_line" | grep -oP '[\d,]+(?=\s+\()' | tr -d ',')
        _ir="${_f[0]:-}" _dr="${_f[1]:-}" _dw="${_f[2]:-}"
        _d1mr="${_f[4]:-}" _d1mw="${_f[5]:-}"
        _dlmr="${_f[7]:-}" _dlmw="${_f[8]:-}"
        _bc="${_f[9]:-}"  _bcm="${_f[10]:-}" _bi="${_f[11]:-}" _bim="${_f[12]:-}"

        total_ir="${_ir:-N/A}"
        d1mr="N/A"; llmr="N/A"; bcm_r="N/A"
        [[ -n "$_dr" && -n "$_dw" ]] && {
            _reads_writes=$((_dr + _dw))
            [[ $_reads_writes -gt 0 ]] && d1mr="$(awk "BEGIN{printf \"%.2f%%\", ($_d1mr+$_d1mw)*100/$_reads_writes}")"
            [[ $_reads_writes -gt 0 ]] && llmr="$(awk "BEGIN{printf \"%.2f%%\", ($_dlmr+$_dlmw)*100/$_reads_writes}")"
        } 2>/dev/null
        [[ -n "$_bc" && -n "$_bi" ]] && {
            _branches=$((_bc + _bi))
            [[ $_branches -gt 0 ]] && bcm_r="$(awk "BEGIN{printf \"%.2f%%\", ($_bcm+$_bim)*100/$_branches}")"
        } 2>/dev/null

        printf "%-20s %-18s %-18s %-18s %-18s\n" \
            "mode${mode}-${variant}" "$total_ir" "$d1mr" "$llmr" "$bcm_r"
    done
done

echo ""

# ──────────────────────────────────────────────────────────────────────────────
echo "═══════════════════════════════════════════════════════════════════════════"
echo " §5  FILES GENERATED"
echo "═══════════════════════════════════════════════════════════════════════════"
echo ""
find "$RESULTS_DIR" -type f | sort | while read -r f; do
    printf "  %-70s %s\n" "${f#"$PROJECT_ROOT/"}" "$(du -sh "$f" 2>/dev/null | cut -f1)"
done

echo ""
echo "═══════════════════════════════════════════════════════════════════════════"
echo " Report generated: $(date)"
echo "═══════════════════════════════════════════════════════════════════════════"

} | tee "$REPORT"

log "Report saved → $REPORT"
