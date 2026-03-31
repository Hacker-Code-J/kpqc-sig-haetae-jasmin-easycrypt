#!/usr/bin/env bash
# =============================================================================
# Professional Profiling Script — HAETAE Reference Implementation
# =============================================================================
# Tools:  native cpucycles | perf stat | perf record/report | valgrind callgrind
# Target: AMD Ryzen 7 5800X3D, Linux 5.15, perf_event_paranoid=-1
# =============================================================================
set -euo pipefail

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TIMESTAMP="$(date +%Y%m%d_%H%M%S)"
RESULTS_DIR="${SCRIPT_DIR}/profiling_results/${TIMESTAMP}"
BUILD_DIR="${SCRIPT_DIR}/build"
BIN_DIR="${BUILD_DIR}/bin"
LIB_DIR="${BUILD_DIR}/lib"

MODES=(2 3 5)
NTESTS_BENCH=1000   # native benchmark iterations (already in speed.c)
TASKSET_CPU=2       # pin to a single core for stable measurements

# perf stat event groups — split to avoid multiplexing on most PMUs
PERF_EVENTS_CORE="cycles,instructions,branch-instructions,branch-misses"
PERF_EVENTS_CACHE="L1-dcache-loads,L1-dcache-load-misses,LLC-loads,LLC-load-misses"
PERF_EVENTS_TLB="dTLB-loads,dTLB-load-misses,iTLB-loads,iTLB-load-misses"

# Colors
RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'
CYAN='\033[0;36m'; BOLD='\033[1m'; RESET='\033[0m'

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
banner() { echo -e "\n${BOLD}${CYAN}══════════════════════════════════════════════════════${RESET}"; \
           echo -e "${BOLD}${CYAN}  $*${RESET}"; \
           echo -e "${BOLD}${CYAN}══════════════════════════════════════════════════════${RESET}\n"; }
info()   { echo -e "${GREEN}[INFO]${RESET} $*"; }
warn()   { echo -e "${YELLOW}[WARN]${RESET} $*"; }
die()    { echo -e "${RED}[FAIL]${RESET} $*" >&2; exit 1; }
step()   { echo -e "\n${BOLD}▶ $*${RESET}"; }

# ---------------------------------------------------------------------------
# Phase 0 — Preflight
# ---------------------------------------------------------------------------
banner "Phase 0 — Preflight"

for tool in perf valgrind gcc make taskset; do
    if command -v "$tool" &>/dev/null; then
        info "$(command -v "$tool") — $(${tool} --version 2>&1 | head -1)"
    else
        warn "$tool not found — some phases will be skipped"
    fi
done

# Check perf permissions
PARANOID="$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo 3)"
info "perf_event_paranoid = ${PARANOID}"
[[ "$PARANOID" -le 0 ]] || warn "perf_event_paranoid > 0; hardware counters may be limited"

# CPU info snapshot
CPU_MODEL="$(lscpu | grep 'Model name' | sed 's/.*: *//')"
CPU_COUNT="$(nproc)"
info "CPU: ${CPU_MODEL} (${CPU_COUNT} logical cores)"
info "Pinning benchmarks to core ${TASKSET_CPU} for stable measurements"

mkdir -p "${RESULTS_DIR}"/{benchmarks,perf_stat,perf_record,callgrind}
info "Results directory: ${RESULTS_DIR}"

# ---------------------------------------------------------------------------
# Phase 1 — Build with debug symbols
# ---------------------------------------------------------------------------
banner "Phase 1 — Build  (CFLAGS='-O2 -g')"

cd "${SCRIPT_DIR}"
step "Clean previous build"
make clean 2>/dev/null || true

step "Compiling all modes with -O2 -g (keeps full debug info for perf/valgrind)"
make -j"${CPU_COUNT}" CFLAGS="-O2 -g" 2>&1 | tee "${RESULTS_DIR}/build.log"
info "Build complete"

# Verify binaries
for mode in "${MODES[@]}"; do
    [[ -x "${BIN_DIR}/haetae-mode${mode}-benchmark" ]] || die "haetae-mode${mode}-benchmark not found"
    [[ -x "${BIN_DIR}/haetae-mode${mode}-main"      ]] || die "haetae-mode${mode}-main not found"
done
info "All binaries verified"

# Capture binary sizes
{
    echo "# Binary sizes"
    echo '```'
    ls -lh "${BIN_DIR}"/ "${LIB_DIR}"/
    echo '```'
} > "${RESULTS_DIR}/binary_sizes.txt"
cat "${RESULTS_DIR}/binary_sizes.txt"

# ---------------------------------------------------------------------------
# Phase 2 — Native CPU-cycle benchmarks (all modes)
# ---------------------------------------------------------------------------
banner "Phase 2 — Native Cycle-Count Benchmarks"

for mode in "${MODES[@]}"; do
    step "HAETAE Mode ${mode} — ${NTESTS_BENCH} iterations per operation"
    OUT="${RESULTS_DIR}/benchmarks/mode${mode}_benchmark.txt"
    {
        echo "=============================="
        echo " HAETAE Mode ${mode} — Native Benchmark"
        echo " Date: $(date)"
        echo " CPU:  ${CPU_MODEL}"
        echo "=============================="
        echo ""
        taskset -c "${TASKSET_CPU}" \
            env "LD_LIBRARY_PATH=${LIB_DIR}" \
            "${BIN_DIR}/haetae-mode${mode}-benchmark"
    } | tee "${OUT}"
    info "  → Saved to ${OUT}"
done

# ---------------------------------------------------------------------------
# Phase 3 — perf stat (hardware performance counters)
# ---------------------------------------------------------------------------
banner "Phase 3 — perf stat  (hardware counters)"

for mode in "${MODES[@]}"; do
    step "Mode ${mode}: core events (cycles / instructions / branches)"
    OUT_CORE="${RESULTS_DIR}/perf_stat/mode${mode}_core.txt"
    taskset -c "${TASKSET_CPU}" \
        perf stat \
            --repeat=5 \
            -e "${PERF_EVENTS_CORE}" \
            -- env "LD_LIBRARY_PATH=${LIB_DIR}" \
               "${BIN_DIR}/haetae-mode${mode}-benchmark" \
        2>&1 | tee "${OUT_CORE}"

    step "Mode ${mode}: L1/LLC cache events"
    OUT_CACHE="${RESULTS_DIR}/perf_stat/mode${mode}_cache.txt"
    taskset -c "${TASKSET_CPU}" \
        perf stat \
            --repeat=5 \
            -e "${PERF_EVENTS_CACHE}" \
            -- env "LD_LIBRARY_PATH=${LIB_DIR}" \
               "${BIN_DIR}/haetae-mode${mode}-benchmark" \
        2>&1 | tee "${OUT_CACHE}"

    step "Mode ${mode}: TLB events"
    OUT_TLB="${RESULTS_DIR}/perf_stat/mode${mode}_tlb.txt"
    taskset -c "${TASKSET_CPU}" \
        perf stat \
            --repeat=5 \
            -e "${PERF_EVENTS_TLB}" \
            -- env "LD_LIBRARY_PATH=${LIB_DIR}" \
               "${BIN_DIR}/haetae-mode${mode}-benchmark" \
        2>&1 | tee "${OUT_TLB}"

    info "  → perf stat saved to ${RESULTS_DIR}/perf_stat/mode${mode}_*.txt"
done

# ---------------------------------------------------------------------------
# Phase 4 — perf record + report (call graph, mode2 as representative)
# ---------------------------------------------------------------------------
banner "Phase 4 — perf record  (DWARF call graph)"

PERF_DATA_DIR="${RESULTS_DIR}/perf_record"
mkdir -p "${PERF_DATA_DIR}"

for mode in "${MODES[@]}"; do
    step "Mode ${mode}: recording with --call-graph dwarf"
    PERF_DATA="${PERF_DATA_DIR}/mode${mode}.perf.data"

    taskset -c "${TASKSET_CPU}" \
        perf record \
            --call-graph dwarf \
            --freq=9999 \
            --output="${PERF_DATA}" \
            -- env "LD_LIBRARY_PATH=${LIB_DIR}" \
               "${BIN_DIR}/haetae-mode${mode}-benchmark" \
        2>&1 | tee "${PERF_DATA_DIR}/mode${mode}_record.log"

    step "Mode ${mode}: generating flat profile report"
    perf report \
        --input="${PERF_DATA}" \
        --stdio \
        --percent-limit=0.1 \
        --sort=dso,symbol \
        2>/dev/null \
        > "${PERF_DATA_DIR}/mode${mode}_report_flat.txt" || true

    step "Mode ${mode}: generating call-graph report (top 20 symbols)"
    perf report \
        --input="${PERF_DATA}" \
        --stdio \
        --call-graph=graph,0.5,caller \
        --percent-limit=0.5 \
        2>/dev/null \
        > "${PERF_DATA_DIR}/mode${mode}_report_callgraph.txt" || true

    step "Mode ${mode}: generating annotated output"
    perf annotate \
        --input="${PERF_DATA}" \
        --stdio \
        2>/dev/null \
        > "${PERF_DATA_DIR}/mode${mode}_annotate.txt" || true

    info "  → Reports saved to ${PERF_DATA_DIR}/mode${mode}_report_*.txt"
done

# ---------------------------------------------------------------------------
# Phase 5 — valgrind callgrind (mode2; uses -main for manageable runtime)
# ---------------------------------------------------------------------------
banner "Phase 5 — valgrind --tool=callgrind"

CALLGRIND_DIR="${RESULTS_DIR}/callgrind"

for mode in "${MODES[@]}"; do
    step "Mode ${mode}: running under callgrind (this takes ~1–3 min per mode)"
    CG_OUT="${CALLGRIND_DIR}/callgrind.out.mode${mode}"

    valgrind \
        --tool=callgrind \
        --callgrind-out-file="${CG_OUT}" \
        --cache-sim=yes \
        --branch-sim=yes \
        --collect-jumps=yes \
        --dump-instr=yes \
        --collect-systime=yes \
        --separate-threads=yes \
        env "LD_LIBRARY_PATH=${LIB_DIR}" \
        "${BIN_DIR}/haetae-mode${mode}-main" \
        2>&1 | tee "${CALLGRIND_DIR}/mode${mode}_valgrind.log"

    step "Mode ${mode}: callgrind_annotate summary"
    callgrind_annotate \
        --auto=yes \
        --threshold=99 \
        "${CG_OUT}" \
        > "${CALLGRIND_DIR}/mode${mode}_annotate.txt" 2>/dev/null || true

    info "  → callgrind output: ${CG_OUT}"
    info "  → annotated report: ${CALLGRIND_DIR}/mode${mode}_annotate.txt"
    info "  → Open in kcachegrind: kcachegrind ${CG_OUT}"
done

# ---------------------------------------------------------------------------
# Phase 6 — Extract key numbers & generate Markdown report
# ---------------------------------------------------------------------------
banner "Phase 6 — Generating Report"

REPORT="${RESULTS_DIR}/PROFILING_REPORT.md"

{
cat <<HEADER
# HAETAE Reference Implementation — Profiling Report

**Date**: $(date '+%Y-%m-%d %H:%M:%S')
**Host**: $(hostname)
**CPU**: ${CPU_MODEL}
**Logical cores**: ${CPU_COUNT}
**Kernel**: $(uname -r)
**perf version**: $(perf --version 2>/dev/null || echo n/a)
**valgrind version**: $(valgrind --version 2>/dev/null || echo n/a)
**Compiler**: $(gcc --version 2>/dev/null | head -1)
**Build flags**: \`-O2 -g\`
**Core pinned to**: CPU ${TASKSET_CPU} (taskset)
**perf_event_paranoid**: ${PARANOID}

---

## 1. Binary Sizes

$(cat "${RESULTS_DIR}/binary_sizes.txt")

---

## 2. Native Cycle-Count Benchmarks

> 1 000 iterations per operation, \`cpucycles()\` (RDTSC), core pinned.

HEADER

for mode in "${MODES[@]}"; do
    echo "### Mode ${mode}"
    echo '```'
    cat "${RESULTS_DIR}/benchmarks/mode${mode}_benchmark.txt" 2>/dev/null || echo "(no output)"
    echo '```'
    echo ""
done

cat <<'SEC3'
---

## 3. Hardware Performance Counters (perf stat, 5 repetitions)

### 3.1 Core Events (Cycles / Instructions / IPC / Branches)

SEC3

for mode in "${MODES[@]}"; do
    echo "#### Mode ${mode}"
    echo '```'
    # Extract the perf stat summary block (after the program output)
    grep -A 60 "Performance counter stats" "${RESULTS_DIR}/perf_stat/mode${mode}_core.txt" 2>/dev/null \
        | head -40 || echo "(no perf stat output)"
    echo '```'
    echo ""
done

cat <<'SEC3B'
### 3.2 Cache Events (L1-dcache / LLC)

SEC3B

for mode in "${MODES[@]}"; do
    echo "#### Mode ${mode}"
    echo '```'
    grep -A 60 "Performance counter stats" "${RESULTS_DIR}/perf_stat/mode${mode}_cache.txt" 2>/dev/null \
        | head -40 || echo "(no perf stat output)"
    echo '```'
    echo ""
done

cat <<'SEC3C'
### 3.3 TLB Events

SEC3C

for mode in "${MODES[@]}"; do
    echo "#### Mode ${mode}"
    echo '```'
    grep -A 60 "Performance counter stats" "${RESULTS_DIR}/perf_stat/mode${mode}_tlb.txt" 2>/dev/null \
        | head -40 || echo "(no perf stat output)"
    echo '```'
    echo ""
done

cat <<'SEC4'
---

## 4. perf Hotspot Analysis (perf record --call-graph dwarf)

### 4.1 Flat Profile (top symbols by % self time)

SEC4

for mode in "${MODES[@]}"; do
    echo "#### Mode ${mode}"
    echo '```'
    head -80 "${RESULTS_DIR}/perf_record/mode${mode}_report_flat.txt" 2>/dev/null \
        || echo "(no perf report output)"
    echo '```'
    echo ""
done

cat <<'SEC4B'
### 4.2 Call Graph (≥0.5% overhead, caller view)

SEC4B

for mode in "${MODES[@]}"; do
    echo "#### Mode ${mode}"
    echo '```'
    head -120 "${RESULTS_DIR}/perf_record/mode${mode}_report_callgraph.txt" 2>/dev/null \
        || echo "(no perf report output)"
    echo '```'
    echo ""
done

cat <<'SEC5'
---

## 5. Valgrind Callgrind — Instruction-Level Analysis

> Run on \`haetae-mode*-main\` (100 sign/verify iterations).
> Cache sim and branch sim enabled.

SEC5

for mode in "${MODES[@]}"; do
    echo "#### Mode ${mode}"
    echo '```'
    head -100 "${RESULTS_DIR}/callgrind/mode${mode}_annotate.txt" 2>/dev/null \
        || echo "(no callgrind output)"
    echo '```'
    echo ""
    echo "> Full interactive analysis: \`kcachegrind ${RESULTS_DIR}/callgrind/callgrind.out.mode${mode}\`"
    echo ""
done

cat <<'FOOTER'
---

## 6. Raw Artifacts

| File | Description |
|------|-------------|
| `benchmarks/mode*_benchmark.txt` | Native cpucycles output |
| `perf_stat/mode*_core.txt` | perf stat — cycles/instructions/branches |
| `perf_stat/mode*_cache.txt` | perf stat — L1/LLC cache events |
| `perf_stat/mode*_tlb.txt` | perf stat — TLB events |
| `perf_record/mode*.perf.data` | Raw perf sampling data |
| `perf_record/mode*_report_flat.txt` | perf flat profile text |
| `perf_record/mode*_report_callgraph.txt` | perf call-graph text |
| `perf_record/mode*_annotate.txt` | perf annotated assembly |
| `callgrind/callgrind.out.mode*` | Callgrind data (open with kcachegrind) |
| `callgrind/mode*_annotate.txt` | callgrind_annotate text report |

## 7. Recommended Interactive Analysis

```bash
# Interactive perf TUI (all modes)
perf report --input=perf_record/mode2.perf.data

# Instruction-level heatmap (GUI)
kcachegrind callgrind/callgrind.out.mode2
kcachegrind callgrind/callgrind.out.mode3
kcachegrind callgrind/callgrind.out.mode5
```

---
*Generated by profile.sh — HAETAE Reference Profiling*
FOOTER

} > "${REPORT}"

info "Report written to: ${REPORT}"

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
banner "Profiling Complete"

echo -e "${BOLD}Results directory:${RESET} ${RESULTS_DIR}"
echo ""
echo -e "${BOLD}Quick view commands:${RESET}"
echo "  cat  ${RESULTS_DIR}/PROFILING_REPORT.md | less"
echo "  perf report --input=${RESULTS_DIR}/perf_record/mode2.perf.data"
echo "  kcachegrind ${RESULTS_DIR}/callgrind/callgrind.out.mode2"
echo ""
echo -e "${GREEN}Done.${RESET}"
