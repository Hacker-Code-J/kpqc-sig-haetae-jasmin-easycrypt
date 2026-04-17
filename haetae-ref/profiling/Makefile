## profiling/Makefile — HAETAE AArch64 profiling orchestration
##
## Usage:
##   make              → run full pipeline (all 5 phases)
##   make setup        → phase 0: validate environment
##   make bench        → phase 1: PMCCNTR_EL0 cycle benchmarks
##   make perf-stat    → phase 2: perf stat PMU event groups
##   make perf-record  → phase 3: perf record + annotate + call graph
##   make callgrind    → phase 4: valgrind callgrind (slow, ~5-30 min)
##   make report       → phase 5: consolidated summary (reads existing results)
##   make clean        → remove all profiling_results/
##
## Individual phases can be run standalone; report reads whatever is present.
## Run with sudo if perf_event_paranoid > 0 (check: cat /proc/sys/kernel/perf_event_paranoid).

.NOTPARALLEL:
.PHONY: all setup bench perf-stat perf-record callgrind report clean

PROFILING_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
RESULTS_DIR   := $(PROFILING_DIR)../profiling_results

all: setup bench perf-stat perf-record callgrind report
	@echo ""
	@echo "All profiling phases complete. See $(RESULTS_DIR)/summary.txt"

setup:
	@bash $(PROFILING_DIR)00_setup.sh

bench:
	@bash $(PROFILING_DIR)01_bench.sh

perf-stat:
	@bash $(PROFILING_DIR)02_perf_stat.sh

perf-record:
	@bash $(PROFILING_DIR)03_perf_record.sh

callgrind:
	@bash $(PROFILING_DIR)04_callgrind.sh

report:
	@bash $(PROFILING_DIR)05_report.sh

clean:
	rm -rf $(RESULTS_DIR)
	@echo "Removed $(RESULTS_DIR)"
