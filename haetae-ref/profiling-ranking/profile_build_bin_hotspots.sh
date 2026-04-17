#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
BIN_DIR="${ROOT_DIR}/build/bin"
LIB_DIR="${ROOT_DIR}/build/lib"
RESULTS_ROOT="${SCRIPT_DIR}/results"

PERF_BIN="${PERF_BIN:-$(command -v perf || true)}"
PERF_FREQ="${PERF_FREQ:-999}"
STAT_REPS="${STAT_REPS:-3}"
TOP_N="${TOP_N:-12}"
PERCENT_LIMIT="${PERCENT_LIMIT:-0.5}"
CPU_CORE="${CPU_CORE:-}"

MODES=(2 3 5)
VARIANTS=(ref jazz)

SELECTED_MODES=()
SELECTED_VARIANTS=()

log() {
  printf '[%s] %s\n' "$(date '+%H:%M:%S')" "$*"
}

die() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage: profiling/profile_build_bin_hotspots.sh [options]

Profiles HAETAE binaries in build/bin and reports where the load lands inside
keygen, sign, and verify for both ref and jazz builds.

Options:
  --mode <2|3|5>         Profile only one mode. Repeatable.
  --variant <ref|jazz>
                         Profile only one implementation. Repeatable.
  --freq <hz>            perf sampling frequency. Default: 999
  --stat-reps <count>    perf stat repetitions. Default: 3
  --top <count>          Top hotspot rows per section. Default: 12
  --cpu <core>           Pin runs to one CPU core with taskset.
  --perf <path>          Override perf binary path.
  -h, --help             Show this help text.

Environment:
  PERF_BIN               Same as --perf
  PERF_FREQ              Same as --freq
  STAT_REPS              Same as --stat-reps
  TOP_N                  Same as --top
  CPU_CORE               Same as --cpu
EOF
}

main_bin() {
  local mode="$1"
  local variant="$2"

  case "$variant" in
    ref) printf 'haetae-mode%s-main\n' "$mode" ;;
    jazz) printf 'haetae-mode%s-main-jazz\n' "$mode" ;;
    *) die "unknown variant: $variant" ;;
  esac
}

lib_name() {
  local mode="$1"
  local variant="$2"

  case "$variant" in
    ref) printf 'libhaetae-mode%s.so\n' "$mode" ;;
    jazz) printf 'libhaetae-mode%s-jazz.so\n' "$mode" ;;
    *) die "unknown variant: $variant" ;;
  esac
}

check_variant() {
  case "$1" in
    ref|jazz) ;;
    *) die "unsupported variant: $1" ;;
  esac
}

check_mode() {
  case "$1" in
    2|3|5) ;;
    *) die "unsupported mode: $1" ;;
  esac
}

parse_args() {
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --mode)
        [[ $# -ge 2 ]] || die "--mode needs a value"
        check_mode "$2"
        SELECTED_MODES+=("$2")
        shift 2
        ;;
      --variant)
        [[ $# -ge 2 ]] || die "--variant needs a value"
        check_variant "$2"
        SELECTED_VARIANTS+=("$2")
        shift 2
        ;;
      --freq)
        [[ $# -ge 2 ]] || die "--freq needs a value"
        PERF_FREQ="$2"
        shift 2
        ;;
      --stat-reps)
        [[ $# -ge 2 ]] || die "--stat-reps needs a value"
        STAT_REPS="$2"
        shift 2
        ;;
      --top)
        [[ $# -ge 2 ]] || die "--top needs a value"
        TOP_N="$2"
        shift 2
        ;;
      --cpu)
        [[ $# -ge 2 ]] || die "--cpu needs a value"
        CPU_CORE="$2"
        shift 2
        ;;
      --perf)
        [[ $# -ge 2 ]] || die "--perf needs a value"
        PERF_BIN="$2"
        shift 2
        ;;
      -h|--help)
        usage
        exit 0
        ;;
      *)
        die "unknown argument: $1"
        ;;
    esac
  done

  if [[ ${#SELECTED_MODES[@]} -eq 0 ]]; then
    SELECTED_MODES=("${MODES[@]}")
  fi
  if [[ ${#SELECTED_VARIANTS[@]} -eq 0 ]]; then
    SELECTED_VARIANTS=("${VARIANTS[@]}")
  fi
}

emit_hotspot_summary() {
  local tsv_file="$1"
  local out_file="$2"
  local mode="$3"
  local variant="$4"

  {
    printf 'HAETAE mode%s %s operation hotspots\n' "$mode" "$variant"
    printf 'Generated: %s\n' "$(date)"
    printf '\n'

    local op
    for op in keygen sign verify; do
      local total
      total="$(awk -F '\t' -v op="$op" '$1 == "TOTAL" && $2 == op { print $3 }' "$tsv_file")"

      printf '=== %s ===\n' "$op"

      if [[ -z "${total}" || "${total}" == "0" ]]; then
        printf 'No user-space samples attributed to %s.\n\n' "$op"
        continue
      fi

      printf 'Weighted sample total: %s\n' "$total"
      printf 'Top self hotspots:\n'
      awk -F '\t' -v op="$op" '$1 == "SELF" && $2 == op { print $4 "\t" $3 }' "$tsv_file" \
        | sort -nr \
        | head -n "$TOP_N" \
        | awk -F '\t' -v total="$total" '{ printf "  %6.2f%%  %s\n", ($1 * 100.0) / total, $2 }'

      printf 'Top inclusive stack symbols:\n'
      awk -F '\t' -v op="$op" '$1 == "INCL" && $2 == op { print $4 "\t" $3 }' "$tsv_file" \
        | sort -nr \
        | head -n "$TOP_N" \
        | awk -F '\t' -v total="$total" '{ printf "  %6.2f%%  %s\n", ($1 * 100.0) / total, $2 }'
      printf '\n'
    done
  } >"$out_file"
}

classify_perf_samples() {
  local perf_data="$1"
  local out_file="$2"

  "${PERF_BIN}" script -i "$perf_data" | awk '
    function trim_offset(sym) {
      sub(/\+.*/, "", sym)
      return sym
    }

    function operation_from_stack(    i) {
      op = ""
      for (i = 1; i <= depth; ++i) {
        if (symbols[i] ~ /_(keypair|keypair_internal)$/) {
          op = "keygen"
        } else if (symbols[i] ~ /_(signature|signature_internal)$/) {
          op = "sign"
        } else if (symbols[i] ~ /_(verify|verify_internal)$/) {
          op = "verify"
        }
      }
      return op
    }

    function flush_sample(    op, i, leaf, key) {
      if (depth == 0 || weight == 0) {
        weight = 0
        depth = 0
        return
      }

      op = operation_from_stack()
      if (op == "") {
        weight = 0
        depth = 0
        return
      }

      total[op] += weight
      leaf = ""

      delete seen
      for (i = 1; i <= depth; ++i) {
        if (dsos[i] == "([kernel.kallsyms])" || dsos[i] == "([unknown])") {
          continue
        }

        if (leaf == "") {
          leaf = symbols[i]
        }

        if (!(symbols[i] in seen)) {
          seen[symbols[i]] = 1
          key = op SUBSEP symbols[i]
          incl[key] += weight
        }
      }

      if (leaf != "") {
        key = op SUBSEP leaf
        self[key] += weight
      }

      weight = 0
      depth = 0
    }

    /^[^ \t]/ && $NF ~ /:$/ && $(NF - 1) ~ /^[0-9,]+$/ {
      flush_sample()
      value = $(NF - 1)
      gsub(/,/, "", value)
      weight = value + 0
      next
    }

    /^[[:space:]]+[0-9a-f]+/ {
      depth++
      symbols[depth] = trim_offset($2)
      dsos[depth] = $3
      next
    }

    /^$/ {
      flush_sample()
      next
    }

    END {
      flush_sample()
      for (op in total) {
        printf "TOTAL\t%s\t%.0f\n", op, total[op]
      }
      for (key in self) {
        split(key, parts, SUBSEP)
        printf "SELF\t%s\t%s\t%.0f\n", parts[1], parts[2], self[key]
      }
      for (key in incl) {
        split(key, parts, SUBSEP)
        printf "INCL\t%s\t%s\t%.0f\n", parts[1], parts[2], incl[key]
      }
    }
  ' >"$out_file"
}

profile_one() {
  local mode="$1"
  local variant="$2"

  local bin_name lib_file bin_path lib_path run_tag out_dir
  bin_name="$(main_bin "$mode" "$variant")"
  lib_file="$(lib_name "$mode" "$variant")"
  bin_path="${BIN_DIR}/${bin_name}"
  lib_path="${LIB_DIR}/${lib_file}"

  [[ -x "$bin_path" ]] || die "missing binary: $bin_path"
  [[ -f "$lib_path" ]] || die "missing library: $lib_path"

  run_tag="mode${mode}_${variant}"
  out_dir="${RUN_DIR}/${run_tag}"
  mkdir -p "$out_dir"

  local -a target_cmd
  target_cmd=(env "LD_LIBRARY_PATH=${LIB_DIR}")
  if [[ -n "${CPU_CORE}" ]]; then
    target_cmd+=(taskset -c "$CPU_CORE")
  fi
  target_cmd+=("$bin_path")

  log "Profiling ${bin_name}"

  "${PERF_BIN}" stat \
    -r "$STAT_REPS" \
    -d \
    -e cycles,instructions,branches,branch-misses,cache-references,cache-misses \
    --output "${out_dir}/perf_stat.txt" \
    -- "${target_cmd[@]}" \
    >"${out_dir}/perf_stat.stdout.txt" \
    2>"${out_dir}/perf_stat.stderr.txt"

  "${PERF_BIN}" record \
    --freq "$PERF_FREQ" \
    --call-graph dwarf \
    --all-user \
    --output "${out_dir}/perf.data" \
    -- "${target_cmd[@]}" \
    >"${out_dir}/perf_record.stdout.txt" \
    2>"${out_dir}/perf_record.stderr.txt"

  "${PERF_BIN}" report \
    --input "${out_dir}/perf.data" \
    --stdio \
    --no-children \
    --sort symbol,dso \
    --percent-limit "$PERCENT_LIMIT" \
    >"${out_dir}/perf_report_flat.txt"

  "${PERF_BIN}" report \
    --input "${out_dir}/perf.data" \
    --stdio \
    --call-graph graph,0.5,caller \
    --percent-limit "$PERCENT_LIMIT" \
    >"${out_dir}/perf_report_callgraph.txt"

  classify_perf_samples "${out_dir}/perf.data" "${out_dir}/hotspots.tsv"
  emit_hotspot_summary "${out_dir}/hotspots.tsv" "${out_dir}/operation_hotspots.txt" "$mode" "$variant"
}

write_run_summary() {
  local summary_file="${RUN_DIR}/summary.txt"

  {
    printf 'HAETAE build/bin profiling run\n'
    printf 'Generated: %s\n' "$(date)"
    printf 'Results: %s\n' "$RUN_DIR"
    printf 'perf: %s\n' "$PERF_BIN"
    printf 'Frequency: %s Hz\n' "$PERF_FREQ"
    printf 'Stat repetitions: %s\n' "$STAT_REPS"
    if [[ -n "${CPU_CORE}" ]]; then
      printf 'Pinned CPU: %s\n' "$CPU_CORE"
    fi
    printf '\n'

    local mode variant file
    for mode in "${SELECTED_MODES[@]}"; do
      for variant in "${SELECTED_VARIANTS[@]}"; do
        file="${RUN_DIR}/mode${mode}_${variant}/operation_hotspots.txt"
        [[ -f "$file" ]] || continue
        printf '===== mode%s %s =====\n' "$mode" "$variant"
        cat "$file"
        printf '\n'
      done
    done
  } >"$summary_file"

  log "Summary written to ${summary_file}"
}

main() {
  parse_args "$@"

  [[ -n "${PERF_BIN}" ]] || die "perf not found"
  [[ -d "$BIN_DIR" ]] || die "missing directory: $BIN_DIR"
  [[ -d "$LIB_DIR" ]] || die "missing directory: $LIB_DIR"
  if [[ -n "${CPU_CORE}" ]] && ! command -v taskset >/dev/null 2>&1; then
    die "CPU pinning requested but taskset is not available"
  fi

  local run_id
  run_id="$(date '+%Y%m%d-%H%M%S')"
  RUN_DIR="${RESULTS_ROOT}/${run_id}"
  mkdir -p "$RUN_DIR"
  ln -sfn "$RUN_DIR" "${RESULTS_ROOT}/latest"

  log "Results directory: ${RUN_DIR}"
  log "Using main binaries rather than benchmark binaries because the benchmark path initializes the PMU cycle counter and can fault with illegal-instruction on some systems."

  local mode variant
  for mode in "${SELECTED_MODES[@]}"; do
    for variant in "${SELECTED_VARIANTS[@]}"; do
      profile_one "$mode" "$variant"
    done
  done

  write_run_summary
}

main "$@"
