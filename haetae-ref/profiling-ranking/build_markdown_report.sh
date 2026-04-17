#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RESULTS_ROOT="${SCRIPT_DIR}/results"
DEFAULT_RESULTS_LINK="${RESULTS_ROOT}/latest"
RENDERER="${SCRIPT_DIR}/render_markdown_report.py"

log() {
  printf '[%s] %s\n' "$(date '+%H:%M:%S')" "$*"
}

die() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage: profiling/build_markdown_report.sh [results-dir]

Builds a Markdown profiling report and PNG visualizations from an existing
profiling results directory. If no results directory is provided, the script
uses profiling/results/latest.
EOF
}

main() {
  if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
  fi

  command -v python3 >/dev/null 2>&1 || die "python3 is required"
  [[ -f "${RENDERER}" ]] || die "missing renderer: ${RENDERER}"

  local results_dir
  results_dir="${1:-${DEFAULT_RESULTS_LINK}}"
  results_dir="$(readlink -f "${results_dir}")"
  [[ -d "${results_dir}" ]] || die "missing results directory: ${results_dir}"

  log "Rendering Markdown report from ${results_dir}"
  export MPLCONFIGDIR="${results_dir}/.mplconfig"
  mkdir -p "${MPLCONFIGDIR}"
  python3 "${RENDERER}" --results-dir "${results_dir}"
  log "Wrote ${results_dir}/haetae_build_bin_profiling_report.md"
  log "Wrote ${results_dir}/haetae_load_rankings.md"
  log "Wrote ${results_dir}/haetae_load_rankings.tsv"
  log "Wrote ${results_dir}/visualizations/"
}

main "$@"
