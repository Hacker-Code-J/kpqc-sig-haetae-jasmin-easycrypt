#!/usr/bin/env bash
## SPDX-License-Identifier: MIT
##
## kat.sh — build HAETAE from source and verify that the generated Known Answer
## Tests (KAT) match the committed reference files under kat/.
##
## This is the single source of truth for KAT testing, used both locally and by
## .github/workflows/kat.yml.  The committed kat/ files are "golden" files: the
## invariant is that a fresh build of src/ reproduces them byte-for-byte.
##
##   ./kat.sh check  [variant ...]   build + generate + diff against kat/  (CI)
##   ./kat.sh update [variant]       regenerate and OVERWRITE kat/         (dev)
##   ./kat.sh list                   show variants and this CPU's ISA support
##
## variants:
##   ref      reference_implementation
##   avx2     optimized_implementation, AVX2 baseline
##   avx512   optimized_implementation, AVX2 + AVX-512  (opt-in)
##   all      ref avx2 avx512  (avx512 auto-skipped when the CPU can't run it)
##
## `update` defaults to `ref`: the reference implementation defines the KAT and
## the optimized variants must match it.  See kat/README.md for the workflow to
## follow when a change legitimately alters the KAT.

set -euo pipefail

# ----------------------------- repo config ---------------------------------
SCHEME="haetae"
KAT_PREFIX="PQCsignKAT_haetae"
MODES=(mode2 mode3 mode5)
CMAKE_DISABLE_TESTS="-DHAETAE_BUILD_TEST=OFF"
CMAKE_ENABLE_AVX512="-DHAETAE_USE_AVX512=ON"
# ---------------------------------------------------------------------------

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KAT_DIR="${REPO_ROOT}/kat"
SUMS_FILE="${KAT_DIR}/SHA256SUMS"
JOBS="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"
DIFF_CONTEXT_LINES="${KAT_DIFF_LINES:-15}"

C_RED=$'\033[31m'; C_GRN=$'\033[32m'; C_YEL=$'\033[33m'; C_RST=$'\033[0m'
[ -t 1 ] || { C_RED=""; C_GRN=""; C_YEL=""; C_RST=""; }

die()  { echo "${C_RED}error:${C_RST} $*" >&2; exit 1; }
warn() { echo "${C_YEL}warning:${C_RST} $*" >&2; }

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1
  else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

impl_dir_for() {
  case "$1" in
    ref) echo "reference_implementation" ;;
    avx2|avx512) echo "optimized_implementation" ;;
    *) die "unknown variant: $1 (expected ref|avx2|avx512)" ;;
  esac
}
build_dir_for() { echo "${REPO_ROOT}/$(impl_dir_for "$1")/build/kat-$1"; }

cpu_flag() {
  if [ -r /proc/cpuinfo ]; then grep -qw "$1" /proc/cpuinfo
  elif command -v sysctl >/dev/null 2>&1; then
    sysctl -a 2>/dev/null | tr 'A-Z.' 'a-z ' | grep -qw "$1"
  else return 1; fi
}
cpu_supports() {
  case "$1" in
    ref) return 0 ;;
    avx2) cpu_flag avx2 ;;
    avx512) cpu_flag avx512f && cpu_flag avx512bw && cpu_flag avx512dq && cpu_flag avx512vl ;;
  esac
}

# Configure + build only the KAT targets for a variant.
build_variant() {
  local variant="$1"
  local src="${REPO_ROOT}/$(impl_dir_for "$variant")"
  local build; build="$(build_dir_for "$variant")"
  local -a extra=(); [ "$variant" = "avx512" ] && extra=("${CMAKE_ENABLE_AVX512}")
  local -a targets=(); local m
  for m in "${MODES[@]}"; do targets+=("${SCHEME}-${m}-kat"); done

  echo "==> configuring ${variant} (${src##*/})"
  cmake -S "$src" -B "$build" -DCMAKE_BUILD_TYPE=Release "${CMAKE_DISABLE_TESTS}" "${extra[@]}"
  echo "==> building ${variant}: ${targets[*]}"
  cmake --build "$build" --target "${targets[@]}" -j "$JOBS"
}

# Run every mode's KAT binary in a clean output dir; echo that dir.
generate_kat() {
  local variant="$1"
  local build; build="$(build_dir_for "$variant")"
  local out="${build}/kat-out"; local m
  rm -rf "$out"; mkdir -p "$out"
  for m in "${MODES[@]}"; do
    ( cd "$out" && "${build}/bin/${SCHEME}-${m}-kat" >/dev/null )
  done
  echo "$out"
}

cmd_check() {
  local -a variants=("$@")
  [ ${#variants[@]} -eq 0 ] && variants=(ref avx2 avx512)
  local overall=0 ran=0 variant m ext gen ref

  for variant in "${variants[@]}"; do
    if [ "$variant" = "all" ]; then cmd_check ref avx2 avx512; return $?; fi
    if ! cpu_supports "$variant"; then
      if [ "${KAT_REQUIRE_ALL:-0}" = "1" ]; then
        die "CPU cannot run '${variant}' (missing ISA) and KAT_REQUIRE_ALL=1"
      fi
      warn "CPU cannot run '${variant}' — skipping.  (set KAT_REQUIRE_ALL=1 to make this fatal)"
      continue
    fi
    ran=$((ran+1))
    echo ""; echo "======== KAT check: ${variant} ========"
    build_variant "$variant"
    local out; out="$(generate_kat "$variant")"

    local variant_fail=0
    for m in "${MODES[@]}"; do
      for ext in req rsp; do
        gen="${out}/${KAT_PREFIX}_${m}.${ext}"
        ref="${KAT_DIR}/${KAT_PREFIX}_${m}.${ext}"
        if [ ! -f "$ref" ]; then
          echo "  ${C_RED}[MISS]${C_RST} ${variant}/${m}.${ext}: no committed reference"
          variant_fail=1; continue
        fi
        if diff -q "$gen" "$ref" >/dev/null 2>&1; then
          echo "  ${C_GRN}[PASS]${C_RST} ${variant}/${m}.${ext}"
        else
          variant_fail=1
          echo "  ${C_RED}[FAIL]${C_RST} ${variant}/${m}.${ext}"
          echo "         committed sha256: $(sha256_of "$ref")"
          echo "         generated sha256: $(sha256_of "$gen")"
          echo "         differing lines : $(diff "$ref" "$gen" | grep -c '^[<>]' || true)"
          echo "         --- diff (committed <  vs  > generated), first ${DIFF_CONTEXT_LINES} changed lines ---"
          diff "$ref" "$gen" | grep '^[<>]' | head -n "$DIFF_CONTEXT_LINES" | sed 's/^/         /'
        fi
      done
    done
    if [ "$variant_fail" -ne 0 ]; then overall=1; echo "  ${C_RED}==> ${variant} FAILED${C_RST}"
    else echo "  ${C_GRN}==> ${variant} OK${C_RST}"; fi
  done

  # SHA256SUMS integrity check (compact, reviewable guard against partial commits).
  if [ -f "$SUMS_FILE" ]; then
    echo ""; echo "======== SHA256SUMS integrity ========"
    if ( cd "$KAT_DIR" && sha256sum -c --status SHA256SUMS ); then
      echo "  ${C_GRN}[PASS]${C_RST} committed kat/ files match kat/SHA256SUMS"
    else
      overall=1
      echo "  ${C_RED}[FAIL]${C_RST} kat/SHA256SUMS does not match committed kat/ files"
      ( cd "$KAT_DIR" && sha256sum -c SHA256SUMS 2>&1 | grep -v ': OK$' | sed 's/^/         /' ) || true
    fi
  fi

  echo ""
  if [ "$ran" -eq 0 ]; then
    warn "no variants were runnable on this CPU"
  fi
  if [ "$overall" -ne 0 ]; then
    echo "${C_RED}KAT CHECK FAILED.${C_RST}" >&2
    echo "If this change is an INTENTIONAL KAT update, regenerate and commit:" >&2
    echo "    ./kat.sh update           # regenerates kat/ from reference_implementation" >&2
    echo "    git add kat/ && git commit" >&2
    echo "See kat/README.md for the full procedure." >&2
    return 1
  fi
  echo "${C_GRN}KAT CHECK PASSED${C_RST} (${ran} variant(s))."
}

cmd_update() {
  local variant="${1:-ref}"
  cpu_supports "$variant" || die "CPU cannot run '${variant}'; pick a variant this machine supports"
  echo "==> regenerating committed KAT from '${variant}'"
  build_variant "$variant"
  local out; out="$(generate_kat "$variant")"
  local m ext changed=0
  for m in "${MODES[@]}"; do
    for ext in req rsp; do
      local gen="${out}/${KAT_PREFIX}_${m}.${ext}"
      local ref="${KAT_DIR}/${KAT_PREFIX}_${m}.${ext}"
      if [ -f "$ref" ] && diff -q "$gen" "$ref" >/dev/null 2>&1; then
        echo "  [unchanged] ${m}.${ext}"
      else
        cp -f "$gen" "$ref"
        echo "  ${C_YEL}[updated]${C_RST}   ${m}.${ext}  -> $(sha256_of "$ref")"
        changed=1
      fi
    done
  done
  ( cd "$KAT_DIR" && sha256sum ${KAT_PREFIX}_*.req ${KAT_PREFIX}_*.rsp > SHA256SUMS )
  echo "==> wrote kat/SHA256SUMS"
  if [ "$changed" -eq 0 ]; then
    echo "${C_GRN}KAT already up to date${C_RST} — nothing to commit."
  else
    echo "${C_YEL}KAT updated.${C_RST}  Review 'git diff kat/SHA256SUMS' and commit kat/ together with your source change."
  fi
}

cmd_list() {
  echo "scheme : ${SCHEME}"
  echo "modes  : ${MODES[*]}"
  echo "kat dir: ${KAT_DIR}"
  echo ""
  printf "%-8s %-28s %s\n" "variant" "implementation" "CPU support"
  for v in ref avx2 avx512; do
    if cpu_supports "$v"; then s="${C_GRN}yes${C_RST}"; else s="${C_RED}no${C_RST}"; fi
    printf "%-8s %-28s %b\n" "$v" "$(impl_dir_for "$v")" "$s"
  done
}

main() {
  local cmd="${1:-check}"; shift || true
  case "$cmd" in
    check)  cmd_check "$@" ;;
    update) cmd_update "$@" ;;
    list)   cmd_list ;;
    -h|--help|help) sed -n '2,40p' "${BASH_SOURCE[0]}" | sed 's/^## \{0,1\}//' ;;
    *) die "unknown command: ${cmd} (expected check|update|list)" ;;
  esac
}
main "$@"
