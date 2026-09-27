#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
mkdir -p build

if ! python3 scripts/materialize.py --check >build/checked-hyperball-materialization.log 2>&1; then
  cat build/checked-hyperball-materialization.log >&2
  exit 1
fi

checker="${JASMIN_CT:-jasmin-ct}"
"$checker" --version >build/checked-hyperball-ct-version.log 2>&1
selectors=(
  --slice checked_scalar_ct_jazz
  --slice checked_norm_ct_jazz
  --slice checked_vector_ct_jazz
  --slice checked_phase_ct_jazz
  --slice checked_phase_values_ct_jazz
  --slice checked_sign_ct_jazz
)

run_checks() {
  local label="$1" input_source="$2" check
  shift 2
  local -a check_command
  for check in ct sct; do
    check_command=("$checker")
    if [[ "$check" == sct ]]; then
      check_command+=(--sct)
    fi
    check_command+=("$@" "$input_source")
    printf '%q ' "${check_command[@]}" >"build/$label-$check.command"
    printf '\n' >>"build/$label-$check.command"
    if ! "${check_command[@]}" >"build/$label-$check.log" 2>&1; then
      cat "build/$label-$check.log" >&2
      exit 1
    fi
  done
}

run_checks checked-hyperball tests/checked-hyperball-ct.jazz "${selectors[@]}"
run_checks checked-hyperball-standalone jasmin/hyperball.jazz \
  --slice polyfixveclk_sample_hyperball_mode2_jazz \
  --slice polyfixveclk_sample_hyperball_mode3_jazz \
  --slice polyfixveclk_sample_hyperball_mode5_jazz
run_checks checked-hyperball-signer jasmin/sign.jazz \
  --slice _sf_hyperball_mode2 --slice _sf_hyperball_mode3 --slice _sf_hyperball_mode5

printf '%s\n' 'PASS: CT and SCT for six checked paths and standalone/signer modes 2, 3 and 5'
