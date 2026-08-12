#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
PAPER="$PROJECT_DIR/latex/main.tex"
CONCLUSION="$PROJECT_DIR/latex/sections/37-paper-freeze.tex"
LEDGER="$PROJECT_DIR/CLAIM_LEDGER.md"
GRAPH="$PROJECT_DIR/THEOREM_GRAPH.md"
ARTIFACTS="$PROJECT_DIR/manifests/paper-artifacts.md"
SUMMARY=${PAPER_FREEZE_SUMMARY:-}
if [ -z "$SUMMARY" ]; then
  SUMMARY="$PROJECT_DIR/logs/verify-all-summary.txt"
fi
MANIFEST="$PROJECT_DIR/manifests/proof-targets.txt"

require_fixed() {
  pattern=$1
  file=$2
  if ! rg -F "$pattern" "$file" > /dev/null; then
    printf 'FAIL paper-freeze marker missing: %s in %s\n' "$pattern" "$file"
    exit 1
  fi
}

require_fixed 'Machine-Checked Refinement Slices' "$PAPER"
require_fixed '\input{sections/37-paper-freeze}' "$PAPER"

for file in "$CONCLUSION" "$LEDGER" "$GRAPH" "$ARTIFACTS"; do
  require_fixed 'PAPER-KG' "$file"
  require_fixed 'PAPER-SIGN' "$file"
  require_fixed 'PAPER-VERIFY' "$file"
  require_fixed 'PAPER-SIGN-VERIFY' "$file"
  require_fixed 'A s = q j' "$file"
  require_fixed 'S-1' "$file"
  require_fixed 'V-3' "$file"
  require_fixed 'verify_matrix_ntt_acc_mode2_cols4_correct' "$file"
  require_fixed 'rq_mul_coeff_foldr_to_bigi' "$file"
  require_fixed 'full_ntt_montgomery_spectral_action' "$file"
  require_fixed 'verify_crt_freeze_mode2_word_exact' "$file"
done

require_fixed 'PAPER-FROZEN' "$CONCLUSION"
require_fixed 'PAPER-FROZEN' "$ARTIFACTS"

require_fixed 'sf_challenge_mode2_highbits_lsb_sampleinball_correct' "$CONCLUSION"
require_fixed 'verify_tail_m23_highbits_lsb_sampleinball_correct' "$CONCLUSION"
require_fixed 'sf_challenge_mode2_highbits_lsb_sampleinball_correct' "$ARTIFACTS"
require_fixed 'verify_tail_m23_highbits_lsb_sampleinball_correct' "$ARTIFACTS"

target_count=$(awk 'NF && $1 !~ /^#/ { count++ } END { print count + 0 }' "$MANIFEST")
if [ "$target_count" -ne 82 ]; then
  printf 'FAIL paper-freeze proof manifest count: %s\n' "$target_count"
  exit 1
fi

if [ "${PAPER_FREEZE_SCOPE_ONLY:-0}" != 1 ]; then
  fresh_count=$(rg -c '^PASS fresh compile' "$SUMMARY" || true)
  result_count=$(rg -c '^RESULT PASS authored-targets=82 cache=-no-eco$' \
    "$SUMMARY" || true)
  if [ "$fresh_count" -ne 82 ] || [ "$result_count" -ne 1 ]; then
    printf 'FAIL paper-freeze aggregate evidence: fresh=%s result=%s\n' \
      "$fresh_count" "$result_count"
    exit 1
  fi
fi

if rg -n \
    '(A[[:space:]]*s[[:space:]]*=[[:space:]]*q[[:space:]]*j|S-1--S-7|V-3/V-4).{0,32}(\[PROVED\]|\| PROVED|\\status\{PROVED\})|(\[PROVED\]|\| PROVED|\\status\{PROVED\}).{0,32}(A[[:space:]]*s[[:space:]]*=[[:space:]]*q[[:space:]]*j|S-1--S-7|V-3/V-4)' \
    "$PAPER" "$CONCLUSION" "$LEDGER" "$GRAPH" "$ARTIFACTS"; then
  printf 'FAIL forbidden paper-level proof promotion\n'
  exit 1
fi

if [ "${PAPER_FREEZE_SCOPE_ONLY:-0}" = 1 ]; then
  printf 'PASS paper-freeze scope audit\n'
else
  printf 'PASS paper-freeze scope and 82-target evidence audit\n'
fi
