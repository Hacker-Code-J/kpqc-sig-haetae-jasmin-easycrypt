#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

for required in \
  "$SCRIPT_DIR/../CLAIM_LEDGER.md" \
  "$SCRIPT_DIR/../THEOREM_GRAPH.md" \
  "$SCRIPT_DIR/../WEEK9_REPORT.md" \
  "$SCRIPT_DIR/../WEEK10_REPORT.md" \
  "$SCRIPT_DIR/../WEEK11_REPORT.md" \
  "$SCRIPT_DIR/../WEEK12_REPORT.md" \
  "$SCRIPT_DIR/../WEEK13_REPORT.md" \
  "$SCRIPT_DIR/../WEEK14_REPORT.md" \
  "$SCRIPT_DIR/../WEEK15_REPORT.md" \
  "$SCRIPT_DIR/../WEEK16_MINCORE_PLAN.md" \
  "$SCRIPT_DIR/../WEEK16_KG_REPORT.md" \
  "$SCRIPT_DIR/../WEEK16_KG_NTT_MUL_REPORT.md" \
  "$SCRIPT_DIR/../HBZ_FULL_WRAPPER_COMPOSITION.md" \
  "$SCRIPT_DIR/../RANS_ACTUAL_SUCCESS_WITNESS.md" \
  "$SCRIPT_DIR/../RANS_BYTE_STACK_INVARIANT.md" \
  "$SCRIPT_DIR/../RANS_ENCODER_INVARIANT.md" \
  "$SCRIPT_DIR/../RANS_DECODER_INVARIANT.md" \
  "$SCRIPT_DIR/../RANS_CORE_COMPOSITION.md" \
  "$SCRIPT_DIR/../MODE2_HBZ_CODEC_OBLIGATIONS.md" \
  "$SCRIPT_DIR/../manifests/proof-targets.txt" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansActualInverse.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansEncoderActualTraceClosure.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansEncoderOuterRefinement.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansDecoderActualTrace.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansDecoderTopHoare.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansCoreCompositionBridge.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansCoreActualInverse.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2HbzInternalBoundaries.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2HbzFullEncodeTrace.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2HbzFullDecodeInverse.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2HbzFullActualInverse.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2HbzSignatureBoundaryLift.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansAllSixBudget.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/sign/Mode2RansActualSuccessWitness.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/keygen/Mode2KeygenSnapshotAlgebra.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/keygen/Mode2KeygenCoreEquation.ec" \
  "$SCRIPT_DIR/../easycrypt/refinement/keygen/Mode2KeygenNttMulBridge.ec"
do
  if [ ! -f "$required" ]; then
    printf 'FAIL missing source-of-truth artifact: %s\n' "$required" >&2
    exit 1
  fi
done

snapshot_target_count=$(sed -n \
  's/.*\\AuthoredTargetCount}{\([0-9][0-9]*\)}.*/\1/p' \
  "$SCRIPT_DIR/status.tex")
manifest_target_count=$(awk 'NF && $1 !~ /^#/ { count++ } END { print count + 0 }' \
  "$SCRIPT_DIR/../manifests/proof-targets.txt")

if [ -z "$snapshot_target_count" ] || \
   [ "$snapshot_target_count" != "$manifest_target_count" ]; then
  printf 'FAIL authored target snapshot=%s manifest=%s\n' \
    "${snapshot_target_count:-missing}" "$manifest_target_count" >&2
  exit 1
fi

cd "$SCRIPT_DIR"
latexmk -xelatex -halt-on-error -file-line-error -interaction=nonstopmode main.tex

if rg -ni 'undefined (reference|references|citation|citations)|citation .* undefined|reference .* undefined|LaTeX Error' \
    main.log main.fls main.fdb_latexmk 2>/dev/null; then
  printf 'FAIL algebraist guide has an undefined reference/citation or LaTeX error\n' >&2
  exit 1
fi

printf 'PASS algebraist guide build %s/main.pdf\n' "$SCRIPT_DIR"
