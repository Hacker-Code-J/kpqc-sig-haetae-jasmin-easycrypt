#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
WHY3_BIN=${WHY3:-why3}
WHY3SERVER_BIN=${WHY3SERVER:-"$($WHY3_BIN --print-libdir)/why3server"}
MANIFEST="$PROJECT_DIR/manifests/proof-targets.txt"
EXTRACTION_HASHES="$PROJECT_DIR/manifests/generated-extractions.sha256"
LOG_DIR="$PROJECT_DIR/logs"
LATEX_DIR="$PROJECT_DIR/latex"

mkdir -p "$LOG_DIR"
WORK_DIR=$(mktemp -d)
SERVER_SOCKET=${WHY3_SERVER_SOCKET:-"$WORK_DIR/why3server.socket"}
SERVER_PID=
cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  rm -rf "$WORK_DIR"
}
trap cleanup EXIT HUP INT TERM

SUMMARY="$LOG_DIR/verify-all-summary.txt"
: > "$SUMMARY"

if [ -n "${WHY3_SERVER_SOCKET:-}" ]; then
  if [ ! -S "$SERVER_SOCKET" ]; then
    printf 'FAIL supplied Why3 server socket is unavailable: %s\n' \
      "$SERVER_SOCKET" | tee -a "$SUMMARY"
    exit 1
  fi
  printf 'PASS supplied Why3 server socket\n' | tee -a "$SUMMARY"
else
  "$WHY3SERVER_BIN" --socket "$SERVER_SOCKET" -j 1 \
    > "$LOG_DIR/why3server.log" 2>&1 &
  SERVER_PID=$!
  server_wait=0
  while [ ! -S "$SERVER_SOCKET" ] && [ "$server_wait" -lt 50 ]; do
    sleep 0.1
    server_wait=$((server_wait + 1))
  done
  if [ ! -S "$SERVER_SOCKET" ]; then
    printf 'FAIL Why3 server startup\n' | tee -a "$SUMMARY"
    exit 1
  fi
fi

"$SCRIPT_DIR/check-source-drift.sh" \
  > "$LOG_DIR/source-drift.log" 2>&1
printf 'PASS source drift\n' | tee -a "$SUMMARY"

"$SCRIPT_DIR/check-proof-holes.sh" \
  > "$LOG_DIR/proof-hole-scan.log" 2>&1
printf 'PASS proof-hole scan\n' | tee -a "$SUMMARY"

PAPER_FREEZE_SCOPE_ONLY=1 "$SCRIPT_DIR/check-paper-freeze.sh" \
  > "$LOG_DIR/paper-freeze-scope-audit.log" 2>&1
printf 'PASS paper-freeze claim-scope audit\n' | tee -a "$SUMMARY"

find "$PROJECT_DIR/easycrypt" -type f -name '*.ec' \
  | sed "s#^$PROJECT_DIR/##" | LC_ALL=C sort \
  > "$WORK_DIR/discovered-targets.txt"
LC_ALL=C sort "$MANIFEST" > "$WORK_DIR/manifest-targets.txt"
manifest_target_count=$(awk 'NF && $1 !~ /^#/ { count++ } END { print count + 0 }' \
  "$MANIFEST")
if ! diff -u "$WORK_DIR/manifest-targets.txt" \
    "$WORK_DIR/discovered-targets.txt" \
    > "$LOG_DIR/target-manifest.log"; then
  printf 'FAIL unmanifested or missing proof target\n' | tee -a "$SUMMARY"
  cat "$LOG_DIR/target-manifest.log"
  exit 1
fi
if [ "$manifest_target_count" -ne 82 ]; then
  printf 'FAIL expected 82 authored proof targets, found %s\n' \
    "$manifest_target_count" | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS proof target manifest\n' | tee -a "$SUMMARY"

if rg -n '^[[:space:]]*axiom[[:space:]]' "$PROJECT_DIR/easycrypt" \
    > "$LOG_DIR/authored-axiom-scan.log"; then
  printf 'FAIL authored axiom declaration\n' | tee -a "$SUMMARY"
  cat "$LOG_DIR/authored-axiom-scan.log"
  exit 1
fi
printf 'PASS authored axiom scan\n' | tee -a "$SUMMARY"

if rg -n '^[[:space:]]*(print[[:space:]]+(goal|all)|lemma[[:space:]]+(debug|tmp|temporary)([^[:alnum:]_]|$)|op[[:space:]]+(debug|tmp|temporary)([^[:alnum:]_]|$))' \
    "$PROJECT_DIR/easycrypt" > "$LOG_DIR/debug-temporary-scan.log"; then
  printf 'FAIL debug or temporary declaration\n' | tee -a "$SUMMARY"
  cat "$LOG_DIR/debug-temporary-scan.log"
  exit 1
fi
printf 'PASS debug/temporary declaration scan\n' | tee -a "$SUMMARY"

EXACT_MU="$PROJECT_DIR/easycrypt/refinement/composition/ExactMuTopControl.ec"
EXACT_COMPOSITION="$PROJECT_DIR/easycrypt/refinement/composition/ExactMode2RawMuComposition.ec"
if ! rg -F 'equiv [Sign._sf_mu_rawpre ~ Verify.__verify_hash_mu :' \
    "$EXACT_MU" > "$LOG_DIR/generated-top-control-scan.log"; then
  printf 'FAIL generated Sign/Verify top procedures absent from direct theorem\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if ! rg -F 'lemma raw_prelen_shr63_zero' "$EXACT_MU" \
    >> "$LOG_DIR/generated-top-control-scan.log" || \
   ! rg -F 'rcondt{1} 18' "$EXACT_MU" \
    >> "$LOG_DIR/generated-top-control-scan.log"; then
  printf 'FAIL raw_prelen is not connected to the generated Verify branch\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if ! rg -F 'lemma generated_raw_mu_preconditions_from_keygen_prefix' \
    "$EXACT_COMPOSITION" > "$LOG_DIR/generated-top-reachability-scan.log" || \
   ! rg -F 'lemma keypair_internal_return_reaches_generated_raw_mu_preconditions' \
    "$EXACT_COMPOSITION" >> "$LOG_DIR/generated-top-reachability-scan.log" || \
   ! rg -F 'SignMu._sf_mu_rawpre' "$EXACT_COMPOSITION" \
    >> "$LOG_DIR/generated-top-reachability-scan.log" || \
   ! rg -F 'VerifyMu.__verify_hash_mu' "$EXACT_COMPOSITION" \
    >> "$LOG_DIR/generated-top-reachability-scan.log"; then
  printf 'FAIL generated raw composition reachability surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'delta_(Sign|Verify|Encoding)[[:space:]]*=[[:space:]]*0' \
    "$PROJECT_DIR" --glob '!logs/**' --glob '!latex/main.*' \
    > "$LOG_DIR/delta-scope-scan.log"; then
  printf 'FAIL local mu zero-loss promoted to a full implementation delta\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS generated top control and reachability source checks\n' \
  | tee -a "$SUMMARY"

RAW_COMPOSITION="$PROJECT_DIR/easycrypt/refinement/composition"
if ! rg -F 'Raw.cryptolab_haetae_mode2_keypair_internal ~' \
    "$RAW_COMPOSITION/RawApiKeygenExportComposition.ec" \
    > "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'Sign.cryptolab_haetae_mode2_signature_internal ~' \
    "$RAW_COMPOSITION/RawApiCallerMuTrace.ec" >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'Verify.cryptolab_haetae_mode2_verify_internal ~ VerifyCryptolabMuTrace.run' \
    "$RAW_COMPOSITION/RawApiVerifyMuTrace.ec" >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'lemma keypair_raw_api_exports_matching_prefixes' \
    "$RAW_COMPOSITION/RawApiKeygenSequentialExport.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'OBL-API-ADDRESS-BINDING' \
    "$RAW_COMPOSITION/RawApiAddressBridge.ec" >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'raw_api_key_memory_reaches_mu_zero_loss' \
    "$RAW_COMPOSITION/RawApiMuReachability.ec" >> "$LOG_DIR/raw-api-bridge-scan.log"; then
  printf 'FAIL week4 raw API bridge/theorem naming scan\n' | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'stores[[:space:]]+mem[[:space:]]+0' \
    "$RAW_COMPOSITION/RawApiMuReachability.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log"; then
  printf 'FAIL constructed stores witness in Week4 raw API reachability\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if ! rg -F 'lemma verify_full_m23_trace_accept_implies_tail_reached' \
    "$RAW_COMPOSITION/RawApiVerifyAcceptTrace.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'lemma verify_cryptolab_actual_accept_binds_hash_inputs' \
    "$RAW_COMPOSITION/RawApiVerifyAcceptTrace.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'lemma actual_raw_keygen_exports_matching_prefixes' \
    "$RAW_COMPOSITION/RawApiAcceptedMuComposition.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'lemma actual_raw_sign_exact_mu_trace' \
    "$RAW_COMPOSITION/RawApiAcceptedMuComposition.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log" \
  || ! rg -F 'lemma raw_api_accepting_execution_hash_mu_zero_loss' \
    "$RAW_COMPOSITION/RawApiAcceptedMuComposition.ec" \
    >> "$LOG_DIR/raw-api-bridge-scan.log"; then
  printf 'FAIL Week5 accepted raw API theorem surface\n' | tee -a "$SUMMARY"
  exit 1
fi
if rg -n '(raw_api_caller_chain_residual|keypair_raw_api_exports_matching_prefixes_residual|verify_raw_api_exact_mu_trace_residual_obligation|cryptolab_verify_internal_exact_mu_trace_residual_obligation)' \
    "$PROJECT_DIR/easycrypt" >> "$LOG_DIR/raw-api-bridge-scan.log"; then
  printf 'FAIL obsolete boolean residual placeholder remains\n' | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week4/5 raw API bridge theorem surface scan\n' \
  | tee -a "$SUMMARY"

WEEK6_FRAME="$RAW_COMPOSITION/RawApiSignOutputFrame.ec"
WEEK6_LOCAL="$RAW_COMPOSITION/RegionLocalMuTop.ec"
WEEK6_DIRECT="$RAW_COMPOSITION/RawApiDirectObservedMu.ec"
if ! rg -F 'lemma sign_raw_api_frames_reused_regions' "$WEEK6_FRAME" \
    > "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'Sign.cryptolab_haetae_mode2_signature_internal :' "$WEEK6_FRAME" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'lemma sign_output_frame_contract_satisfiable' "$WEEK6_FRAME" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'lemma sign_verify_generated_raw_mu_prefix_regionwise' "$WEEK6_LOCAL" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'equiv [Sign._sf_mu_rawpre ~ Verify.__verify_hash_mu :' "$WEEK6_LOCAL" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'module RawSignThenVerifyActual' "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'Sign.cryptolab_haetae_mode2_signature_internal' "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'Verify.cryptolab_haetae_mode2_verify_internal' "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'lemma raw_sign_then_verify_actual_exact_trace' "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'lemma sign_then_verify_trace_accept_implies_tail_reached' "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log" || \
   ! rg -F 'lemma sign_frame_establishes_raw_mu_read_relation' "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log"; then
  printf 'FAIL Week6 actual frame/region-local/sequential trace surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'stores[[:space:]]+mem[[:space:]]+0' \
    "$WEEK6_FRAME" "$WEEK6_LOCAL" "$WEEK6_DIRECT" \
    >> "$LOG_DIR/week6-theorem-surface-scan.log"; then
  printf 'FAIL constructed stores witness in Week6 API evidence\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week6 actual frame, locality, and trace-boundary source checks\n' \
  | tee -a "$SUMMARY"

WEEK7_CODEC="$PROJECT_DIR/easycrypt/refinement/sign"
if ! rg -F 'lemma pack_sig_prefix_mode2_layout' \
    "$WEEK7_CODEC/Mode2SignaturePrefixPack.ec" \
    > "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F 'Pack._pack_sig_prefix :' \
    "$WEEK7_CODEC/Mode2SignaturePrefixPack.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F 'lemma unpack_sig_prefix_mode2_layout' \
    "$WEEK7_CODEC/Mode2SignaturePrefixUnpack.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F 'Unpack._unpack_sig_prefix :' \
    "$WEEK7_CODEC/Mode2SignaturePrefixUnpack.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F 'lemma pack_unpack_sig_prefix_mode2_roundtrip' \
    "$WEEK7_CODEC/Mode2SignaturePrefixRoundTrip.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F 'sig <@ Pack._pack_sig_prefix' \
    "$WEEK7_CODEC/Mode2SignaturePrefixRoundTrip.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F '(decoded_cp, decoded_low) <@ Unpack._unpack_sig_prefix' \
    "$WEEK7_CODEC/Mode2SignaturePrefixRoundTrip.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log" || \
   ! rg -F 'lemma prefix_codec_preconditions_satisfiable' \
    "$WEEK7_CODEC/Mode2SignaturePrefixCodec.ec" \
    >> "$LOG_DIR/week7-signature-codec-scan.log"; then
  printf 'FAIL Week7 actual signature-prefix codec theorem surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'delta_mu_raw_api_accept[[:space:]]*=[[:space:]]*0' \
    "$PROJECT_DIR/easycrypt" \
    >> "$LOG_DIR/week7-signature-codec-scan.log"; then
  printf 'FAIL unavailable raw-API observed-mu zero-loss claim authored\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week7 actual prefix-codec and replay-boundary source checks\n' \
  | tee -a "$SUMMARY"

WEEK8_HBZ="$PROJECT_DIR/easycrypt/refinement/sign"
if ! rg -F 'lemma encode_hb_z1_prepare_mode2_correct' \
    "$WEEK8_HBZ/Mode2HbzPrepare.ec" \
    > "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma decode_hb_z1_apply_mode2_correct' \
    "$WEEK8_HBZ/Mode2HbzApply.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma encode_prepare_decode_apply_mode2_inverse' \
    "$WEEK8_HBZ/Mode2HbzLeafRoundTrip.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma pack_target_encode_hb_z1_full_exact_focused' \
    "$WEEK8_HBZ/Mode2HbzActualBoundary.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma unpack_target_decode_hb_z1_full_exact_focused' \
    "$WEEK8_HBZ/Mode2HbzActualBoundary.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'op mode2_hbz_table_certificate' \
    "$WEEK8_HBZ/Mode2HbzTableCertificate.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma actual_mode2_hbz_tables_certified' \
    "$WEEK8_HBZ/Mode2HbzSymbolWordsGenerated.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma hbz_fast_step_decode_inverse' \
    "$WEEK8_HBZ/Mode2RansCore.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log" || \
   ! rg -F 'lemma hbz_fast_step_preconditions_satisfiable' \
    "$WEEK8_HBZ/Mode2RansCore.ec" \
    >> "$LOG_DIR/week8-hbz-surface-scan.log"; then
  printf 'FAIL Week8 HBZ/rANS theorem surface\n' | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week8 HBZ/rANS theorem surface scan\n' \
  | tee -a "$SUMMARY"

WEEK9_RANS="$PROJECT_DIR/easycrypt/refinement/sign"
if ! rg -F 'lemma renorm_bytes_readback' \
    "$WEEK9_RANS/Mode2RansByteStack.ec" \
    > "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'lemma normalized_fast_step_state_bounds' \
    "$WEEK9_RANS/Mode2RansByteStack.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'lemma encoder_two_byte_decoder_order' \
    "$WEEK9_RANS/Mode2RansNormalization.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'lemma copy_encoded_suffix_correct' \
    "$WEEK9_RANS/Mode2RansSuffixCopy.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'hoare [Copy.__copy_encoded_suffix :' \
    "$WEEK9_RANS/Mode2RansSuffixCopy.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_mode2_control' \
    "$WEEK9_RANS/Mode2RansEncodeRefinement.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'hoare [Encode._rans_encode :' \
    "$WEEK9_RANS/Mode2RansEncodeRefinement.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_decode_mode2_control' \
    "$WEEK9_RANS/Mode2RansDecodeRefinement.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'hoare [Decode._rans_decode :' \
    "$WEEK9_RANS/Mode2RansDecodeRefinement.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'module Mode2RansActualHarness' \
    "$WEEK9_RANS/Mode2RansActualInverse.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F '(encoded, encoder_state) <@ Encode._rans_encode' \
    "$WEEK9_RANS/Mode2RansActualInverse.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F 'copied <@ Copy.__copy_encoded_suffix' \
    "$WEEK9_RANS/Mode2RansActualInverse.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log" || \
   ! rg -F '(decoded, decoder_state) <@ Decode._rans_decode' \
    "$WEEK9_RANS/Mode2RansActualInverse.ec" \
    >> "$LOG_DIR/week9-rans-surface-scan.log"; then
  printf 'FAIL Week9 byte-stack/copy/actual harness theorem surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'delta_(encoding|challenge|Sign|Verify)[[:space:]]*=[[:space:]]*0' \
    "$WEEK9_RANS" > "$LOG_DIR/week9-rans-overclaim-scan.log"; then
  printf 'FAIL Week9 partial rANS evidence promoted to a zero-loss delta\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week9 byte-stack, actual-copy, and harness boundary checks\n' \
  | tee -a "$SUMMARY"

WEEK10_ENCODER="$PROJECT_DIR/easycrypt/refinement/sign"
if ! rg -F 'lemma symbol_list_of_array_size' \
    "$WEEK10_ENCODER/Mode2RansArrayListBridge.ec" \
    > "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma encode_trace_suffix_extension' \
    "$WEEK10_ENCODER/Mode2RansArrayListBridge.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma actual_mode2_encoder_word_step_correct' \
    "$WEEK10_ENCODER/Mode2RansEncoderWordStep.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma inner_progress_segment_step' \
    "$WEEK10_ENCODER/Mode2RansEncoderInnerProgress.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma actual_encoder_final_state_serialization' \
    "$WEEK10_ENCODER/Mode2RansEncoderSerialization.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'op encoder_inner_segment_inv' \
    "$WEEK10_ENCODER/Mode2RansEncoderTrace.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma encoder_inner_segment_step' \
    "$WEEK10_ENCODER/Mode2RansEncoderTrace.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'encoder_inner_segment_inv x_max x off encp' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualInner.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'hoare [Encode._rans_encode :' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualInner.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_inner_no_underflow' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualInner.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_success_size_bound' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualInner.ec" \
    >> "$LOG_DIR/week10-rans-encoder-surface-scan.log"; then
  printf 'FAIL Week10 encoder bridge/word/inner-loop theorem surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if ! rg -F 'op encoder_outer_tail_inv' \
    "$WEEK10_ENCODER/Mode2RansEncoderTailInvariant.ec" \
    > "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'op encoder_inner_tail_inv' \
    "$WEEK10_ENCODER/Mode2RansEncoderTailInvariant.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma encoder_inner_tail_exit_exact' \
    "$WEEK10_ENCODER/Mode2RansEncoderTailInvariant.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma generated_outer_word_update_matches' \
    "$WEEK10_ENCODER/Mode2RansEncoderGeneratedWordStep.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma generated_encoder_outer_finalize_success' \
    "$WEEK10_ENCODER/Mode2RansEncoderGeneratedFinalization.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_trace_closure' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualTraceClosure.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'hoare [Encode._rans_encode :' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualTraceClosure.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'trace_bytes (symbol_list_of_array symbols0)' \
    "$WEEK10_ENCODER/Mode2RansEncoderActualTraceClosure.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_trace_refinement' \
    "$WEEK10_ENCODER/Mode2RansEncoderOuterRefinement.ec" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log" || \
   ! rg -F '| OBL-RANS-ENCODE-REFINEMENT | PROVED (success-conditioned partial correctness) |' \
    "$PROJECT_DIR/CLAIM_LEDGER.md" \
    >> "$LOG_DIR/week11-rans-encoder-surface-scan.log"; then
  printf 'FAIL Week11 actual encoder trace-closure theorem surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week10 encoder bridge, word step, serialization, and actual inner-loop checks\n' \
  | tee -a "$SUMMARY"
printf 'PASS Week11 tail-aware actual encoder trace-closure checks\n' \
  | tee -a "$SUMMARY"

WEEK12_DECODER="$PROJECT_DIR/easycrypt/refinement/sign"
if ! rg -F 'lemma actual_rans_decode_trace_refinement' \
    "$WEEK12_DECODER/Mode2RansDecoderTopHoare.ec" \
    > "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'hoare [Decode._rans_decode :' \
    "$WEEK12_DECODER/Mode2RansDecoderTopHoare.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'actual_mode2_decoder_trace_input' \
    "$WEEK12_DECODER/Mode2RansDecoderTopHoare.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'actual_mode2_decoder_trace_post' \
    "$WEEK12_DECODER/Mode2RansDecoderTopHoare.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'BArray24.get64 result.`2 1 = W64.zero' \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'BArray24.get64 result.`2 0 = W64.of_int encoded_size' \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'decoded_symbol_prefix result.`1 expected_symbols mode2_hbz_count' \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'decoded_symbol_tail_frame decoded0 result.`1 mode2_hbz_count' \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'lemma decoder_outer_to_inner_trace_actual_loaded' \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log" || \
   ! rg -F 'lemma decoder_outer_trace_exit_components' \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log"; then
  printf 'FAIL Week12 actual decoder semantic-refinement surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'lossless|islossless|is_lossless' \
    "$WEEK12_DECODER/Mode2RansDecoderTopHoare.ec" \
    "$WEEK12_DECODER/Mode2RansDecoderActualTrace.ec" \
    >> "$LOG_DIR/week12-rans-decoder-surface-scan.log"; then
  printf 'FAIL Week12 decoder theorem overstates termination/losslessness\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week12 actual decoder symbol/off/bad/frame semantic surface\n' \
  | tee -a "$SUMMARY"

WEEK13_CORE="$PROJECT_DIR/easycrypt/refinement/sign"
WEEK13_BRIDGE="$WEEK13_CORE/Mode2RansCoreCompositionBridge.ec"
WEEK13_INVERSE="$WEEK13_CORE/Mode2RansCoreActualInverse.ec"
WEEK13_HARNESS="$WEEK13_CORE/Mode2RansActualInverse.ec"
if ! rg -F 'lemma copied_suffix_is_exact_trace' \
    "$WEEK13_BRIDGE" > "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'lemma segment_matches_implies_exact_decoder_segment_input' \
    "$WEEK13_BRIDGE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'lemma segment_matches_implies_decoder_word_reads' \
    "$WEEK13_BRIDGE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'lemma actual_decoder_input_from_copied_trace' \
    "$WEEK13_BRIDGE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'lemma encoder_success_size_word_bridge' \
    "$WEEK13_BRIDGE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'lemma core_composition_preconditions_satisfiable' \
    "$WEEK13_BRIDGE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_copy_decode_inverse' \
    "$WEEK13_INVERSE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'hoare [Mode2RansActualHarness.run :' \
    "$WEEK13_INVERSE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'call (actual_rans_encode_trace_refinement' \
    "$WEEK13_INVERSE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'call (copy_encoded_suffix_correct' \
    "$WEEK13_INVERSE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'call (actual_rans_decode_trace_refinement' \
    "$WEEK13_INVERSE" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F '(encoded, encoder_state) <@ Encode._rans_encode' \
    "$WEEK13_HARNESS" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F 'copied <@ Copy.__copy_encoded_suffix' \
    "$WEEK13_HARNESS" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F '(decoded, decoder_state) <@ Decode._rans_decode' \
    "$WEEK13_HARNESS" >> "$LOG_DIR/week13-rans-core-surface-scan.log" || \
   ! rg -F '| OBL-RANS-CORE-INVERSE | PROVED (success-conditioned partial correctness) |' \
    "$PROJECT_DIR/CLAIM_LEDGER.md" \
    >> "$LOG_DIR/week13-rans-core-surface-scan.log"; then
  printf 'FAIL Week13 actual rANS core-composition theorem surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
awk '
  /lemma actual_rans_encode_copy_decode_inverse/ { inside = 1 }
  inside { print }
  inside && /==>/ { exit }
' "$WEEK13_INVERSE" > "$WORK_DIR/week13-core-precondition.txt"
if rg -n \
    'encoder_bad[[:space:]]*=|decoder_ran|decoder_bad[[:space:]]*=|decoded_symbol_prefix|actual_core_success_result|actual_mode2_decoder_trace_input|segment_matches[[:space:]]+copied' \
    "$WORK_DIR/week13-core-precondition.txt" \
    >> "$LOG_DIR/week13-rans-core-surface-scan.log"; then
  printf 'FAIL Week13 harness theorem assumes a success/result/trace premise\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'lossless|islossless|is_lossless' \
    "$WEEK13_BRIDGE" "$WEEK13_INVERSE" \
    >> "$LOG_DIR/week13-rans-core-surface-scan.log"; then
  printf 'FAIL Week13 core theorem overstates termination/losslessness\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week13 actual encoder/copy/decoder core-composition surface\n' \
  | tee -a "$SUMMARY"

WEEK14_HBZ="$PROJECT_DIR/easycrypt/refinement/sign"
WEEK14_INTERNAL="$WEEK14_HBZ/Mode2HbzInternalBoundaries.ec"
WEEK14_ENCODER="$WEEK14_HBZ/Mode2HbzFullEncodeTrace.ec"
WEEK14_DECODER="$WEEK14_HBZ/Mode2HbzFullDecodeInverse.ec"
WEEK14_PAIR="$WEEK14_HBZ/Mode2HbzFullActualInverse.ec"
WEEK14_PRODUCTION="$WEEK14_HBZ/Mode2HbzSignatureBoundaryLift.ec"
if ! rg -F 'lemma full_encode_prepare_exact_focused' \
    "$WEEK14_INTERNAL" > "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma full_rans_encode_exact_focused' \
    "$WEEK14_INTERNAL" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma full_rans_decode_exact_focused' \
    "$WEEK14_INTERNAL" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma full_decode_apply_exact_focused' \
    "$WEEK14_INTERNAL" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma prepared_hbz_implies_mode2_symbol_stream' \
    "$WEEK14_INTERNAL" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma decoded_prefix_preserves_prepared_hbz' \
    "$WEEK14_INTERNAL" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma actual_encode_hb_z1_full_mode2_trace' \
    "$WEEK14_ENCODER" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'hoare [Focus._encode_hb_z1_full :' \
    "$WEEK14_ENCODER" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma actual_decode_hb_z1_full_mode2_inverse' \
    "$WEEK14_DECODER" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'hoare [FullDecode._decode_hb_z1_full :' \
    "$WEEK14_DECODER" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma actual_hbz_full_encode_decode_inverse_mode2' \
    "$WEEK14_PAIR" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F '(encoded, size) <@ HbzFullEncode._encode_hb_z1_full' \
    "$WEEK14_PAIR" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F '(decoded, bad) <@ HbzFullDecode._decode_hb_z1_full' \
    "$WEEK14_PAIR" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma signature_pack_unpack_hbz_full_actual_exact' \
    "$WEEK14_PRODUCTION" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'lemma signature_pack_unpack_hbz_full_inverse_mode2' \
    "$WEEK14_PRODUCTION" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F '(encoded, size) <@ Pack._encode_hb_z1_full' \
    "$WEEK14_PRODUCTION" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F '(decoded, bad) <@ Unpack._decode_hb_z1_full' \
    "$WEEK14_PRODUCTION" >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F '| OBL-SIG-HBZ-ENCODE-DECODE | PROVED (success-conditioned partial correctness) |' \
    "$PROJECT_DIR/CLAIM_LEDGER.md" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log"; then
  printf 'FAIL Week14 actual full-HBZ wrapper or production-lift surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
awk '
  /lemma actual_hbz_full_encode_decode_inverse_mode2/ { inside = 1 }
  inside { print }
  inside && /==>/ { exit }
' "$WEEK14_PAIR" > "$WORK_DIR/week14-hbz-pair-precondition.txt"
if rg -n \
    'segment_matches|prepared_hbz_prefix|mode2_hbz_symbol_stream|decoder_ran|decoder_bad|decoded_hbz_prefix|encoded_size|size[[:space:]]*(<>|>)|encoder_success|decoder_success' \
    "$WORK_DIR/week14-hbz-pair-precondition.txt" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log"; then
  printf 'FAIL Week14 pair theorem assumes success, trace, or decoded result\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if ! rg -F 'res.`2 = W64.zero' "$WEEK14_PAIR" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F '!HbzFullActualHarness.decoder_ran' "$WEEK14_PAIR" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'res.`2 <> W64.zero' "$WEEK14_PAIR" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'coeff_tail_frame decoded0 res.`4 mode2_hbz_count' "$WEEK14_PAIR" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log" || \
   ! rg -F 'suffix_frame out0 res.`1 (W64.to_uint res.`2)' "$WEEK14_PAIR" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log"; then
  printf 'FAIL Week14 pair theorem does not retain required failure/success frames\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'lossless|islossless|is_lossless' \
    "$WEEK14_INTERNAL" "$WEEK14_ENCODER" "$WEEK14_DECODER" \
    "$WEEK14_PAIR" "$WEEK14_PRODUCTION" \
    >> "$LOG_DIR/week14-hbz-full-surface-scan.log"; then
  printf 'FAIL Week14 full-wrapper theorem overstates termination/losslessness\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week14 actual full-HBZ failure/success and production-lift surface\n' \
  | tee -a "$SUMMARY"

WEEK15_RANS="$PROJECT_DIR/easycrypt/refinement/sign"
WEEK15_BUDGET="$WEEK15_RANS/Mode2RansAllSixBudget.ec"
WEEK15_CLOSURE="$WEEK15_RANS/Mode2RansEncoderActualTraceClosure.ec"
WEEK15_WITNESS="$WEEK15_RANS/Mode2RansActualSuccessWitness.ec"
if ! rg -F 'lemma zero_hbz_get32' \
    "$WEEK15_BUDGET" > "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma zero_hbz_canonical' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma prepared_zero_hbz_is_all_six' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma actual_focused_encode_hb_z1_prepare_zero_hbz' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma actual_prepare_zero_hbz_all_six' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma symbol6_normalization_len_le1' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma hbz_xmax_symbol6_product' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma symbol6_div256_below_xmax' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma all_six_first_four_no_normalization' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma all_six_normalization_budget' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma all_six_list_normalization_budget' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma all_six_trace_fits_mode2' \
    "$WEEK15_BUDGET" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_failure_trace_cause' \
    "$WEEK15_CLOSURE" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F '1020 < size (encode_trace (symbol_list_of_array symbols0)).`2' \
    "$WEEK15_CLOSURE" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma actual_rans_encode_all_six_success' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'hoare [Encode._rans_encode :' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma actual_encode_hb_z1_full_zero_success' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'hoare [Focus._encode_hb_z1_full :' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma signature_pack_hbz_zero_success_mode2' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'hoare [Pack._encode_hb_z1_full :' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F 'lemma signature_pack_unpack_hbz_zero_success_mode2' \
    "$WEEK15_WITNESS" >> "$LOG_DIR/week15-rans-success-surface-scan.log" || \
   ! rg -F '| OBL-RANS-ACTUAL-SUCCESS-WITNESS | PROVED (fixed all-6 input, Hoare partial correctness) |' \
    "$PROJECT_DIR/CLAIM_LEDGER.md" >> "$LOG_DIR/week15-rans-success-surface-scan.log"; then
  printf 'FAIL Week15 fixed all-six actual success-witness surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
awk '
  /lemma actual_rans_encode_all_six_success/ { inside = 1 }
  inside { print }
  inside && /==>/ { exit }
' "$WEEK15_WITNESS" > "$WORK_DIR/week15-core-success-precondition.txt"
awk '
  /lemma actual_encode_hb_z1_full_zero_success/ { inside = 1 }
  inside { print }
  inside && /==>/ { exit }
' "$WEEK15_WITNESS" > "$WORK_DIR/week15-full-success-precondition.txt"
if rg -n \
    'encoder_success|decoder_success|segment_matches|trace_bytes|prepared_hbz_prefix|BArray16.get64[[:space:]]+res|bad[[:space:]]*=|off[[:space:]]*(>=|>)|size[[:space:]]*(<>|>|>=|<=)' \
    "$WORK_DIR/week15-core-success-precondition.txt" \
    "$WORK_DIR/week15-full-success-precondition.txt" \
    >> "$LOG_DIR/week15-rans-success-surface-scan.log"; then
  printf 'FAIL Week15 success theorem assumes success, capacity, or trace evidence\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'phoare|islossless|is_lossless' \
    "$WEEK15_BUDGET" "$WEEK15_CLOSURE" "$WEEK15_WITNESS" \
    >> "$LOG_DIR/week15-rans-success-surface-scan.log"; then
  printf 'FAIL Week15 Hoare witness is mislabeled as a losslessness theorem\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week15 fixed all-six budget, failure exclusion, and production lift\n' \
  | tee -a "$SUMMARY"

WEEK16_CORE="$PROJECT_DIR/easycrypt/refinement/keygen/Mode2KeygenCoreEquation.ec"
WEEK16_NTT_BRIDGE="$PROJECT_DIR/easycrypt/refinement/keygen/Mode2KeygenNttMulBridge.ec"
WEEK16_SNAPSHOT="$PROJECT_DIR/easycrypt/refinement/keygen/Mode2KeygenSnapshotAlgebra.ec"
WEEK16_REUSED="$PROJECT_DIR/manifests/reused-theorems.md"
WEEK16_LEDGER="$PROJECT_DIR/CLAIM_LEDGER.md"
WEEK16_NTT_REPORT="$PROJECT_DIR/WEEK16_KG_NTT_MUL_REPORT.md"
if ! rg -F 'module ActualM23MatrixFinalizeSnapshot' "$WEEK16_CORE" \
    > "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F '(bp, s1hatp) <@ Parent._kp_m23_matrix' "$WEEK16_CORE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F '(bp, s2) <@ Parent._keypair_finalize_m23' "$WEEK16_CORE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'lemma actual_m23_matrix_finalize_snapshot' "$WEEK16_CORE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'op actual_snapshot_mod2q_zero' "$WEEK16_CORE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'lemma finalize_semantic_output_snapshot_mod2q_zero' \
    "$WEEK16_CORE" >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'lemma snapshot_expression_from_product_congruent_mod_2q' \
    "$WEEK16_SNAPSHOT" >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F '| OBL-MINCORE-KEYGEN | PARTIAL — STOP-KG-NTT |' \
    "$WEEK16_LEDGER" >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'lemma output_row_from_mode2_ntt_words' "$WEEK16_NTT_BRIDGE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'lemma output_row_repr_from_mode2_ntt_words' "$WEEK16_NTT_BRIDGE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'lemma actual_m23_matrix_snapshot_rows_explicit' "$WEEK16_NTT_BRIDGE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'Mode2KeygenCoreEquation.ActualM23MatrixFinalizeSnapshot.run' \
    "$WEEK16_NTT_BRIDGE" >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'STOP-KG-NTT' "$WEEK16_NTT_REPORT" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'odd-root orthogonality' "$WEEK16_NTT_REPORT" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log" || \
   ! rg -F 'KG-NTT-MUL continuation and stop boundary' "$WEEK16_REUSED" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log"; then
  printf 'FAIL Week16 direct keygen harness surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'require import.*HAETAE_Algebra|poly_mul|matrix_vec_mul|Agen|sgen|KG-|desired|equation' \
    "$WEEK16_NTT_BRIDGE" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log"; then
  printf 'FAIL Week16 NTT boundary hides the missing security-model product\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
sed -n '/module ActualM23MatrixFinalizeSnapshot = {/,/^}./p' \
  "$WEEK16_CORE" > "$WORK_DIR/week16-keygen-harness-body.txt"
if rg -n 'CheckedMode2Parent|Sampler|retry|pack|cryptolab_|_keypair_full_m23|Api|public' \
    "$WORK_DIR/week16-keygen-harness-body.txt" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log"; then
  printf 'FAIL Week16 harness pulls sampler, retry, packer, or public-API machinery\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
awk '
  /lemma actual_m23_matrix_finalize_snapshot/ { inside = 1 }
  inside { print }
  inside && /==>/ { exit }
' "$WEEK16_CORE" > "$WORK_DIR/week16-keygen-precondition.txt"
if rg -n 'KG-|desired|equation|finalize_semantic_output|finalize_haetae_semantic_output|accepted|success' \
    "$WORK_DIR/week16-keygen-precondition.txt" \
    >> "$LOG_DIR/week16-keygen-core-surface-scan.log"; then
  printf 'FAIL Week16 direct Hoare precondition assumes target equations or success facts\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week16 direct-keygen harness and STOP-KG-NTT boundary checks\n' \
  | tee -a "$SUMMARY"

WEEK16_SIGN="$PROJECT_DIR/easycrypt/refinement/sign/Mode2SignAcceptedCore.ec"
WEEK16_SIGN_REPORT="$PROJECT_DIR/WEEK16_SIGN_REPORT.md"
if ! rg -F 'module ActualSignAcceptedCore = {' "$WEEK16_SIGN" \
    > "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'Sign._sf_round_challenge_mode2' "$WEEK16_SIGN" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'Sign._sf_z_check' "$WEEK16_SIGN" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'Sign._sf_hint_mode2' "$WEEK16_SIGN" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'if (zcheck_reject = W64.zero)' "$WEEK16_SIGN" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'lemma actual_sign_accepted_core_branch_control_mode2' \
    "$WEEK16_SIGN" >> "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'STOP-SIGN-CHAL-MODE2' "$WEEK16_SIGN_REPORT" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log" || \
   ! rg -F 'sf_challenge_mode2_highbits_lsb_sampleinball_correct' \
    "$WEEK16_SIGN_REPORT" >> "$LOG_DIR/week16-sign-core-surface-scan.log"; then
  printf 'FAIL Week16 direct Sign-core/STOP boundary surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
sed -n '/module ActualSignAcceptedCore = {/,/^}./p' \
  "$WEEK16_SIGN" > "$WORK_DIR/week16-sign-harness-body.txt"
if rg -n 'RawSignApiTarget|cryptolab_|_sf_signature_core|_sf_hyperball|_sf_pack|public[ -]API' \
    "$WORK_DIR/week16-sign-harness-body.txt" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log"; then
  printf 'FAIL Week16 Sign harness pulls sampler, retry, packer, or public API\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
awk '
  /lemma actual_sign_accepted_core_branch_control_mode2/ { inside = 1 }
  inside { print }
  inside && /==>/ { exit }
' "$WEEK16_SIGN" > "$WORK_DIR/week16-sign-precondition.txt"
if rg -n 'reject[[:space:]]*=[[:space:]]*W64.zero|S-[1-7]|SampleInBall|HighBits|norm|hint_hp[[:space:]]*=' \
    "$WORK_DIR/week16-sign-precondition.txt" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log"; then
  printf 'FAIL Week16 Sign theorem precondition assumes acceptance or target equations\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -F 'lemma actual_sign_accepted_core_equations_mode2' "$WEEK16_SIGN" \
    >> "$LOG_DIR/week16-sign-core-surface-scan.log"; then
  printf 'FAIL stopped Week16 Sign boundary claims unproved S-1--S-7 theorem\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week16 direct Sign-core control and STOP-SIGN-CHAL-MODE2 checks\n' \
  | tee -a "$SUMMARY"

WEEK16_VERIFY_DIR="$PROJECT_DIR/easycrypt/refinement/verify"
WEEK16_VERIFY_SEQUENCE="$WEEK16_VERIFY_DIR/Mode2VerifyCoreSequence.ec"
WEEK16_VERIFY_PREPARE="$WEEK16_VERIFY_DIR/Mode2VerifyPrepareNorm.ec"
WEEK16_VERIFY_RECOVER="$WEEK16_VERIFY_DIR/Mode2VerifyRecover.ec"
WEEK16_VERIFY_TAIL="$WEEK16_VERIFY_DIR/Mode2VerifyTailChallenge.ec"
WEEK16_VERIFY_REPORT="$PROJECT_DIR/WEEK16_VERIFY_REPORT.md"
WEEK16_VERIFY_EXTRACT="$SCRIPT_DIR/extract-verify-core.sh"
if ! rg -F 'module ActualVerifyCoreSequence = {' "$WEEK16_VERIFY_SEQUENCE" \
    > "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma actual_verify_core_sequence_branch_control_mode2' \
    "$WEEK16_VERIFY_SEQUENCE" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma actual_verify_core_sequence_input_snapshots_mode2' \
    "$WEEK16_VERIFY_SEQUENCE" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma verify_prepare_z1_mode2_word_exact' \
    "$WEEK16_VERIFY_PREPARE" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma verify_prepare_wprime_mode2_word_exact' \
    "$WEEK16_VERIFY_PREPARE" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma sign_verify_norm_reject_mode2_word_exact' \
    "$WEEK16_VERIFY_PREPARE" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma actual_sign_verify_recover_w_mode2_word_semantics' \
    "$WEEK16_VERIFY_RECOVER" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma actual_sign_verify_recover_z2_mode2_word_semantics' \
    "$WEEK16_VERIFY_RECOVER" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma poly_mismatch_mode2_word_exact' \
    "$WEEK16_VERIFY_TAIL" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'lemma verify_tail_exact_trace_mode2' \
    "$WEEK16_VERIFY_TAIL" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'STOP-VERIFY-MATRIX-CRT' "$WEEK16_VERIFY_REPORT" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'verify_matrix_crt_mode2_fromcrt_freeze_exact' \
    "$WEEK16_VERIFY_REPORT" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'verify_matrix_ntt_acc_mode2_cols4_correct' \
    "$WEEK16_VERIFY_REPORT" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'rq_mul_coeff_foldr_to_bigi' \
    "$WEEK16_VERIFY_REPORT" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'full_ntt_montgomery_spectral_action' \
    "$WEEK16_VERIFY_REPORT" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'verify_crt_freeze_mode2_word_exact' \
    "$WEEK16_VERIFY_REPORT" >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F 'verify_tail_m23_highbits_lsb_sampleinball_correct' \
    "$WEEK16_VERIFY_REPORT" >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL Week16 direct Verify-core/STOP boundary surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi

sed -n '/module ActualVerifyCoreSequence = {/,/^}./p' \
  "$WEEK16_VERIFY_SEQUENCE" > "$WORK_DIR/week16-verify-harness-body.txt"
if ! awk '
  /Verify[.]_verify_prepare_z1_wprime/ {
    prepare++; if (state != 0) bad = 1; state = 1
  }
  /Verify[.]_verify_matrix_crt/ {
    matrix++; if (state != 1) bad = 1; state = 2
  }
  /Verify[.]_sign_verify_recover_w_z2/ {
    recover++; if (state != 2) bad = 1; state = 3
  }
  /Verify[.]_sign_verify_norm_reject/ {
    norm++; if (state != 3) bad = 1; state = 4
  }
  /Verify[.]_sign_verify_tail_m23/ {
    tail++; if (state != 4) bad = 1; state = 5
  }
  END {
    if (bad || state != 5 || prepare != 1 || matrix != 1 || recover != 1 ||
        norm != 1 || tail != 1) exit 1
  }
' "$WORK_DIR/week16-verify-harness-body.txt"; then
  printf 'FAIL Week16 Verify helpers are not called exactly once in order\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if ! rg -F 'if (reject = W64.zero)' \
    "$WORK_DIR/week16-verify-harness-body.txt" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL Week16 Verify tail is not guarded by the actual norm result\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'cryptolab_|_unpack|_decode|_encode|_keypair|_sf_|Raw[A-Za-z]*Api|PublicApi' \
    "$WORK_DIR/week16-verify-harness-body.txt" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL Week16 Verify harness widens into codec, API, KeyGen, or Sign\n' \
    | tee -a "$SUMMARY"
  exit 1
fi

: > "$WORK_DIR/week16-verify-preconditions.txt"
for theorem in \
    actual_verify_core_sequence_branch_control_mode2 \
    verify_prepare_z1_mode2_word_exact \
    verify_prepare_wprime_mode2_word_exact \
    sign_verify_norm_reject_mode2_word_exact \
    actual_sign_verify_recover_w_mode2_word_semantics \
    actual_sign_verify_recover_z2_mode2_word_semantics \
    poly_mismatch_mode2_word_exact; do
  case "$theorem" in
    actual_verify_core_sequence_branch_control_mode2)
      theorem_file="$WEEK16_VERIFY_SEQUENCE"
      ;;
    verify_prepare_z1_mode2_word_exact|verify_prepare_wprime_mode2_word_exact|sign_verify_norm_reject_mode2_word_exact)
      theorem_file="$WEEK16_VERIFY_PREPARE"
      ;;
    actual_sign_verify_recover_w_mode2_word_semantics|actual_sign_verify_recover_z2_mode2_word_semantics)
      theorem_file="$WEEK16_VERIFY_RECOVER"
      ;;
    poly_mismatch_mode2_word_exact)
      theorem_file="$WEEK16_VERIFY_TAIL"
      ;;
  esac
  awk -v theorem="$theorem" '
    $0 ~ "lemma " theorem { found = 1 }
    found && /hoare \[/ { inside = 1 }
    inside { print }
    inside && /==>/ { exit }
  ' "$theorem_file" >> "$WORK_DIR/week16-verify-preconditions.txt"
done
if rg -n \
    'reject[[:space:]]*=[[:space:]]*W64[.]zero|res[[:space:]]*=|verify_norm_accepts_word|matrix_highbits[[:space:]]*=|recover_[wz2]+_prefix[[:space:]]+res|SampleInBall|challenge[_ -]?equality' \
    "$WORK_DIR/week16-verify-preconditions.txt" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL Week16 Verify theorem assumes rejection, reconstruction, norm, or challenge result\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n 'phoare|islossless|is_lossless' \
    "$WEEK16_VERIFY_SEQUENCE" "$WEEK16_VERIFY_PREPARE" \
    "$WEEK16_VERIFY_RECOVER" "$WEEK16_VERIFY_TAIL" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL Week16 Verify partial-correctness result claims termination\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if [ "$(rg -c '^[[:space:]]*-f ' "$WEEK16_VERIFY_EXTRACT")" -ne 5 ] || \
   ! rg -F -- '-f _verify_prepare_z1_wprime' "$WEEK16_VERIFY_EXTRACT" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F -- '-f _verify_matrix_crt' "$WEEK16_VERIFY_EXTRACT" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F -- '-f _sign_verify_recover_w_z2' "$WEEK16_VERIFY_EXTRACT" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F -- '-f _sign_verify_norm_reject' "$WEEK16_VERIFY_EXTRACT" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log" || \
   ! rg -F -- '-f _sign_verify_tail_m23' "$WEEK16_VERIFY_EXTRACT" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL Week16 Verify focused extraction roots drifted\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
if rg -n \
    'lemma (actual_verify_core_predicate_mode2|verify_matrix_crt_mode2_fromcrt_freeze_exact|verify_matrix_ntt_acc_mode2_cols4_correct|verify_crt_freeze_mode2_word_exact)' \
    "$WEEK16_VERIFY_DIR" \
    >> "$LOG_DIR/week16-verify-core-surface-scan.log"; then
  printf 'FAIL stopped Week16 Verify boundary claims an unproved matrix or full predicate theorem\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS Week16 direct Verify-core word results and STOP-VERIFY-MATRIX-CRT checks\n' \
  | tee -a "$SUMMARY"

API_BRIDGE="$PROJECT_DIR/easycrypt/refinement/composition/ApiKeyMemoryBridge.ec"
if ! rg -F 'lemma keygen_export_vk_mode2_prefix' "$API_BRIDGE" \
    > "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'lemma keygen_export_sk_mode2_prefix' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'lemma sign_import_mode2_sk_prefix' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'lemma verify_import_mode2_vk_prefix' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'lemma imported_sign_sk_reaches_mu_memory' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'lemma keygen_export_sk_mode2_prefix_frames_vk' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'lemma mode2_api_region_contract_satisfiable' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'op valid_region_int' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log" || \
   ! rg -F 'op disjoint_regions' "$API_BRIDGE" \
    >> "$LOG_DIR/api-memory-reachability-scan.log"; then
  printf 'FAIL actual API copy-helper reachability surface\n' \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS actual API copy-helper reachability source checks\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR/extract" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-transcripts.sh" \
  > "$LOG_DIR/focused-extraction-transcripts.log" 2>&1
printf 'PASS focused transcript extraction\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR/mu-hash-extract" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-mu-hash.sh" \
  > "$LOG_DIR/focused-extraction-mu-hash.log" 2>&1
printf 'PASS focused mu-hash extraction\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR/packer-extract" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-packers.sh" \
  > "$LOG_DIR/focused-extraction-packers.log" 2>&1
printf 'PASS focused packer extraction\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-signature-codec.sh" \
  > "$LOG_DIR/focused-extraction-signature-codec.log" 2>&1
printf 'PASS focused signature codec extraction\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-hbz-codec.sh" \
  > "$LOG_DIR/focused-extraction-hbz-codec.log" 2>&1
printf 'PASS focused HBZ/rANS extraction\n' \
  | tee -a "$SUMMARY"

"$SCRIPT_DIR/generate-hbz-symbol-certificate.sh" \
  "$WORK_DIR/Mode2HbzSymbolWordsGenerated.ec"
if ! cmp -s "$WORK_DIR/Mode2HbzSymbolWordsGenerated.ec" \
    "$PROJECT_DIR/easycrypt/refinement/sign/Mode2HbzSymbolWordsGenerated.ec"; then
  printf 'FAIL generated HBZ symbol certificate drift\n' | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS deterministic HBZ symbol certificate regeneration\n' \
  | tee -a "$SUMMARY"

(cd "$PROJECT_DIR" && \
  sha256sum -c manifests/generated-certificates.sha256) \
  > "$LOG_DIR/generated-certificate-hash.log" 2>&1
printf 'PASS generated HBZ certificate hashes\n' \
  | tee -a "$SUMMARY"

extract_generated_proc() {
  source_file=$1
  proc_name=$2
  output_file=$3
  awk -v proc_name="$proc_name" '
    $0 ~ "^  proc " proc_name "[ (]" { inside = 1 }
    inside {
      if (seen && $0 ~ "^  proc ") exit
      print
      seen = 1
    }
  ' "$source_file" > "$output_file"
  [ -s "$output_file" ]
}

compare_generated_proc() {
  left_file=$1
  right_file=$2
  proc_name=$3
  label=$4
  left_proc="$WORK_DIR/$label.focused.ec"
  right_proc="$WORK_DIR/$label.signature.ec"
  extract_generated_proc "$left_file" "$proc_name" "$left_proc"
  extract_generated_proc "$right_file" "$proc_name" "$right_proc"
  if ! cmp -s "$left_proc" "$right_proc"; then
    printf 'FAIL generated procedure drift: %s\n' "$proc_name" \
      | tee -a "$SUMMARY"
    exit 1
  fi
  sha256sum "$left_proc" >> "$LOG_DIR/hbz-procedure-identity.log"
}

: > "$LOG_DIR/hbz-procedure-identity.log"
compare_generated_proc \
  "$WORK_DIR/hbz-codec/HbzFullEncodeTarget.ec" \
  "$WORK_DIR/pack/SignaturePackMode2Target.ec" \
  _rans_encode hbz-rans-encode
compare_generated_proc \
  "$WORK_DIR/hbz-codec/HbzFullEncodeTarget.ec" \
  "$WORK_DIR/pack/SignaturePackMode2Target.ec" \
  _encode_hb_z1_prepare hbz-prepare
compare_generated_proc \
  "$WORK_DIR/hbz-codec/HbzFullEncodeTarget.ec" \
  "$WORK_DIR/pack/SignaturePackMode2Target.ec" \
  _encode_hb_z1_full hbz-full-encode
compare_generated_proc \
  "$WORK_DIR/hbz-codec/HbzFullDecodeTarget.ec" \
  "$WORK_DIR/unpack/SignatureUnpackMode2Target.ec" \
  _rans_decode hbz-rans-decode
compare_generated_proc \
  "$WORK_DIR/hbz-codec/HbzFullDecodeTarget.ec" \
  "$WORK_DIR/unpack/SignatureUnpackMode2Target.ec" \
  _decode_hb_z1_apply hbz-apply
compare_generated_proc \
  "$WORK_DIR/hbz-codec/HbzFullDecodeTarget.ec" \
  "$WORK_DIR/unpack/SignatureUnpackMode2Target.ec" \
  _decode_hb_z1_full hbz-full-decode
printf 'PASS focused/signature HBZ generated procedure identity\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR/api-key-extract" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-api-key-memory.sh" \
  > "$LOG_DIR/focused-extraction-api-key-memory.log" 2>&1
printf 'PASS focused API key-memory extraction\n' \
  | tee -a "$SUMMARY"
TOPDOWN_EXTRACT_DIR="$WORK_DIR/raw-api-extract" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-raw-api-callers.sh" \
  > "$LOG_DIR/focused-extraction-raw-api-callers.log" 2>&1
printf 'PASS focused raw API caller extraction\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-sign-accepted-core.sh" \
  > "$LOG_DIR/focused-extraction-sign-accepted-core.log" 2>&1
printf 'PASS focused Sign accepted-core extraction\n' \
  | tee -a "$SUMMARY"

TOPDOWN_EXTRACT_DIR="$WORK_DIR" \
WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
  "$SCRIPT_DIR/extract-verify-core.sh" \
  > "$LOG_DIR/focused-extraction-verify-core.log" 2>&1
printf 'PASS focused Verify core extraction\n' \
  | tee -a "$SUMMARY"

(cd "$WORK_DIR" && sha256sum -c "$EXTRACTION_HASHES") \
  > "$LOG_DIR/focused-extraction-drift.log" 2>&1
printf 'PASS focused extraction regeneration drift\n' \
  | tee -a "$SUMMARY"

SIGN_EXTRACT="$WORK_DIR/extract/sign"
VERIFY_EXTRACT="$WORK_DIR/extract/verify"
MU_SIGN_EXTRACT="$WORK_DIR/mu-hash-extract/sign"
MU_VERIFY_EXTRACT="$WORK_DIR/mu-hash-extract/verify"
API_KEYGEN_EXTRACT="$WORK_DIR/api-key-extract/keygen"
API_SIGN_EXTRACT="$WORK_DIR/api-key-extract/sign"
API_VERIFY_EXTRACT="$WORK_DIR/api-key-extract/verify"
RAW_KEYGEN_EXTRACT="$WORK_DIR/raw-api-extract/keygen"
RAW_SIGN_EXTRACT="$WORK_DIR/raw-api-extract/sign"
RAW_VERIFY_EXTRACT="$WORK_DIR/raw-api-extract/verify"
SIG_PACK_EXTRACT="$WORK_DIR/pack"
SIG_UNPACK_EXTRACT="$WORK_DIR/unpack"
HBZ_EXTRACT="$WORK_DIR/hbz-codec"
SIGN_CORE_EXTRACT="$WORK_DIR/sign-accepted-core"
VERIFY_CORE_EXTRACT="$WORK_DIR/verify-core"
PARENT_EXTRACT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/extract/keygen-mode2-parent"
CALLER_EXTRACT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/extract/keygen-sampler-callers"
NTT_EXTRACT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/extract/ntt"
OLD_SPEC="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/spec"
OLD_REFINEMENT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/refinement"
OLD_SUPPORT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/support"
SECURITY="$ROOT_DIR/haetae-security/provable-security/easycrypt"
ROOT_SECURITY="$ROOT_DIR/haetae-security"
NTT_SUPPORT="$ROOT_DIR/haetae-ntt-verify/easycrypt-ct"

compiled=0
while IFS= read -r target || [ -n "$target" ]; do
  [ -n "$target" ] || continue
  file="$PROJECT_DIR/$target"
  name=$(basename "$target" .ec)
  log="$LOG_DIR/compile-$name.log"
  case "$name" in
    ExtractedChallengeAbsorb)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$SIGN_EXTRACT" -I "$VERIFY_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    PackedKeyPrefix)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$PARENT_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    ExtractedPackedKeyPrefix)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$PARENT_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    Mode2SignaturePrefixCodec|Mode2SignaturePrefixPack|Mode2SignaturePrefixUnpack|Mode2SignaturePrefixRoundTrip)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$SIG_PACK_EXTRACT" -I "$SIG_UNPACK_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/sign" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    Mode2RansDecoderCursor|Mode2RansDecoderWordStep|Mode2RansDecoderNormalization|Mode2RansDecoderActualWord|Mode2RansDecoderGeneratedStep|Mode2RansDecoderCursorSteps|Mode2RansDecoderActualTrace|Mode2RansDecoderTopHoare|Mode2RansCoreCompositionBridge|Mode2RansCoreActualInverse|Mode2RansEncoderActualTraceClosure|Mode2RansAllSixBudget|Mode2HbzInternalBoundaries|Mode2HbzFullEncodeTrace|Mode2HbzFullDecodeInverse|Mode2HbzFullActualInverse|Mode2HbzSignatureBoundaryLift|Mode2RansActualSuccessWitness)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 10 "$file" \
        -I "$HBZ_EXTRACT" -I "$SIG_PACK_EXTRACT" \
        -I "$SIG_UNPACK_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/sign" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    Mode2SignAcceptedCore)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$SIGN_CORE_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/sign" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    Mode2VerifyCoreSequence|Mode2VerifyPrepareNorm|Mode2VerifyRecover|Mode2VerifyTailChallenge)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$VERIFY_CORE_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/verify" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    Mode2HbzCodecSpec|Mode2HbzPrepare|Mode2HbzApply|Mode2HbzLeafRoundTrip|Mode2HbzTableCertificate|Mode2HbzSymbolWordsGenerated|Mode2RansCore|Mode2HbzActualBoundary|Mode2RansByteStack|Mode2RansNormalization|Mode2RansSuffixCopy|Mode2RansEncodeRefinement|Mode2RansDecodeRefinement|Mode2RansActualInverse|Mode2RansArrayListBridge|Mode2RansEncoderWordStep|Mode2RansEncoderGeneratedWordStep|Mode2RansEncoderInnerProgress|Mode2RansEncoderSerialization|Mode2RansEncoderSerializationComposition|Mode2RansEncoderTrace|Mode2RansEncoderActualInner|Mode2RansEncoderTailInvariant|Mode2RansEncoderFinalization|Mode2RansEncoderGeneratedFinalization|Mode2RansEncoderOuterRefinement)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$HBZ_EXTRACT" -I "$SIG_PACK_EXTRACT" \
        -I "$SIG_UNPACK_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/sign" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    ExistingFirstAttemptAdapter|Mode2KeygenSnapshotAlgebra|Mode2KeygenNttMulBridge|Mode2KeygenCoreEquation)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$PARENT_EXTRACT" -I "$CALLER_EXTRACT" -I "$NTT_EXTRACT" \
        -I "$OLD_SPEC" -I "$OLD_REFINEMENT" -I "$SECURITY" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -I "$NTT_SUPPORT" -I "$OLD_SUPPORT" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    ExtractedMuHashPrefix)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$MU_SIGN_EXTRACT" -I "$MU_VERIFY_EXTRACT" \
        -I "$PARENT_EXTRACT" -I "$OLD_SPEC" -I "$ROOT_SECURITY" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    ExactMuTopControl)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$MU_SIGN_EXTRACT" -I "$MU_VERIFY_EXTRACT" \
        -I "$PARENT_EXTRACT" -I "$OLD_SPEC" -I "$ROOT_SECURITY" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    ExactMode2RawMuComposition|Mode2MuChallengeComposition)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$SIGN_EXTRACT" -I "$VERIFY_EXTRACT" \
        -I "$MU_SIGN_EXTRACT" -I "$MU_VERIFY_EXTRACT" \
        -I "$PARENT_EXTRACT" -I "$OLD_SPEC" -I "$ROOT_SECURITY" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -I "$PROJECT_DIR/easycrypt/support" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    ApiKeyMemoryBridge)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$API_KEYGEN_EXTRACT" \
        -I "$API_SIGN_EXTRACT" -I "$API_VERIFY_EXTRACT" \
        -I "$MU_SIGN_EXTRACT" -I "$MU_VERIFY_EXTRACT" \
        -I "$PARENT_EXTRACT" -I "$OLD_SPEC" -I "$ROOT_SECURITY" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    RawApiAddressBridge|RawApiAcceptedMuComposition|RawApiKeygenExportComposition|RawApiKeygenSequentialExport|RawApiCallerMuTrace|RawApiVerifyMuTrace|RawApiVerifyAcceptTrace|RawApiMuReachability|RawApiSignOutputFrame|RawApiDirectObservedMu|RegionLocalMuEquivalence|RegionLocalMuTop)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$RAW_KEYGEN_EXTRACT" -I "$RAW_SIGN_EXTRACT" \
        -I "$RAW_VERIFY_EXTRACT" \
        -I "$API_KEYGEN_EXTRACT" -I "$API_SIGN_EXTRACT" \
        -I "$API_VERIFY_EXTRACT" \
        -I "$MU_SIGN_EXTRACT" -I "$MU_VERIFY_EXTRACT" \
        -I "$SIGN_EXTRACT" -I "$VERIFY_EXTRACT" \
        -I "$PARENT_EXTRACT" -I "$OLD_SPEC" -I "$OLD_REFINEMENT" \
        -I "$OLD_SUPPORT" -I "$ROOT_SECURITY" -I "$SECURITY" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -I "$PROJECT_DIR/easycrypt/support" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    TranscriptBytes)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$PROJECT_DIR/easycrypt/refinement/composition" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    Mode2KeyMemoryBridge)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 "$file" \
        -I "$PARENT_EXTRACT" \
        -I "$PROJECT_DIR/easycrypt/refinement/keygen" \
        -I "$PROJECT_DIR/easycrypt/support" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        < /dev/null > "$log" 2>&1
      ;;
    *)
      "$EASYCRYPT_BIN" compile -script -no-eco -timeout 5 \
        -I "$PROJECT_DIR/easycrypt/specs" \
        -I "$PROJECT_DIR/easycrypt/security" \
        -server "$SERVER_SOCKET" -max-provers 1 \
        "$file" \
        < /dev/null > "$log" 2>&1
      ;;
  esac
  compiled=$((compiled + 1))
  printf 'PASS fresh compile %s\n' "$target" | tee -a "$SUMMARY"
done < "$MANIFEST"

"$SCRIPT_DIR/verify-baselines.sh" > "$LOG_DIR/baseline-verification.log" 2>&1
printf 'PASS baseline verification\n' | tee -a "$SUMMARY"

sh "$SCRIPT_DIR/build-notes.sh" > "$LOG_DIR/latex-build.log" 2>&1
printf 'PASS LaTeX research notes build\n' | tee -a "$SUMMARY"

"$SCRIPT_DIR/check-source-drift.sh" \
  > "$LOG_DIR/source-drift-after.log" 2>&1
printf 'PASS read-only roots unchanged after verification\n' | tee -a "$SUMMARY"

PAPER_AUDIT_SUMMARY="$WORK_DIR/paper-freeze-summary.txt"
cp "$SUMMARY" "$PAPER_AUDIT_SUMMARY"
printf 'RESULT PASS authored-targets=%s cache=-no-eco\n' "$compiled" \
  >> "$PAPER_AUDIT_SUMMARY"
PAPER_FREEZE_SUMMARY="$PAPER_AUDIT_SUMMARY" \
  "$SCRIPT_DIR/check-paper-freeze.sh" \
  > "$LOG_DIR/paper-freeze-audit.log" 2>&1
printf 'PASS paper-freeze scope and 82-target evidence audit\n' \
  | tee -a "$SUMMARY"
printf 'RESULT PASS authored-targets=%s cache=-no-eco\n' "$compiled" \
  | tee -a "$SUMMARY"
