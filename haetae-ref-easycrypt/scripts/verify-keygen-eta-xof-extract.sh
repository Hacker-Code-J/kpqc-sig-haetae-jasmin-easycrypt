#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
EXTRACT_DIR="$PROJECT_DIR/easycrypt/extract/keygen-eta-xof"
FILE_MANIFEST="$PROJECT_DIR/manifests/keygen-eta-xof-extract-files.txt"
PROCEDURE_MANIFEST="$PROJECT_DIR/manifests/keygen-eta-xof-procedures.txt"
LOG_DIR="$PROJECT_DIR/logs/keygen-eta-xof-extract"
SUMMARY="$PROJECT_DIR/logs/keygen-eta-xof-extract-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}

mkdir -p "$LOG_DIR"

SOURCE_CHECK_LOG="$LOG_DIR/source-hash-check.log"
if "$SCRIPT_DIR/check-sources.sh" > "$SOURCE_CHECK_LOG" 2>&1; then
  source_count=$(wc -l < "$SOURCE_CHECK_LOG" | tr -d ' ')
else
  status=$?
  printf 'FAIL canonical source hash check exit=%s log=%s\n' \
    "$status" "$SOURCE_CHECK_LOG"
  cat "$SOURCE_CHECK_LOG"
  exit "$status"
fi

{
  printf 'HAETAE mode-2 key-generation eta XOF leaf extraction verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Source: ../haetae-ref-jasmin/jasmin/keypair.jazz\n'
  printf 'Selected function: _kp_poly_uniform_eta_at_seedbuf_2048\n'
  printf 'Extraction model: barray\n'
  printf 'Generated file manifest: manifests/keygen-eta-xof-extract-files.txt\n'
  printf 'Procedure closure manifest: manifests/keygen-eta-xof-procedures.txt\n'
  printf 'Toolchain: manifests/toolchain.md\n\n'
  printf 'PASS canonical source hash check (%s pinned inputs)\n' "$source_count"
  printf 'Pinned source and parsed-dependency SHA-256 values:\n'
  (cd "$PROJECT_DIR" && sha256sum \
    ../haetae-ref-jasmin/jasmin/keypair.jazz \
    ../haetae-ref-jasmin/jasmin/params.jinc \
    ../haetae-ref-jasmin/jasmin/keccak.jinc \
    ../haetae-ref-jasmin/jasmin/polynomial_sampler.jinc \
    ../haetae-ref-jasmin/jasmin/expand.jinc \
    ../haetae-ref-jasmin/jasmin/poly.jinc \
    ../haetae-ref-jasmin/jasmin/pack.jinc \
    ../haetae-ref-jasmin/jasmin/sign.jinc \
    ../haetae-ref-jasmin/jasmin/fft.jinc \
    ../haetae-ref-jasmin/jasmin/fft_pipeline.jinc \
    ../haetae-ref-jasmin/jasmin/fft_tables.jinc \
    ../haetae-ref-jasmin/jasmin/singular_values.jinc \
    ../haetae-ref-jasmin/jasmin/api.jinc \
    ../haetae-ref-jasmin/jasmin/reduce.jinc \
    ../haetae-ref-jasmin/jasmin/zetas.jinc)
  printf '\n'
} > "$SUMMARY"

"$SCRIPT_DIR/check-keygen-eta-xof-extract-drift.sh" | tee -a "$SUMMARY"

passed=0
total=0
while IFS= read -r file || [ -n "$file" ]; do
  total=$((total + 1))
  log="$LOG_DIR/${file%.ec}.log"
  if "$EASYCRYPT_BIN" compile -no-eco "$EXTRACT_DIR/$file" \
      -I "$EXTRACT_DIR" < /dev/null > "$log" 2>&1; then
    passed=$((passed + 1))
    printf 'PASS compile %s\n' "$file" | tee -a "$SUMMARY"
  else
    status=$?
    printf 'FAIL compile %s exit=%s log=%s\n' "$file" "$status" "$log" \
      | tee -a "$SUMMARY"
    tail -n 80 "$log"
    exit "$status"
  fi
done < "$FILE_MANIFEST"

HOLE_LOG="$LOG_DIR/proof-hole-scan.log"
hole_status=0
rg -n '(^|[^[:alnum:]_])(admit|abort)([^[:alnum:]_]|$)' \
  "$EXTRACT_DIR" --glob '*.ec' > "$HOLE_LOG" || hole_status=$?
case "$hole_status" in
  0)
    printf 'FAIL proof-hole scan log=%s\n' "$HOLE_LOG" | tee -a "$SUMMARY"
    cat "$HOLE_LOG"
    exit 1
    ;;
  1)
    printf 'PASS proof-hole scan (no admit/abort proof commands)\n' \
      | tee -a "$SUMMARY"
    ;;
  *)
    printf 'FAIL proof-hole scan exit=%s log=%s\n' \
      "$hole_status" "$HOLE_LOG" | tee -a "$SUMMARY"
    exit "$hole_status"
    ;;
esac

AXIOM_LOG="$LOG_DIR/axiom-declaration-scan.log"
axiom_status=0
rg -n '^[[:space:]]*axiom[[:space:]]' \
  "$EXTRACT_DIR" --glob '*.ec' > "$AXIOM_LOG" || axiom_status=$?
case "$axiom_status" in
  0)
    printf 'FAIL axiom declaration scan log=%s\n' "$AXIOM_LOG" \
      | tee -a "$SUMMARY"
    cat "$AXIOM_LOG"
    exit 1
    ;;
  1)
    printf 'PASS axiom declaration scan (none found)\n' | tee -a "$SUMMARY"
    ;;
  *)
    printf 'FAIL axiom declaration scan exit=%s log=%s\n' \
      "$axiom_status" "$AXIOM_LOG" | tee -a "$SUMMARY"
    exit "$axiom_status"
    ;;
esac

sha256sum "$EXTRACT_DIR/KeygenEtaXofTarget.ec" >> "$SUMMARY"
printf 'RESULT: PASS compiled=%s total=%s procedures=%s mode=-no-eco\n' \
  "$passed" "$total" \
  "$(wc -l < "$PROCEDURE_MANIFEST" | tr -d ' ')" | tee -a "$SUMMARY"
