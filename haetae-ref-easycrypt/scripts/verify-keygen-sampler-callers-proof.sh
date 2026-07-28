#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
EASYCRYPT_DIR="$PROJECT_DIR/easycrypt"
EXTRACT_DIR="$EASYCRYPT_DIR/extract/keygen-sampler-callers"
SPEC_DIR="$EASYCRYPT_DIR/spec"
REFINEMENT_DIR="$EASYCRYPT_DIR/refinement"
SECURITY_DIR="$PROJECT_DIR/../haetae-security/provable-security/easycrypt"
FILE_MANIFEST="$PROJECT_DIR/manifests/keygen-sampler-callers-proof-files.txt"
LOG_DIR="$PROJECT_DIR/logs/keygen-sampler-callers-proof"
SUMMARY="$PROJECT_DIR/logs/keygen-sampler-callers-proof-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
WHY3_BIN=${WHY3:-why3}
WHY3SERVER_BIN=${WHY3SERVER:-"$($WHY3_BIN --print-libdir)/why3server"}
MAX_PROVERS=${EC_MAX_PROVERS:-1}

mkdir -p "$LOG_DIR"

LOCK_DIR="$LOG_DIR/.verify.lock"
if ! mkdir "$LOCK_DIR" 2>/dev/null; then
  printf 'FAIL another sampler-caller proof verification is active lock=%s\n' \
    "$LOCK_DIR"
  exit 75
fi

SERVER_DIR=$(mktemp -d)
SERVER_SOCKET="$SERVER_DIR/why3server.socket"
SERVER_LOG="$LOG_DIR/why3server.log"
SERVER_PID=

cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  rm -rf "$SERVER_DIR"
  rmdir "$LOCK_DIR" 2>/dev/null || true
}
trap cleanup EXIT HUP INT TERM

if [ ! -x "$WHY3SERVER_BIN" ]; then
  printf 'FAIL missing Why3 server executable: %s\n' "$WHY3SERVER_BIN"
  exit 2
fi

"$WHY3SERVER_BIN" --socket "$SERVER_SOCKET" -j "$MAX_PROVERS" \
  > "$SERVER_LOG" 2>&1 &
SERVER_PID=$!
server_wait=0
while [ ! -S "$SERVER_SOCKET" ] && [ "$server_wait" -lt 50 ]; do
  sleep 0.1
  server_wait=$((server_wait + 1))
done
if [ ! -S "$SERVER_SOCKET" ]; then
  printf 'FAIL Why3 server startup log=%s\n' "$SERVER_LOG"
  tail -n 80 "$SERVER_LOG"
  exit 1
fi

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

DRIFT_LOG="$LOG_DIR/extraction-drift.log"
if "$SCRIPT_DIR/check-keygen-sampler-callers-extract-drift.sh" \
    > "$DRIFT_LOG" 2>&1; then
  :
else
  status=$?
  printf 'FAIL extraction drift check exit=%s log=%s\n' \
    "$status" "$DRIFT_LOG"
  tail -n 80 "$DRIFT_LOG"
  exit "$status"
fi

{
  printf 'HAETAE key-generation sampler consumer and caller proof verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Command: ./scripts/verify-keygen-sampler-callers-proof.sh\n'
  printf 'Generated target: easycrypt/extract/keygen-sampler-callers/KeygenSamplerCallersTarget.ec\n'
  printf 'Authored specifications: easycrypt/spec/KeygenSamplerCallersSpec.ec; easycrypt/spec/KeygenUniformXofLeafSpec.ec; easycrypt/spec/KeygenEtaSamplerSpec.ec; easycrypt/spec/KeygenKeccak1600Spec.ec; easycrypt/spec/KeygenShakeStreamSpec.ec; easycrypt/spec/KeygenSeedXofSpec.ec\n'
  printf 'Authored refinements: easycrypt/refinement/TargetKeygenSamplerCallers.ec; easycrypt/refinement/TargetKeygenUniformXofLeaf.ec; easycrypt/refinement/TargetKeygenEtaSampler.ec; easycrypt/refinement/TargetKeygenKeccak1600.ec; easycrypt/refinement/TargetKeygenShakeStream.ec; easycrypt/refinement/TargetKeygenSeedXof.ec\n'
  printf 'Proof manifest: manifests/keygen-sampler-callers-proof-files.txt\n'
  printf 'Source manifest: manifests/sources.sha256\n'
  printf 'Toolchain: manifests/toolchain.md\n\n'
  printf 'PASS canonical source hash check (%s pinned inputs)\n' "$source_count"
  cat "$DRIFT_LOG"
} > "$SUMMARY"

printf 'PASS dedicated Why3 server startup max-provers=%s\n' "$MAX_PROVERS" \
  | tee -a "$SUMMARY"

passed=0
total=0
while IFS= read -r file || [ -n "$file" ]; do
  total=$((total + 1))
  name=$(basename "$file" .ec)
  log="$LOG_DIR/$name.log"
  if "$EASYCRYPT_BIN" compile -no-eco "$EASYCRYPT_DIR/$file" \
      -server "$SERVER_SOCKET" -max-provers "$MAX_PROVERS" \
      -I "$EXTRACT_DIR" -I "$SPEC_DIR" -I "$REFINEMENT_DIR" \
      -I "$SECURITY_DIR" \
      < /dev/null > "$log" 2>&1; then
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
  "$SPEC_DIR/KeygenSamplerCallersSpec.ec" \
  "$SPEC_DIR/KeygenUniformXofLeafSpec.ec" \
  "$SPEC_DIR/KeygenEtaSamplerSpec.ec" \
  "$SPEC_DIR/KeygenKeccak1600Spec.ec" \
  "$SPEC_DIR/KeygenShakeStreamSpec.ec" \
  "$SPEC_DIR/KeygenSeedXofSpec.ec" \
  "$REFINEMENT_DIR/TargetKeygenSamplerCallers.ec" \
  "$REFINEMENT_DIR/TargetKeygenUniformXofLeaf.ec" \
  "$REFINEMENT_DIR/TargetKeygenEtaSampler.ec" \
  "$REFINEMENT_DIR/TargetKeygenKeccak1600.ec" \
  "$REFINEMENT_DIR/TargetKeygenShakeStream.ec" \
  "$REFINEMENT_DIR/TargetKeygenSeedXof.ec" \
  > "$HOLE_LOG" || hole_status=$?
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
  "$SPEC_DIR/KeygenSamplerCallersSpec.ec" \
  "$SPEC_DIR/KeygenUniformXofLeafSpec.ec" \
  "$SPEC_DIR/KeygenEtaSamplerSpec.ec" \
  "$SPEC_DIR/KeygenKeccak1600Spec.ec" \
  "$SPEC_DIR/KeygenShakeStreamSpec.ec" \
  "$SPEC_DIR/KeygenSeedXofSpec.ec" \
  "$REFINEMENT_DIR/TargetKeygenSamplerCallers.ec" \
  "$REFINEMENT_DIR/TargetKeygenUniformXofLeaf.ec" \
  "$REFINEMENT_DIR/TargetKeygenEtaSampler.ec" \
  "$REFINEMENT_DIR/TargetKeygenKeccak1600.ec" \
  "$REFINEMENT_DIR/TargetKeygenShakeStream.ec" \
  "$REFINEMENT_DIR/TargetKeygenSeedXof.ec" \
  > "$AXIOM_LOG" || axiom_status=$?
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

printf 'Checked artifact SHA-256 values:\n' >> "$SUMMARY"
sha256sum \
  "$EXTRACT_DIR/KeygenSamplerCallersTarget.ec" \
  "$SPEC_DIR/KeygenSamplerCallersSpec.ec" \
  "$SPEC_DIR/KeygenUniformXofLeafSpec.ec" \
  "$SPEC_DIR/KeygenEtaSamplerSpec.ec" \
  "$SPEC_DIR/KeygenKeccak1600Spec.ec" \
  "$SPEC_DIR/KeygenShakeStreamSpec.ec" \
  "$SPEC_DIR/KeygenSeedXofSpec.ec" \
  "$REFINEMENT_DIR/TargetKeygenSamplerCallers.ec" \
  "$REFINEMENT_DIR/TargetKeygenUniformXofLeaf.ec" \
  "$REFINEMENT_DIR/TargetKeygenEtaSampler.ec" \
  "$REFINEMENT_DIR/TargetKeygenKeccak1600.ec" \
  "$REFINEMENT_DIR/TargetKeygenShakeStream.ec" \
  "$REFINEMENT_DIR/TargetKeygenSeedXof.ec" >> "$SUMMARY"

printf 'RESULT: PASS compiled=%s total=%s mode=-no-eco\n' \
  "$passed" "$total" | tee -a "$SUMMARY"
