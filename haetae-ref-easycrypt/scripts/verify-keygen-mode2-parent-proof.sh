#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
EASYCRYPT_DIR="$PROJECT_DIR/easycrypt"
PARENT_EXTRACT_DIR="$EASYCRYPT_DIR/extract/keygen-mode2-parent"
CALLER_EXTRACT_DIR="$EASYCRYPT_DIR/extract/keygen-sampler-callers"
SPEC_DIR="$EASYCRYPT_DIR/spec"
REFINEMENT_DIR="$EASYCRYPT_DIR/refinement"
SECURITY_DIR="$PROJECT_DIR/../haetae-security/provable-security/easycrypt"
FILE_MANIFEST="$PROJECT_DIR/manifests/keygen-mode2-parent-proof-files.txt"
SHARED_MANIFEST="$PROJECT_DIR/manifests/keygen-mode2-parent-shared-theories.txt"
LOG_DIR="$PROJECT_DIR/logs/keygen-mode2-parent-proof"
SUMMARY="$PROJECT_DIR/logs/keygen-mode2-parent-proof-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
WHY3_BIN=${WHY3:-why3}
WHY3SERVER_BIN=${WHY3SERVER:-"$($WHY3_BIN --print-libdir)/why3server"}
MAX_PROVERS=${EC_MAX_PROVERS:-1}

mkdir -p "$LOG_DIR"

LOCK_DIR="$LOG_DIR/.verify.lock"
if ! mkdir "$LOCK_DIR" 2>/dev/null; then
  printf 'FAIL another mode-2 parent proof verification is active lock=%s\n' \
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

PARENT_DRIFT_LOG="$LOG_DIR/parent-extraction-drift.log"
if "$SCRIPT_DIR/check-keygen-mode2-parent-extract-drift.sh" \
    > "$PARENT_DRIFT_LOG" 2>&1; then
  :
else
  status=$?
  printf 'FAIL parent extraction drift check exit=%s log=%s\n' \
    "$status" "$PARENT_DRIFT_LOG"
  tail -n 80 "$PARENT_DRIFT_LOG"
  exit "$status"
fi

CALLER_DRIFT_LOG="$LOG_DIR/caller-extraction-drift.log"
if "$SCRIPT_DIR/check-keygen-sampler-callers-extract-drift.sh" \
    > "$CALLER_DRIFT_LOG" 2>&1; then
  :
else
  status=$?
  printf 'FAIL caller extraction drift check exit=%s log=%s\n' \
    "$status" "$CALLER_DRIFT_LOG"
  tail -n 80 "$CALLER_DRIFT_LOG"
  exit "$status"
fi

SHARED_LOG="$LOG_DIR/shared-theory-identity.log"
: > "$SHARED_LOG"
find "$PARENT_EXTRACT_DIR" -maxdepth 1 -type f -name '*.ec' \
  -exec basename {} \; | LC_ALL=C sort > "$SERVER_DIR/parent-theories.txt"
find "$CALLER_EXTRACT_DIR" -maxdepth 1 -type f -name '*.ec' \
  -exec basename {} \; | LC_ALL=C sort > "$SERVER_DIR/caller-theories.txt"
comm -12 "$SERVER_DIR/parent-theories.txt" "$SERVER_DIR/caller-theories.txt" \
  > "$SERVER_DIR/shared-theories.txt"
if ! diff -u "$SHARED_MANIFEST" "$SERVER_DIR/shared-theories.txt" \
    >> "$SHARED_LOG"; then
  printf 'FAIL shared generated theory inventory drift log=%s\n' "$SHARED_LOG"
  cat "$SHARED_LOG"
  exit 1
fi
shared_count=0
while IFS= read -r file || [ -n "$file" ]; do
  if [ ! -f "$PARENT_EXTRACT_DIR/$file" ] ||
      [ ! -f "$CALLER_EXTRACT_DIR/$file" ]; then
    printf 'missing shared theory: %s\n' "$file" >> "$SHARED_LOG"
    printf 'FAIL shared generated theory inventory log=%s\n' "$SHARED_LOG"
    cat "$SHARED_LOG"
    exit 1
  fi
  if diff -u "$CALLER_EXTRACT_DIR/$file" "$PARENT_EXTRACT_DIR/$file" \
      >> "$SHARED_LOG"; then
    shared_count=$((shared_count + 1))
  else
    printf 'FAIL shared generated theory differs: %s log=%s\n' \
      "$file" "$SHARED_LOG"
    tail -n 80 "$SHARED_LOG"
    exit 1
  fi
done < "$SHARED_MANIFEST"
printf 'PASS byte-identical shared generated theories (%s files)\n' \
  "$shared_count" >> "$SHARED_LOG"

{
  printf 'HAETAE mode-2 key-generation parent sampler-prefix proof verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Command: ./scripts/verify-keygen-mode2-parent-proof.sh\n'
  printf 'Actual parent target: easycrypt/extract/keygen-mode2-parent/KeygenMode2ParentTarget.ec\n'
  printf 'Bridge target: easycrypt/extract/keygen-sampler-callers/KeygenSamplerCallersTarget.ec\n'
  printf 'Authored parent specification: easycrypt/spec/KeygenMode2ParentSpec.ec\n'
  printf 'Authored parent refinements: easycrypt/refinement/TargetKeygenMode2Parent.ec; easycrypt/refinement/TargetKeygenMode2ParentComposition.ec\n'
  printf 'Proof manifest: manifests/keygen-mode2-parent-proof-files.txt\n'
  printf 'Shared-theory manifest: manifests/keygen-mode2-parent-shared-theories.txt\n'
  printf 'Source manifest: manifests/sources.sha256\n'
  printf 'Toolchain: manifests/toolchain.md\n\n'
  printf 'PASS canonical source hash check (%s pinned inputs)\n' "$source_count"
  cat "$PARENT_DRIFT_LOG"
  cat "$CALLER_DRIFT_LOG"
  cat "$SHARED_LOG"
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
      -I "$PARENT_EXTRACT_DIR" -I "$CALLER_EXTRACT_DIR" \
      -I "$SPEC_DIR" -I "$REFINEMENT_DIR" -I "$SECURITY_DIR" \
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
  "$SPEC_DIR/KeygenMode2ParentSpec.ec" \
  "$REFINEMENT_DIR/TargetKeygenSamplerCallers.ec" \
  "$REFINEMENT_DIR/TargetKeygenUniformXofLeaf.ec" \
  "$REFINEMENT_DIR/TargetKeygenEtaSampler.ec" \
  "$REFINEMENT_DIR/TargetKeygenKeccak1600.ec" \
  "$REFINEMENT_DIR/TargetKeygenShakeStream.ec" \
  "$REFINEMENT_DIR/TargetKeygenSeedXof.ec" \
  "$REFINEMENT_DIR/TargetKeygenMode2Parent.ec" \
  "$REFINEMENT_DIR/TargetKeygenMode2ParentComposition.ec" \
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
  "$SPEC_DIR/KeygenMode2ParentSpec.ec" \
  "$REFINEMENT_DIR/TargetKeygenSamplerCallers.ec" \
  "$REFINEMENT_DIR/TargetKeygenUniformXofLeaf.ec" \
  "$REFINEMENT_DIR/TargetKeygenEtaSampler.ec" \
  "$REFINEMENT_DIR/TargetKeygenKeccak1600.ec" \
  "$REFINEMENT_DIR/TargetKeygenShakeStream.ec" \
  "$REFINEMENT_DIR/TargetKeygenSeedXof.ec" \
  "$REFINEMENT_DIR/TargetKeygenMode2Parent.ec" \
  "$REFINEMENT_DIR/TargetKeygenMode2ParentComposition.ec" \
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
while IFS= read -r file || [ -n "$file" ]; do
  sha256sum "$EASYCRYPT_DIR/$file" >> "$SUMMARY"
done < "$FILE_MANIFEST"

printf 'RESULT: PASS compiled=%s total=%s mode=-no-eco\n' \
  "$passed" "$total" | tee -a "$SUMMARY"
