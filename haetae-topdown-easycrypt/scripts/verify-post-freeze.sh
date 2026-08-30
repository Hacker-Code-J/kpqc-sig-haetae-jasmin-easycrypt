#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)

EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
WHY3_BIN=${WHY3:-why3}
WHY3SERVER_BIN=${WHY3SERVER:-"$($WHY3_BIN --print-libdir)/why3server"}
PYTHON_BIN=${PYTHON:-python3}
TIMEOUT=${POST_FREEZE_EASYCRYPT_TIMEOUT:-5}

PROOF_MANIFEST="$PROJECT_DIR/manifests/post-freeze-proof-targets.txt"
ARTIFACT_MANIFEST="$PROJECT_DIR/manifests/post-freeze-executable-artifacts.txt"
CLAIM_MAP="$PROJECT_DIR/manifests/post-freeze-claim-map.tsv"
FROZEN_EXTRACTION_HASHES="$PROJECT_DIR/manifests/generated-extractions.sha256"
POST_FREEZE_EXTRACTION_HASHES="$PROJECT_DIR/manifests/post-freeze-generated-extractions.sha256"
LOG_DIR="$PROJECT_DIR/logs/post-freeze"
SUMMARY="$PROJECT_DIR/logs/verify-post-freeze-summary.txt"

mkdir -p "$LOG_DIR"
: > "$SUMMARY"

WORK_DIR=$(mktemp -d /tmp/haetae-post-freeze-verify.XXXXXX)
SERVER_SOCKET=${WHY3_SERVER_SOCKET:-"$WORK_DIR/why3server.socket"}
SERVER_PID=

cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  case "$WORK_DIR" in
    /tmp/haetae-post-freeze-verify.*)
      rm -rf -- "$WORK_DIR"
      ;;
  esac
}
trap cleanup EXIT HUP INT TERM

pass() {
  printf 'PASS %s\n' "$1" | tee -a "$SUMMARY"
}

fail() {
  printf 'FAIL %s\n' "$1" | tee -a "$SUMMARY" >&2
  exit 1
}

command -v "$EASYCRYPT_BIN" > /dev/null 2>&1 || fail "EasyCrypt unavailable: $EASYCRYPT_BIN"
command -v "$WHY3_BIN" > /dev/null 2>&1 || fail "Why3 unavailable: $WHY3_BIN"
command -v "$PYTHON_BIN" > /dev/null 2>&1 || fail "Python unavailable: $PYTHON_BIN"
command -v jasmin2ec > /dev/null 2>&1 || fail "jasmin2ec unavailable"
command -v rg > /dev/null 2>&1 || fail "rg unavailable"

if [ -n "${WHY3_SERVER_SOCKET:-}" ]; then
  [ -S "$SERVER_SOCKET" ] || fail "supplied Why3 server socket unavailable: $SERVER_SOCKET"
  pass "supplied Why3 server socket"
else
  "$WHY3SERVER_BIN" --socket "$SERVER_SOCKET" -j 1 \
    > "$LOG_DIR/why3server.log" 2>&1 &
  SERVER_PID=$!
  server_wait=0
  while [ ! -S "$SERVER_SOCKET" ] && [ "$server_wait" -lt 100 ]; do
    sleep 0.1
    server_wait=$((server_wait + 1))
  done
  [ -S "$SERVER_SOCKET" ] || fail "Why3 server startup"
  pass "Why3 server startup"
fi

[ -f "$PROOF_MANIFEST" ] || fail "missing proof manifest"
[ -f "$ARTIFACT_MANIFEST" ] || fail "missing executable-artifact manifest"
[ -f "$CLAIM_MAP" ] || fail "missing claim map"

DISCOVERED_PROOFS="$WORK_DIR/discovered-proofs.txt"
SORTED_PROOFS="$WORK_DIR/manifest-proofs.txt"
find "$PROJECT_DIR/post-freeze" -maxdepth 1 -type f -name '*.ec' \
  | sed "s#^$ROOT_DIR/##" > "$DISCOVERED_PROOFS"
for target in \
  haetae-ntt-verify/easycrypt/NTTFullSpectralAction.ec \
  haetae-ntt-verify/easycrypt/NTTMode2RowSpecializations.ec \
  haetae-ntt-verify/easycrypt/NTTRowProductSpec.ec \
  haetae-ntt-verify/easycrypt/RqHAETAEBridge.ec
do
  [ -f "$ROOT_DIR/$target" ] || fail "missing shared NTT target: $target"
  printf '%s\n' "$target" >> "$DISCOVERED_PROOFS"
done
LC_ALL=C sort -o "$DISCOVERED_PROOFS" "$DISCOVERED_PROOFS"
LC_ALL=C sort "$PROOF_MANIFEST" > "$SORTED_PROOFS"
if ! diff -u "$SORTED_PROOFS" "$DISCOVERED_PROOFS" \
    > "$LOG_DIR/proof-manifest-drift.log"; then
  tail -n 80 "$LOG_DIR/proof-manifest-drift.log" >&2
  fail "post-freeze proof manifest drift"
fi
proof_count=$(awk 'NF && $1 !~ /^#/ { count++ } END { print count + 0 }' "$PROOF_MANIFEST")
[ "$proof_count" -eq 164 ] || fail "expected 164 proof targets, found $proof_count"
pass "post-freeze proof manifest targets=164"

DISCOVERED_ARTIFACTS="$WORK_DIR/discovered-artifacts.txt"
SORTED_ARTIFACTS="$WORK_DIR/manifest-artifacts.txt"
find "$PROJECT_DIR/post-freeze" -maxdepth 1 -type f \
  \( -name 'check-*.py' -o -name '*.json' \
     -o -name 'extract-mode2-accepted-class-trace.c' \) \
  | sed "s#^$ROOT_DIR/##" | LC_ALL=C sort > "$DISCOVERED_ARTIFACTS"
LC_ALL=C sort "$ARTIFACT_MANIFEST" > "$SORTED_ARTIFACTS"
if ! diff -u "$SORTED_ARTIFACTS" "$DISCOVERED_ARTIFACTS" \
    > "$LOG_DIR/executable-artifact-manifest-drift.log"; then
  tail -n 80 "$LOG_DIR/executable-artifact-manifest-drift.log" >&2
  fail "post-freeze executable-artifact manifest drift"
fi
artifact_count=$(awk 'NF && $1 !~ /^#/ { count++ } END { print count + 0 }' "$ARTIFACT_MANIFEST")
[ "$artifact_count" -eq 15 ] || fail "expected 15 executable artifacts, found $artifact_count"
pass "post-freeze executable-artifact manifest entries=15"

EXPECTED_CLAIM_ARTIFACTS="$WORK_DIR/expected-claim-artifacts.txt"
MAPPED_CLAIM_ARTIFACTS="$WORK_DIR/mapped-claim-artifacts.txt"
{
  cat "$PROOF_MANIFEST"
  cat "$ARTIFACT_MANIFEST"
} | LC_ALL=C sort > "$EXPECTED_CLAIM_ARTIFACTS"
awk -F '\t' 'NR > 1 { print $1 }' "$CLAIM_MAP" \
  | LC_ALL=C sort > "$MAPPED_CLAIM_ARTIFACTS"
if ! diff -u "$EXPECTED_CLAIM_ARTIFACTS" "$MAPPED_CLAIM_ARTIFACTS" \
    > "$LOG_DIR/claim-map-coverage.log"; then
  tail -n 80 "$LOG_DIR/claim-map-coverage.log" >&2
  fail "post-freeze claim-map coverage"
fi
if ! awk -F '\t' '
  NR == 1 {
    if ($0 != "artifact\tclaim_id\trole\tevidence_status\tpaper_use") exit 1
    next
  }
  NF != 5 { exit 1 }
  $2 !~ /^(C1-FAITHFUL-REFINEMENT|C2-CHALLENGE-MODEL|C3-QUANTITATIVE-KEYGEN|S2-SIGN-ROM|S3-PUBLIC-KEY-NMA)$/ { exit 1 }
  seen[$1]++ > 0 { exit 1 }
  { count++ }
  END { if (count != 179) exit 1 }
' "$CLAIM_MAP" > "$LOG_DIR/claim-map-schema.log" 2>&1; then
  fail "post-freeze claim-map schema"
fi
pass "post-freeze claim map entries=179"

if rg -ni '^[[:space:]]*axiom[[:space:]]|(^|[^[:alnum:]_])(admit|admitted|abort|sorry)([^[:alnum:]_]|$)' \
    "$PROJECT_DIR/post-freeze" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/NTTFullSpectralAction.ec" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/NTTMode2RowSpecializations.ec" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/NTTRowProductSpec.ec" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/RqHAETAEBridge.ec" \
    --glob '*.ec' > "$LOG_DIR/proof-escape-scan.log"; then
  cat "$LOG_DIR/proof-escape-scan.log" >&2
  fail "proof escape found"
fi
pass "post-freeze proof-escape scan"

if rg -n '^[[:space:]]*(print[[:space:]]+(goal|all)|lemma[[:space:]]+(debug|tmp|temporary)([^[:alnum:]_]|$)|op[[:space:]]+(debug|tmp|temporary)([^[:alnum:]_]|$))' \
    "$PROJECT_DIR/post-freeze" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/NTTFullSpectralAction.ec" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/NTTMode2RowSpecializations.ec" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/NTTRowProductSpec.ec" \
    "$ROOT_DIR/haetae-ntt-verify/easycrypt/RqHAETAEBridge.ec" \
    --glob '*.ec' > "$LOG_DIR/debug-temporary-scan.log"; then
  cat "$LOG_DIR/debug-temporary-scan.log" >&2
  fail "debug or temporary declaration found"
fi
pass "post-freeze debug/temporary declaration scan"

"$SCRIPT_DIR/check-source-drift.sh" > "$LOG_DIR/source-drift-before.log" 2>&1 \
  || fail "source drift before verification"
pass "source drift before verification"

PAPER_FREEZE_SCOPE_ONLY=1 "$SCRIPT_DIR/check-paper-freeze.sh" \
  > "$LOG_DIR/paper-freeze-scope-audit.log" 2>&1 \
  || fail "frozen 82-target scope audit"
pass "frozen 82-target scope preserved"

run_extraction() {
  label=$1
  output_dir=$2
  script=$3
  log="$LOG_DIR/extract-$label.log"
  if ! TOPDOWN_EXTRACT_DIR="$output_dir" \
       WHY3_SERVER_SOCKET="$SERVER_SOCKET" \
       "$script" > "$log" 2>&1; then
    tail -n 60 "$log" >&2
    fail "focused extraction $label"
  fi
  pass "focused extraction $label"
}

run_extraction transcripts "$WORK_DIR/extract" \
  "$SCRIPT_DIR/extract-transcripts.sh"
run_extraction mu-hash "$WORK_DIR/mu-hash-extract" \
  "$SCRIPT_DIR/extract-mu-hash.sh"
run_extraction packers "$WORK_DIR/packer-extract" \
  "$SCRIPT_DIR/extract-packers.sh"
run_extraction signature-codec "$WORK_DIR" \
  "$SCRIPT_DIR/extract-signature-codec.sh"
run_extraction hbz-codec "$WORK_DIR" \
  "$SCRIPT_DIR/extract-hbz-codec.sh"
run_extraction api-key-memory "$WORK_DIR/api-key-extract" \
  "$SCRIPT_DIR/extract-api-key-memory.sh"
run_extraction raw-api-callers "$WORK_DIR/raw-api-extract" \
  "$SCRIPT_DIR/extract-raw-api-callers.sh"
run_extraction sign-accepted-core "$WORK_DIR" \
  "$SCRIPT_DIR/extract-sign-accepted-core.sh"
run_extraction verify-core "$WORK_DIR" \
  "$SCRIPT_DIR/extract-verify-core.sh"
run_extraction verify-unpack-v3 "$WORK_DIR" \
  "$SCRIPT_DIR/extract-verify-unpack-v3.sh"

if ! (cd "$WORK_DIR" && sha256sum -c "$FROZEN_EXTRACTION_HASHES") \
    > "$LOG_DIR/frozen-generated-extraction-hashes.log" 2>&1; then
  tail -n 80 "$LOG_DIR/frozen-generated-extraction-hashes.log" >&2
  fail "frozen generated extraction hashes"
fi
pass "frozen generated extraction hashes"

if ! (cd "$WORK_DIR" && sha256sum -c "$POST_FREEZE_EXTRACTION_HASHES") \
    > "$LOG_DIR/post-freeze-generated-extraction-hashes.log" 2>&1; then
  tail -n 80 "$LOG_DIR/post-freeze-generated-extraction-hashes.log" >&2
  fail "post-freeze generated extraction hashes"
fi
pass "post-freeze generated extraction hashes"

checker_count=0
certificate_count=0
c_source_count=0
while IFS= read -r artifact || [ -n "$artifact" ]; do
  [ -n "$artifact" ] || continue
  case "$artifact" in
    \#*) continue ;;
    *.py)
      checker_count=$((checker_count + 1))
      name=$(basename "$artifact" .py)
      log="$LOG_DIR/checker-$name.log"
      if ! (cd "$ROOT_DIR" && PYTHONDONTWRITEBYTECODE=1 \
            "$PYTHON_BIN" "$artifact") > "$log" 2>&1; then
        tail -n 80 "$log" >&2
        fail "executable checker $artifact"
      fi
      pass "executable checker $artifact"
      ;;
    *.json)
      certificate_count=$((certificate_count + 1))
      name=$(basename "$artifact" .json)
      log="$LOG_DIR/json-$name.log"
      if ! "$PYTHON_BIN" -m json.tool "$ROOT_DIR/$artifact" \
          > "$log" 2>&1; then
        tail -n 40 "$log" >&2
        fail "JSON certificate $artifact"
      fi
      pass "JSON certificate $artifact"
      ;;
    *.c)
      c_source_count=$((c_source_count + 1))
      class_trace_checker="$PROJECT_DIR/post-freeze/check-mode2-accepted-class-trace.py"
      class_trace_log="$LOG_DIR/checker-check-mode2-accepted-class-trace.log"
      if ! rg -F 'extract-mode2-accepted-class-trace.c' \
          "$class_trace_checker" > /dev/null \
        || ! rg -F 'build_harness(binary)' "$class_trace_checker" > /dev/null \
        || ! rg -F 'run_harness(binary)' "$class_trace_checker" > /dev/null \
        || ! rg -F 'PASS deterministic mode2 accepted class trace' \
          "$class_trace_log" > /dev/null; then
        fail "C trace extractor is not compiled and replayed by its checker"
      fi
      ;;
    *)
      fail "unknown executable artifact type: $artifact"
      ;;
  esac
done < "$ARTIFACT_MANIFEST"
[ "$checker_count" -eq 8 ] || fail "expected 8 checkers, ran $checker_count"
[ "$certificate_count" -eq 6 ] || fail "expected 6 certificates, parsed $certificate_count"
[ "$c_source_count" -eq 1 ] || fail "expected 1 C trace source, found $c_source_count"
pass "executable certificate totals checkers=8 certificates=6 c-sources=1"

TOPDOWN_SPECS="$PROJECT_DIR/easycrypt/specs"
TOPDOWN_SECURITY="$PROJECT_DIR/easycrypt/security"
TOPDOWN_SUPPORT="$PROJECT_DIR/easycrypt/support"
TOPDOWN_COMPOSITION="$PROJECT_DIR/easycrypt/refinement/composition"
TOPDOWN_KEYGEN="$PROJECT_DIR/easycrypt/refinement/keygen"
TOPDOWN_SIGN="$PROJECT_DIR/easycrypt/refinement/sign"
TOPDOWN_VERIFY="$PROJECT_DIR/easycrypt/refinement/verify"
POST_FREEZE="$PROJECT_DIR/post-freeze"

OLD_SPEC="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/spec"
OLD_REFINEMENT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/refinement"
OLD_SUPPORT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/support"
PARENT_EXTRACT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/extract/keygen-mode2-parent"
CALLER_EXTRACT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/extract/keygen-sampler-callers"
NTT_EXTRACT="$ROOT_DIR/haetae-ref-easycrypt/easycrypt/extract/ntt"
NTT_FOUNDATION="$ROOT_DIR/haetae-ntt-verify/easycrypt"
NTT_SUPPORT="$ROOT_DIR/haetae-ntt-verify/easycrypt-ct"
SECURITY="$ROOT_DIR/haetae-security/provable-security/easycrypt"
ROOT_SECURITY="$ROOT_DIR/haetae-security"

SIGN_EXTRACT="$WORK_DIR/extract/sign"
VERIFY_EXTRACT="$WORK_DIR/extract/verify"
MU_SIGN_EXTRACT="$WORK_DIR/mu-hash-extract/sign"
MU_VERIFY_EXTRACT="$WORK_DIR/mu-hash-extract/verify"
PACKER_EXTRACT="$WORK_DIR/packer-extract/packers"
SIG_PACK_EXTRACT="$WORK_DIR/pack"
SIG_UNPACK_EXTRACT="$WORK_DIR/unpack"
HBZ_EXTRACT="$WORK_DIR/hbz-codec"
API_KEYGEN_EXTRACT="$WORK_DIR/api-key-extract/keygen"
API_SIGN_EXTRACT="$WORK_DIR/api-key-extract/sign"
API_VERIFY_EXTRACT="$WORK_DIR/api-key-extract/verify"
RAW_KEYGEN_EXTRACT="$WORK_DIR/raw-api-extract/keygen"
RAW_SIGN_EXTRACT="$WORK_DIR/raw-api-extract/sign"
RAW_VERIFY_EXTRACT="$WORK_DIR/raw-api-extract/verify"
SIGN_CORE_EXTRACT="$WORK_DIR/sign-accepted-core"
VERIFY_CORE_EXTRACT="$WORK_DIR/verify-core"
VERIFY_UNPACK_EXTRACT="$WORK_DIR/verify-unpack-v3"

compile_target() {
  target=$1
  file="$ROOT_DIR/$target"
  name=$(basename "$target" .ec)
  log="$LOG_DIR/compile-$name.log"
  if ! "$EASYCRYPT_BIN" compile -script -no-eco \
      -timeout "$TIMEOUT" -max-provers 1 -server "$SERVER_SOCKET" \
      -I "$POST_FREEZE" \
      -I "$TOPDOWN_SPECS" -I "$TOPDOWN_SECURITY" -I "$TOPDOWN_SUPPORT" \
      -I "$TOPDOWN_COMPOSITION" -I "$TOPDOWN_KEYGEN" \
      -I "$TOPDOWN_SIGN" -I "$TOPDOWN_VERIFY" \
      -I "$OLD_SPEC" -I "$OLD_REFINEMENT" -I "$OLD_SUPPORT" \
      -I "$PARENT_EXTRACT" -I "$CALLER_EXTRACT" -I "$NTT_EXTRACT" \
      -I "$SECURITY" -I "$ROOT_SECURITY" \
      -I "$NTT_FOUNDATION" -I "$NTT_SUPPORT" \
      -I "$SIGN_EXTRACT" -I "$VERIFY_EXTRACT" \
      -I "$MU_SIGN_EXTRACT" -I "$MU_VERIFY_EXTRACT" \
      -I "$PACKER_EXTRACT" -I "$SIG_PACK_EXTRACT" \
      -I "$SIG_UNPACK_EXTRACT" -I "$HBZ_EXTRACT" \
      -I "$API_KEYGEN_EXTRACT" -I "$API_SIGN_EXTRACT" \
      -I "$API_VERIFY_EXTRACT" \
      -I "$RAW_KEYGEN_EXTRACT" -I "$RAW_SIGN_EXTRACT" \
      -I "$RAW_VERIFY_EXTRACT" \
      -I "$SIGN_CORE_EXTRACT" -I "$VERIFY_CORE_EXTRACT" \
      -I "$VERIFY_UNPACK_EXTRACT" \
      "$file" < /dev/null > "$log" 2>&1; then
    tail -n 80 "$log" >&2
    fail "fresh compile $target"
  fi
  pass "fresh compile $target"
}

compiled=0
while IFS= read -r target || [ -n "$target" ]; do
  [ -n "$target" ] || continue
  case "$target" in
    \#*) continue ;;
  esac
  compile_target "$target"
  compiled=$((compiled + 1))
done < "$PROOF_MANIFEST"
[ "$compiled" -eq 164 ] || fail "expected 164 compiled targets, got $compiled"

"$SCRIPT_DIR/check-source-drift.sh" > "$LOG_DIR/source-drift-after.log" 2>&1 \
  || fail "source drift after verification"
pass "source drift after verification"

printf 'RESULT PASS post-freeze-theories=%s checkers=%s certificates=%s cache=-no-eco\n' \
  "$compiled" "$checker_count" "$certificate_count" | tee -a "$SUMMARY"
