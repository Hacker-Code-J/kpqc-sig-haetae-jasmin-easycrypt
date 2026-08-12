#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
JASMIN2EC_BIN=${JASMIN2EC:-jasmin2ec}
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
SERVER_SOCKET=${WHY3_SERVER_SOCKET:-}

cleanup_output=0
if [ -n "${TOPDOWN_EXTRACT_DIR:-}" ]; then
  OUTPUT_DIR=$TOPDOWN_EXTRACT_DIR
  mkdir -p "$OUTPUT_DIR"
else
  OUTPUT_DIR=$(mktemp -d)
  cleanup_output=1
fi

cleanup() {
  if [ "$cleanup_output" -eq 1 ]; then
    rm -rf "$OUTPUT_DIR"
  fi
}
trap cleanup EXIT HUP INT TERM

TARGET_DIR="$OUTPUT_DIR/sign-accepted-core"
TARGET="$TARGET_DIR/SignAcceptedCoreTarget.ec"
mkdir -p "$TARGET_DIR"

# These are the three actual mode-2 helpers composed by the authored harness.
# jasmin2ec includes their transitive callees but no sampler, packer, retry loop,
# or public API root.
"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$TARGET_DIR" \
  -o "$TARGET" \
  -f _sf_round_challenge_mode2 \
  -f _sf_z_check \
  -f _sf_hint_mode2 \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/sign.jazz"

if [ -n "$SERVER_SOCKET" ]; then
  "$EASYCRYPT_BIN" compile -script -no-eco "$TARGET" \
    -I "$TARGET_DIR" -server "$SERVER_SOCKET" -max-provers 1 \
    < /dev/null
else
  "$EASYCRYPT_BIN" compile -script -no-eco "$TARGET" \
    -I "$TARGET_DIR" < /dev/null
fi

printf 'PASS focused Sign accepted-core extraction target=%s\n' "$TARGET"
