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

SIGN_DIR="$OUTPUT_DIR/sign"
VERIFY_DIR="$OUTPUT_DIR/verify"
mkdir -p "$SIGN_DIR" "$VERIFY_DIR"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$SIGN_DIR" \
  -o "$SIGN_DIR/SignMuHashTarget.ec" \
  -f _sf_mu_rawpre \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/sign.jazz"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$VERIFY_DIR" \
  -o "$VERIFY_DIR/VerifyMuHashTarget.ec" \
  -f __verify_hash_mu \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/verification_transcript.jazz"

if [ -n "$SERVER_SOCKET" ]; then
  "$EASYCRYPT_BIN" compile -script -no-eco \
    "$SIGN_DIR/SignMuHashTarget.ec" -I "$SIGN_DIR" \
    -server "$SERVER_SOCKET" -max-provers 1 < /dev/null
  "$EASYCRYPT_BIN" compile -script -no-eco \
    "$VERIFY_DIR/VerifyMuHashTarget.ec" -I "$VERIFY_DIR" \
    -server "$SERVER_SOCKET" -max-provers 1 < /dev/null
else
  "$EASYCRYPT_BIN" compile -script -no-eco \
    "$SIGN_DIR/SignMuHashTarget.ec" -I "$SIGN_DIR" < /dev/null
  "$EASYCRYPT_BIN" compile -script -no-eco \
    "$VERIFY_DIR/VerifyMuHashTarget.ec" -I "$VERIFY_DIR" < /dev/null
fi

printf 'PASS focused mu-hash extraction sign=%s verify=%s\n' \
  "$SIGN_DIR" "$VERIFY_DIR"
