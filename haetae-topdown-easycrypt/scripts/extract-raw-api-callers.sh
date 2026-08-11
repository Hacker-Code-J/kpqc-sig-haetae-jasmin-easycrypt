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

KEYGEN_DIR="$OUTPUT_DIR/keygen"
SIGN_DIR="$OUTPUT_DIR/sign"
VERIFY_DIR="$OUTPUT_DIR/verify"
mkdir -p "$KEYGEN_DIR" "$SIGN_DIR" "$VERIFY_DIR"

# Each root is an actual raw/internal ABI entry point. jasmin2ec includes the
# complete reachable closure, including the helper procedures listed in the
# focused-extraction manifest.
"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$KEYGEN_DIR" \
  -o "$KEYGEN_DIR/RawKeygenApiTarget.ec" \
  -f cryptolab_haetae_mode2_keypair_internal \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/keypair.jazz"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$SIGN_DIR" \
  -o "$SIGN_DIR/RawSignApiTarget.ec" \
  -f cryptolab_haetae_mode2_signature_internal \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/sign.jazz"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$VERIFY_DIR" \
  -o "$VERIFY_DIR/RawVerifyApiTarget.ec" \
  -f cryptolab_haetae_mode2_verify_internal \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/verify.jazz"

compile_target() {
  target=$1
  include_dir=$2
  if [ -n "$SERVER_SOCKET" ]; then
    "$EASYCRYPT_BIN" compile -script -no-eco "$target" -I "$include_dir" \
      -server "$SERVER_SOCKET" -max-provers 1 < /dev/null
  else
    "$EASYCRYPT_BIN" compile -script -no-eco "$target" -I "$include_dir" \
      < /dev/null
  fi
}

compile_target "$KEYGEN_DIR/RawKeygenApiTarget.ec" "$KEYGEN_DIR"
compile_target "$SIGN_DIR/RawSignApiTarget.ec" "$SIGN_DIR"
compile_target "$VERIFY_DIR/RawVerifyApiTarget.ec" "$VERIFY_DIR"

printf 'PASS raw ABI caller extraction keygen=%s sign=%s verify=%s\n' \
  "$KEYGEN_DIR" "$SIGN_DIR" "$VERIFY_DIR"
