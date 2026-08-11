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
  OUTPUT_ROOT=$TOPDOWN_EXTRACT_DIR
else
  OUTPUT_ROOT=$(mktemp -d)
  cleanup_output=1
fi
OUTPUT_DIR="$OUTPUT_ROOT/hbz-codec"
mkdir -p "$OUTPUT_DIR"

cleanup() {
  if [ "$cleanup_output" -eq 1 ]; then
    rm -rf "$OUTPUT_ROOT"
  fi
}
trap cleanup EXIT HUP INT TERM

extract() {
  source=$1
  root=$2
  target=$3
  "$JASMIN2EC_BIN" --array-model=barray \
    --output-array="$OUTPUT_DIR" \
    -o "$OUTPUT_DIR/$target" \
    -f "$root" \
    "$source"
}

extract "$ROOT_DIR/haetae-ref-jasmin/jasmin/hpoly.jazz" \
  encode_hb_z1_prepare_jazz HbzPrepareTarget.ec
extract "$ROOT_DIR/haetae-ref-jasmin/jasmin/hpoly.jazz" \
  decode_hb_z1_apply_jazz HbzApplyTarget.ec
extract "$ROOT_DIR/haetae-ref-jasmin/jasmin/hpoly.jazz" \
  rans_encode_jazz RansEncodeTarget.ec
extract "$ROOT_DIR/haetae-ref-jasmin/jasmin/hpoly.jazz" \
  rans_decode_jazz RansDecodeTarget.ec
extract "$ROOT_DIR/haetae-ref-jasmin/jasmin/encoding.jazz" \
  encode_hb_z1_mode2_full_jazz HbzFullEncodeTarget.ec
extract "$ROOT_DIR/haetae-ref-jasmin/jasmin/encoding.jazz" \
  decode_hb_z1_mode2_full_jazz HbzFullDecodeTarget.ec

compile_target() {
  target=$1
  if [ -n "$SERVER_SOCKET" ]; then
    "$EASYCRYPT_BIN" compile -script -no-eco "$target" \
      -I "$OUTPUT_DIR" -server "$SERVER_SOCKET" -max-provers 1 \
      < /dev/null
  else
    "$EASYCRYPT_BIN" compile -script -no-eco "$target" \
      -I "$OUTPUT_DIR" < /dev/null
  fi
}

for target in \
  HbzPrepareTarget.ec \
  HbzApplyTarget.ec \
  RansEncodeTarget.ec \
  RansDecodeTarget.ec \
  HbzFullEncodeTarget.ec \
  HbzFullDecodeTarget.ec
do
  compile_target "$OUTPUT_DIR/$target"
done

printf 'PASS focused HBZ codec extraction dir=%s\n' "$OUTPUT_DIR"
