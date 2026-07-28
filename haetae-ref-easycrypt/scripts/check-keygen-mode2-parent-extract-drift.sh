#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
SOURCE="$ROOT_DIR/haetae-ref-jasmin/jasmin/keypair.jazz"
OUT_DIR="$PROJECT_DIR/easycrypt/extract/keygen-mode2-parent"
FILE_MANIFEST="$PROJECT_DIR/manifests/keygen-mode2-parent-extract-files.txt"
PROCEDURE_MANIFEST="$PROJECT_DIR/manifests/keygen-mode2-parent-procedures.txt"
TMP_DIR=$(mktemp -d)

cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT HUP INT TERM

"$SCRIPT_DIR/check-sources.sh" >/dev/null

jasmin2ec --array-model=barray \
  --output-array="$TMP_DIR" \
  -o "$TMP_DIR/KeygenMode2ParentTarget.ec" \
  -f crypto_sign_keypair_internal_mode2_jazz \
  "$SOURCE"

find "$TMP_DIR" -maxdepth 1 -type f -name '*.ec' -exec basename {} \; \
  | LC_ALL=C sort > "$TMP_DIR/generated-files.txt"
diff -u "$FILE_MANIFEST" "$TMP_DIR/generated-files.txt"

find "$OUT_DIR" -maxdepth 1 -type f -name '*.ec' -exec basename {} \; \
  | LC_ALL=C sort > "$TMP_DIR/tracked-files.txt"
diff -u "$FILE_MANIFEST" "$TMP_DIR/tracked-files.txt"

sed -n 's/^[[:space:]]*proc \([^ (]*\).*/\1/p' \
  "$TMP_DIR/KeygenMode2ParentTarget.ec" > "$TMP_DIR/generated-procedures.txt"
diff -u "$PROCEDURE_MANIFEST" "$TMP_DIR/generated-procedures.txt"

while IFS= read -r file || [ -n "$file" ]; do
  diff -u "$OUT_DIR/$file" "$TMP_DIR/$file"
done < "$FILE_MANIFEST"

printf 'PASS: mode-2 key-generation parent extraction has zero regeneration drift (%s files, %s procedures)\n' \
  "$(wc -l < "$FILE_MANIFEST" | tr -d ' ')" \
  "$(wc -l < "$PROCEDURE_MANIFEST" | tr -d ' ')"
