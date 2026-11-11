#!/bin/bash

set -e

# Compares KATs produced by pre-built binaries in BIN_DIR against ../kat.
# For a from-source build + all optimized variants, use ../kat.sh (the CI entry
# point): `../kat.sh check`.

BIN_DIR=${1:-./build/release/bin}
REF_DIR=../kat

declare -a MODES=("mode2" "mode3" "mode5")

fail=0

echo "==== KAT TEST START ===="

for mode in "${MODES[@]}"; do
    echo "[*] Running haetae-${mode}-kat..."
    ${BIN_DIR}/haetae-${mode}-kat

    GEN_FILE=PQCsignKAT_haetae_${mode}.rsp
    REF_FILE=${REF_DIR}/PQCsignKAT_haetae_${mode}.rsp

    echo "[*] Comparing ${mode}..."

    if diff -ru "$GEN_FILE" "$REF_FILE" > /dev/null; then
        echo "[PASS] ${mode}"
    else
        echo "[FAIL] ${mode}"
        diff -ru "$GEN_FILE" "$REF_FILE" || true
        fail=1
    fi

    rm "$GEN_FILE" PQCsignKAT_haetae_${mode}.req

    echo ""
done

echo "==== KAT TEST END ===="

exit $fail
