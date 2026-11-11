#!/usr/bin/env bash
set -euo pipefail

if [ $# -eq 1 ]; then
    # only algo_mode
    ALGO_MODE="$1"
    BIN="./build/release/bin/haetae-${ALGO_MODE}-benchmark"

elif [ $# -eq 2 ]; then
    # avx_mode + algo_mode
    AVX_MODE="$1"
    ALGO_MODE="$2"
    BIN="./build/release-${AVX_MODE}/bin/haetae-${ALGO_MODE}-benchmark"

else
    echo "Usage:"
    echo "  $0 <algo_mode>"
    echo "  $0 <avx_mode> <algo_mode>"
    exit 1
fi

if [ ! -x "$BIN" ]; then
    echo "Error: benchmark binary not found: $BIN" >&2
    exit 1
fi

"$BIN" | awk '
/^crypto_sign_keypair:/   { section="keygen"; next }
/^crypto_sign_signature:/ { section="sign";   next }
/^crypto_sign_verify:/    { section="verify"; next }

/^median:/ {
    gsub(/[^0-9.]/, "", $2)
    med[section]=$2
    next
}

/^average:/ {
    gsub(/[^0-9.]/, "", $2)
    avg[section]=$2
    next
}

END {
    print med["keygen"]
    print avg["keygen"]
    print med["sign"]
    print avg["sign"]
    print med["verify"]
    print avg["verify"]
}
'
