#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_dir"

server_args=()
if [[ -n "${WHY3_SERVER_SOCKET:-}" ]]; then
  [[ -S "$WHY3_SERVER_SOCKET" ]] || {
    echo "Missing Why3 server socket: $WHY3_SERVER_SOCKET" >&2
    exit 2
  }
  server_args=(-server "$WHY3_SERVER_SOCKET")
fi

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 TARGET.ec [EASYCRYPT_OPTIONS...]" >&2
  exit 2
fi
source_path=$1
shift
source_dir="$(cd -- "$(dirname -- "$source_path")" && pwd)"
source_basename="$(basename -- "$source_path")"

# EasyCrypt can return success at EOF with a proof still open.  A following
# checked declaration forces it to reject pending proofs and clone obligations.
# Keep the basename so the temporary main theory has the original namespace.
verify_temp_dir="$(mktemp -d "${TMPDIR:-/tmp}/haetae120-ec-eof.XXXXXXXX")"
trap 'rm -rf -- "$verify_temp_dir"' EXIT
verify_source_copy="$verify_temp_dir/$source_basename"
cp -- "$source_path" "$verify_source_copy"
cat >> "$verify_source_copy" <<'EOF'

lemma __haetae120_verification_eof_complete : true.
proof. trivial. qed.
EOF

"${EASYCRYPT:-easycrypt}" compile -no-eco -pragmas Proofs:check \
  -timeout "${EC_TIMEOUT:-10}" -max-provers "${EC_MAX_PROVERS:-1}" \
  "${server_args[@]}" \
  -I "$source_dir" \
  -I generated/sampler -I generated/ntt -I generated/api \
  -I theories -I theories/ntt -I proofs "$verify_source_copy" "$@"
