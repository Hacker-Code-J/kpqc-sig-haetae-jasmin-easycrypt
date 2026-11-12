#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == --help ]]; then
  echo 'Usage: bash env/bootstrap.sh'
  echo 'Rebuilds the pinned Linux x86-64 toolchain under env/; JOBS defaults to 2.'
  echo 'Install system prerequisites from env/README.md first, then source env/activate.sh.'
  exit 0
fi
[[ $# == 0 ]] || { echo 'Usage: bash env/bootstrap.sh [--help]' >&2; exit 2; }
env_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
[[ "$(uname -s)/$(uname -m)" == Linux/x86_64 ]] || {
  echo 'Supported bootstrap platform: Linux x86-64' >&2; exit 2;
}
for command in opam git make cc c++ python3 wget unzip cvc4; do
  command -v "$command" >/dev/null || { echo "Missing prerequisite: $command (see env/README.md)" >&2; exit 2; }
done
# Z3 4.12.6 declares this system package on Debian-family hosts. Check before
# importing the much larger compiler switch so an unavailable package fails early.
haetae_os_family="$(python3 - <<'PY'
import platform
try:
    release = platform.freedesktop_os_release()
except (AttributeError, OSError):
    release = {}
print(release.get("ID", "") + " " + release.get("ID_LIKE", ""))
PY
)"
case " $haetae_os_family " in
  *" debian "*)
    haetae_distutils_status="$(dpkg-query -W -f='${db:Status-Status}' python3-distutils 2>/dev/null || true)"
    if [[ "$haetae_distutils_status" != installed ]]; then
      echo 'Missing python3-distutils, required by the Z3 4.12.6 opam package on Debian/Ubuntu.' >&2
      echo 'Use the documented Ubuntu 22.04 baseline and install python3-distutils before bootstrapping.' >&2
      exit 2
    fi
    ;;
esac
export OPAMROOT="$env_dir/.opam-root"
export XDG_CONFIG_HOME="$env_dir/config"
export OPAMJOBS="${JOBS:-2}"
mkdir -p "$env_dir/downloads" "$XDG_CONFIG_HOME"
if [[ ! -f "$OPAMROOT/config" ]]; then
  opam init --root="$OPAMROOT" --bare --no-setup --disable-sandboxing --yes
fi
opam switch import "$env_dir/opam-switch.export" --root="$OPAMROOT" --switch="$env_dir" --yes
# Alt-Ergo requires cmdliner < 2; the frozen compiler switch uses cmdliner 2.
if [[ ! -d "$env_dir/provers/_opam" ]]; then
  opam switch create "$env_dir/provers" --root="$OPAMROOT" --yes \
    --packages=ocaml-base-compiler.5.2.1,alt-ergo.2.6.0,z3.4.12.6
else
  opam install --root="$OPAMROOT" --switch="$env_dir/provers" --yes \
    ocaml-base-compiler.5.2.1 alt-ergo.2.6.0 z3.4.12.6
fi
mkdir -p "$env_dir/provers/bin"
ln -sfn ../_opam/bin/alt-ergo "$env_dir/provers/bin/alt-ergo"
ln -sfn ../_opam/bin/z3 "$env_dir/provers/bin/z3"
cvc5_archive="$env_dir/downloads/cvc5.zip"
if [[ ! -f "$cvc5_archive" ]]; then
  wget -O "$cvc5_archive" https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip
fi
printf '%s  %s\n' 6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56 "$cvc5_archive" | sha256sum --check
unzip -oq "$cvc5_archive" -d "$env_dir/downloads"
source "$env_dir/activate.sh"
easycrypt why3config
opam list --root="$OPAMROOT" --switch="$env_dir" --installed --columns=name,version > "$env_dir/installed-packages.txt"
bash "$env_dir/../scripts/check-environment.sh"
echo 'Environment ready. Run: source env/activate.sh'
