# Source this file from Bash after env/bootstrap.sh completes.
haetae_env_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export OPAMROOT="$haetae_env_dir/.opam-root"
eval "$(opam env --root="$OPAMROOT" --switch="$haetae_env_dir" --set-switch --shell=bash)"
export PATH="$haetae_env_dir/provers/bin:$haetae_env_dir/downloads/cvc5-Linux-x86_64-static/bin:$PATH"
export XDG_CONFIG_HOME="$haetae_env_dir/config"
unset haetae_env_dir
