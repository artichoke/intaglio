#!/usr/bin/env bash
#
# Prepare a fresh Codex app worktree for local development.
#
# Codex invokes this through .codex/environments/environment.toml when it creates
# a new worktree. Keep it idempotent: every command should be safe to run more
# than once in the same checkout.

set -Eeuo pipefail
IFS=$'\n\t'

RESET="" INFO="" WARN="" ERR=""
if [[ -t 1 && ${CI:-false} != "true" ]]; then
  INFO=$'\e[1;34m'
  WARN=$'\e[1;33m'
  ERR=$'\e[1;31m'
  RESET=$'\e[0m'
fi

log() { printf "%s[INFO ]%s %s\n" "$INFO" "$RESET" "$*"; }
warn() { printf "%s[WARN ]%s %s\n" "$WARN" "$RESET" "$*" >&2; }
error() { printf "%s[ERROR]%s %s\n" "$ERR" "$RESET" "$*" >&2; }

die() {
  error "$1"
  exit "${2:-70}"
}

need() {
  command -v "$1" > /dev/null 2>&1 || die "'$1' not found" 69
}

trap 'error "Failure on or near line $LINENO"; exit 70' ERR
trap 'log "completed in ${SECONDS}s"' EXIT

export PATH="/opt/homebrew/bin:/usr/local/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
export COREPACK_ENABLE_DOWNLOAD_PROMPT=0

cd_repo_root() {
  local repo_root

  need git
  repo_root=$(git rev-parse --show-toplevel 2> /dev/null || pwd)
  cd "$repo_root"
}

setup_git_base() {
  local -a args
  local head_sha upstream upstream_sha

  args=("$@")
  upstream=refs/remotes/origin/trunk

  log "fetching latest origin/trunk"
  git fetch --prune origin "+refs/heads/trunk:${upstream}"

  head_sha=$(git rev-parse --verify "HEAD^{commit}")
  upstream_sha=$(git rev-parse --verify "${upstream}^{commit}")

  if [[ $head_sha == "$upstream_sha" ]]; then
    log "worktree is based on origin/trunk at ${upstream_sha:0:12}"
    return
  fi

  if [[ -n $(git status --porcelain --untracked-files=normal) ]]; then
    die "worktree has local changes; refusing to update base to origin/trunk"
  fi

  if ! git merge-base --is-ancestor HEAD "$upstream"; then
    die "current HEAD is not an ancestor of origin/trunk; refusing to rewrite local commits"
  fi

  log "fast-forwarding worktree to origin/trunk at ${upstream_sha:0:12}"
  git merge --ff-only "$upstream"

  log "restarting setup script after refreshing worktree base"
  exec "$PWD/scripts/setup_codex_worktree.sh" "${args[@]}"
}

setup_mise() {
  need mise

  log "trusting mise.toml"
  mise trust --yes mise.toml

  log "checking mise-managed tools"
  if mise install --dry-run-code; then
    log "mise-managed tools are already installed"
  else
    case $? in
      1)
        log "installing missing mise-managed tools"
        mise install --yes
        ;;
      *)
        die "failed to check mise-managed tools"
        ;;
    esac
  fi

  eval "$(mise env -s bash)"
}

setup_rust() {
  need cargo

  log "fetching Rust dependencies"
  cargo fetch
}

setup_node() {
  if [[ ! -f package.json || ! -f pnpm-lock.yaml ]]; then
    warn "skipping pnpm install because package.json or pnpm-lock.yaml is missing"
    return
  fi

  need corepack

  log "installing Node dependencies"
  corepack enable
  pnpm install --frozen-lockfile
}

main() {
  cd_repo_root
  setup_git_base "$@"
  setup_mise
  setup_rust
  setup_node
}

main "$@"
