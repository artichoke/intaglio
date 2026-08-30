#!/usr/bin/env bash
# Install an explicitly requested subset of the repository's locked mise tools.

set -Eeuo pipefail
IFS=$'\n\t'

main() {
  local -r mise=${MISE:?MISE is required}
  local -r requested_tools=${MISE_TOOLS:?MISE_TOOLS is required}
  local -r github_path=${GITHUB_PATH:?GITHUB_PATH is required}
  local bin_path enabled_tools repo_root tool
  local -a tools=()

  repo_root=$(git rev-parse --show-toplevel)
  readonly repo_root

  while IFS= read -r tool; do
    [[ -n $tool ]] || continue
    if [[ ! $tool =~ ^[a-zA-Z0-9][a-zA-Z0-9:._/-]*$ ]]; then
      echo "invalid mise tool name: $tool" >&2
      return 1
    fi

    "$mise" config get --file "$repo_root/mise.toml" "tools.$tool" > /dev/null
    tools+=("$tool")
  done <<< "$requested_tools"

  if [[ ${#tools[@]} -eq 0 ]]; then
    echo "mise-install requires at least one declared tool" >&2
    return 1
  fi

  enabled_tools=$(
    IFS=,
    echo "${tools[*]}"
  )
  readonly enabled_tools

  MISE_ENABLE_TOOLS=$enabled_tools MISE_NO_HOOKS=1 \
    "$mise" install --cd "$repo_root" --locked "${tools[@]}"
  while IFS= read -r bin_path; do
    printf '%s\n' "$bin_path" >> "$github_path"
  done < <(MISE_ENABLE_TOOLS=$enabled_tools \
    "$mise" bin-paths --cd "$repo_root" "${tools[@]}")
}

main "$@"
