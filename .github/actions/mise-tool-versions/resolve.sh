#!/usr/bin/env bash
# Resolve exact mise.toml tool versions into trusted GitHub Action outputs.

set -Eeuo pipefail
IFS=$'\n\t'

emit_version() {
  local -r output_name=$1
  local -r tool_name=$2
  local -r config_path=$3
  local -r github_output=$4
  local -r mise=$5
  local version

  version=$("$mise" config get --file "$config_path" "tools.$tool_name")
  readonly version

  if [[ ! $version =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "mise tool $tool_name must be an exact release, got $version" >&2
    return 1
  fi

  printf '%s=%s\n' "$output_name" "$version" >> "$github_output"
}

main() {
  local -r mise=${MISE:?MISE is required}
  local -r github_output=${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}
  local config_path repo_root

  repo_root=$(git rev-parse --show-toplevel)
  readonly repo_root
  config_path="$repo_root/mise.toml"
  readonly config_path

  emit_version node node "$config_path" "$github_output" "$mise"
  emit_version zizmor aqua:zizmorcore/zizmor "$config_path" "$github_output" "$mise"
}

main "$@"
