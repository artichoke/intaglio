#!/usr/bin/env bash
# Install a pinned mise archive after SHA-256 verification.

set -Eeuo pipefail
IFS=$'\n\t'

SETUP_MISE_SCRATCH=
SETUP_MISE_ARCHIVE=

cleanup() {
  if [[ -n $SETUP_MISE_ARCHIVE ]]; then
    rm -f -- "$SETUP_MISE_ARCHIVE"
  fi
  if [[ -n $SETUP_MISE_SCRATCH ]]; then
    rmdir -- "$SETUP_MISE_SCRATCH"
  fi
}

platform_and_checksum() {
  local -r runner_os=$1
  local -r runner_arch=$2

  case "$runner_os/$runner_arch" in
    Linux/X64)
      printf '%s\t%s\n' linux-x64 \
        "${MISE_SHA256_LINUX_X64:?MISE_SHA256_LINUX_X64 is required}"
      ;;
    macOS/ARM64)
      printf '%s\t%s\n' macos-arm64 \
        "${MISE_SHA256_MACOS_ARM64:?MISE_SHA256_MACOS_ARM64 is required}"
      ;;
    macOS/X64)
      printf '%s\t%s\n' macos-x64 \
        "${MISE_SHA256_MACOS_X64:?MISE_SHA256_MACOS_X64 is required}"
      ;;
    *)
      echo "setup-mise does not support $runner_os $runner_arch" >&2
      return 1
      ;;
  esac
}

verify_checksum() {
  local -r runner_os=$1
  local -r checksum=$2
  local -r archive=$3

  if [[ $runner_os == macOS ]]; then
    printf '%s  %s\n' "$checksum" "$archive" | shasum -a 256 --check
  else
    printf '%s  %s\n' "$checksum" "$archive" | sha256sum --check
  fi
}

main() {
  local -r version=${MISE_VERSION:?MISE_VERSION is required}
  local -r runner_os=${RUNNER_OS:?RUNNER_OS is required}
  local -r runner_arch=${RUNNER_ARCH:?RUNNER_ARCH is required}
  local -r runner_temp=${RUNNER_TEMP:?RUNNER_TEMP is required}
  local -r github_output=${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}
  local archive checksum install_root platform scratch
  local -a curl_args=(--fail --location --silent --show-error)

  if [[ -n ${GITHUB_TOKEN:-} ]]; then
    curl_args+=(--header "Authorization: Bearer $GITHUB_TOKEN")
  fi

  IFS=$'\t' read -r platform checksum < <(
    platform_and_checksum "$runner_os" "$runner_arch"
  )
  readonly platform checksum
  archive="mise-v${version}-${platform}.tar.xz"
  readonly archive
  install_root="$runner_temp/mise-$version"
  readonly install_root
  scratch=$(mktemp -d "$runner_temp/setup-mise.XXXXXX")
  readonly scratch
  SETUP_MISE_SCRATCH=$scratch
  readonly SETUP_MISE_SCRATCH
  SETUP_MISE_ARCHIVE="$scratch/$archive"
  readonly SETUP_MISE_ARCHIVE
  trap cleanup EXIT

  curl "${curl_args[@]}" \
    --output "$SETUP_MISE_ARCHIVE" \
    "https://github.com/jdx/mise/releases/download/v${version}/${archive}"
  verify_checksum "$runner_os" "$checksum" "$SETUP_MISE_ARCHIVE"

  mkdir -p "$install_root"
  tar --extract --xz --file "$SETUP_MISE_ARCHIVE" \
    --directory "$install_root" --strip-components=1

  "$install_root/bin/mise" --version
  printf 'executable=%s\n' "$install_root/bin/mise" >> "$github_output"
}

main "$@"
